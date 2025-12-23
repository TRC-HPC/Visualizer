#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Topology Visualizer (segment time, plots toggle, color on left, groups, node/chunk filters)
Top toolbar: View | Plots | Color | Filters | Save/Load | Logs
"""

# =============================================================================
# Reviewer Notes
# =============================================================================
# This file contains a monolithic Dash application used to visualize a network/topology
# alongside time-segmented simulation logs. The code is organized roughly as:
#   1) Data/model helpers (JSON parsing, log indexing, graph helpers)
#   2) UI constants and layout construction (Dash components)
#   3) Server endpoints for save/load (Flask routes)
#   4) Dash callbacks (interactive behavior; the bulk of the code)
#
# Primary state is held in dcc.Store components (e.g., loaded topology, parsed log data,
# selected segment/time window, and user-defined filters). Most callbacks read from these
# stores and update the Cytoscape graph + Plotly figures accordingly.
#
# =============================================================================


from dash import Dash, html, dcc, Output, Input, State, no_update, ALL, MATCH, ctx
import dash_cytoscape as cyto
import plotly.graph_objects as go
import networkx as nx
import visdcc
from flask import request, jsonify
from dash.exceptions import PreventUpdate
import dash
import json, os, base64, math
from string import Template
import numpy as np
import pandas as pd
import os
from bisect import bisect_right


# ----- Custom X/Y metric catalog -----
# "series" = function of time → returns (t, values) arrays
# "event"  = per-send points → used for scatter clouds
XY_OPTIONS = [
    {"label": "Time (series)", "value": "time"},
    {"label": "In-flight sends (WIP) (series)", "value": "wip"},
    {"label": "Cumulative finished chunks (series)", "value": "cum_finished"},
    {"label": "Average send duration (series)", "value": "avg_send_duration"},
    {"label": "Post-conditions Left (avg over visible hosts) (series)", "value": "postleft_avg"},

    {"label": "Send start time (points)", "value": "send_start_time"},
    {"label": "Send end time (points)", "value": "send_end_time"},
    {"label": "Send duration (points)", "value": "send_duration"},
]


# Your simulation helper
import interactiveinfo
# === JSON LOG ADAPTER ===
class _LinkInfoShim:
    def __init__(self, rank_count:int):
        # Init.
        self.rankCount = int(rank_count)


class DataVar:
    """
    One data/node variable (chunks + sends) parsed from a Varname block.
    This encapsulates what JsonVisualizer.__init__ used to do for a single data var.
    """
    def __init__(self, name: str, block: dict):
        # Init.
        self.name = name
        self.block = block
        self.vartype = (block.get("Vartype") or "").lower()

        values = list(block.get("Values") or [])
        varcount = block.get("Varcount")
        try:
            varcount = int(varcount) if varcount is not None else None
        except Exception:
            # Recover from a failure case and return a safe default.
            varcount = None

        starting_pos = block.get("Starting position") or {}
        starting_chunks = block.get("Starting chunks") or {}

        # ---- starting map: node -> list_of_chunks ----
        start_map = {}
        # Variant B: explicit chunks list
        if isinstance(starting_chunks, dict) and starting_chunks:
            # Branch based on the current state / selection.
            for k, v in starting_chunks.items():
                # Iterate over the relevant items and accumulate results.
                try:
                    node = int(k)
                except Exception:
                    # Recover from a failure case and return a safe default.
                    continue
                if isinstance(v, list):
                    # Branch based on the current state / selection.
                    start_map[node] = [int(x) for x in v]
        # Variant A: flags per node (0/1), seed *all* chunks when value==1
        if isinstance(starting_pos, dict) and starting_pos:
            # fallback varcount from data_id maxima if not present
            if varcount is None:
                # Validate inputs / state before continuing.
                max_chunk = -1
                for ev in values:
                    # Iterate over the relevant items and accumulate results.
                    try:
                        max_chunk = max(max_chunk, int(ev.get("data_id")))
                    except Exception:
                        # Recover from a failure case and return a safe default.
                        pass
                varcount = (max_chunk + 1) if max_chunk >= 0 else 0
            full = list(range(int(varcount or 0)))
            for k, v in starting_pos.items():
                # Iterate over the relevant items and accumulate results.
                try:
                    node = int(k)
                except Exception:
                    # Recover from a failure case and return a safe default.
                    continue
                flag = int(v) if v is not None else 0
                if flag == 1:
                    # Branch based on the current state / selection.
                    start_map[node] = list(full)

                # ---- derive rank_count and chunkCount for THIS data_var ----
        node_ids = set()
        for ev in values:
            # Iterate over the relevant items and accumulate results.
            eid = ev.get("entity_id")
            try:
                # NEW: handle link entity_id = [src, dst]
                if isinstance(eid, (list, tuple)):
                    # Branch based on the current state / selection.
                    if len(eid) == 2:
                        # Branch based on the current state / selection.
                        node_ids.add(int(eid[0]))
                        node_ids.add(int(eid[1]))
                elif eid is not None:
                    # Alternative branch for a different condition.
                    node_ids.add(int(eid))
                s = ev.get("src")
                if s is not None:
                    # Validate inputs / state before continuing.
                    node_ids.add(int(s))
            except Exception:
                # ignore broken entries
                pass

        node_ids.update(start_map.keys())
        rank_count = (max(node_ids) + 1) if node_ids else 0

        if varcount is None:
            # Validate inputs / state before continuing.
            max_chunk = -1
            for ev in values:
                # Iterate over the relevant items and accumulate results.
                try:
                    max_chunk = max(max_chunk, int(ev.get("data_id")))
                except Exception:
                    # Recover from a failure case and return a safe default.
                    pass
            varcount = (max_chunk + 1) if max_chunk >= 0 else 0

        self.rankCount = int(rank_count)
        self.chunkCount = int(varcount or 0)

        N = self.rankCount
        C = self.chunkCount

        # per-node lifecycle and per-chunk lifecycle (unchanged)
        self.nodeLifeCycle = [dict() for _ in range(N)]
        self.chunkLifeCycle = [dict() for _ in range(C)]

        # NEW: per-chunk/per-link intervals for link-based data_vars
        # chunkLinkIntervals[c][(src, dst)] = [(t_start, t_end), ...]
        self.chunkLinkIntervals = [dict() for _ in range(C)]
        # linkChunkIntervals[(src, dst)] = [(t_start, t_end, chunk), ...]
        self.linkChunkIntervals = {}

        # Seed presence at t=0 as "seed"
        for r, chunks in start_map.items():
            # Iterate over the relevant items and accumulate results.
            for c in chunks:
                # Iterate over the relevant items and accumulate results.
                if 0 <= r < N and 0 <= c < C:
                    # Branch based on the current state / selection.
                    self.nodeLifeCycle[r].setdefault(c, []).append((0.0, "seed"))
                    self.chunkLifeCycle[c].setdefault(r, []).append((0.0, "seed"))

        # ---- build send intervals (node-based) + link intervals (NEW) ----
        self.rankSendsByTime = {}
        self.sends = []
        last_start = {}        # for node sends
        link_last_start = {}   # for link intervals
        tmax = 0.0

        values_sorted = sorted(values, key=lambda ev: float(ev.get("time", 0)))
        for ev in values_sorted:
            # Iterate over the relevant items and accumulate results.
            try:
                enum = (ev.get("enum") or "").lower()
                t = float(ev.get("time", 0))
                eid = ev.get("entity_id")
                src_field = ev.get("src")
                chunk = int(ev.get("data_id"))
            except Exception:
                # Recover from a failure case and return a safe default.
                continue

            if t > tmax:
                # Branch based on the current state / selection.
                tmax = t

            # ---------- LINK-LEVEL EVENTS (entity_id is [src, dst]) ----------
            if isinstance(eid, (list, tuple)):
                # Branch based on the current state / selection.
                if len(eid) != 2:
                    # Branch based on the current state / selection.
                    continue
                try:
                    link_src = int(eid[0])
                    link_dst = int(eid[1])
                except Exception:
                    # Recover from a failure case and return a safe default.
                    continue

                key = (link_src, link_dst, chunk)
                if enum == "start":
                    # chunk enters link
                    link_last_start[key] = t
                elif enum in ("leave", "arrive"):
                    # chunk leaves link; close interval
                    t0 = link_last_start.get(key, t)

                    if 0 <= chunk < C:
                        # Branch based on the current state / selection.
                        per_chunk = self.chunkLinkIntervals[chunk].setdefault((link_src, link_dst), [])
                        per_chunk.append((t0, t))

                    Lkey = (link_src, link_dst)
                    self.linkChunkIntervals.setdefault(Lkey, []).append((t0, t, chunk))

                    link_last_start.pop(key, None)

                # IMPORTANT: do NOT feed link events into node send logic
                continue

            # ---------- NODE-LEVEL EVENTS (entity_id is a node id) ----------
            try:
                dst = int(eid)
            except Exception:
                # Recover from a failure case and return a safe default.
                continue

            src = None
            if src_field is not None:
                # Validate inputs / state before continuing.
                try:
                    src = int(src_field)
                except Exception:
                    # Recover from a failure case and return a safe default.
                    src = None

            if enum == "start":
                # send from src → dst
                if src is None:
                    # Validate inputs / state before continuing.
                    continue
                last_start[(dst, src, chunk)] = t

            elif enum == "arrive":
                # lifecycle arrivals
                if 0 <= dst < N and 0 <= chunk < C:
                    # Branch based on the current state / selection.
                    self.nodeLifeCycle[dst].setdefault(chunk, []).append((t, "arrive"))
                    self.chunkLifeCycle[chunk].setdefault(dst, []).append((t, "arrive"))

                # send interval
                t0 = last_start.get((dst, src, chunk), t)
                item = {
                    "t_start": t0,
                    "t_end": t,
                    "chunk": chunk,
                    "src": (src if src is not None else -1),
                    "dst": dst,
                }
                self.sends.append(item)
                self.rankSendsByTime.setdefault((t0, t), []).append(item)

            else:
                # ignore bare "leave" at node level
                pass

        self.time = float(tmax)

    def chunks_on_link_in_segment(self, src, dst, t0, t1):
        """
        Return sorted list of chunk IDs that were on link (src, dst)
        at any time overlapping [t0, t1].
        """
        # Chunks on link in segment.
        try:
            src = int(src)
            dst = int(dst)
        except Exception:
            # Recover from a failure case and return a safe default.
            return []

        try:
            t0 = float(t0)
            t1 = float(t1)
        except Exception:
            # Recover from a failure case and return a safe default.
            return []

        if t1 < t0:
            # Branch based on the current state / selection.
            t0, t1 = t1, t0

        seen = set()
        intervals = []
        intervals.extend(self.linkChunkIntervals.get((src, dst), []) or [])
        if (dst, src) != (src, dst):
            intervals.extend(self.linkChunkIntervals.get((dst, src), []) or [])
        for start, end, chunk in intervals:
            # Iterate over the relevant items and accumulate results.
            if end >= t0 and start <= t1:   # overlap with segment
                try:
                    seen.add(int(chunk))
                except Exception:
                    # Recover from a failure case and return a safe default.
                    pass

        return sorted(seen)

    def link_chunks_detailed_in_segment(self, src, dst, t0, t1):
        """
        For a given link (src, dst), return a list of intervals for chunks
        that were on this link overlapping [t0, t1].

        Each element: {"chunk", "t_start", "t_end"}, sorted by t_end (leave time).
        """
        # Link chunks detailed in segment.
        try:
            src = int(src)
            dst = int(dst)
        except Exception:
            # Recover from a failure case and return a safe default.
            return []

        try:
            t0 = float(t0)
            t1 = float(t1)
        except Exception:
            # Recover from a failure case and return a safe default.
            return []

        if t1 < t0:
            # Branch based on the current state / selection.
            t0, t1 = t1, t0

        res = []
        intervals = []
        intervals.extend(self.linkChunkIntervals.get((src, dst), []) or [])
        if (dst, src) != (src, dst):
            intervals.extend(self.linkChunkIntervals.get((dst, src), []) or [])
        seen_trip = set()
        for start, end, chunk in intervals:
            # Overlap with [t0, t1]?
            if end >= t0 and start <= t1:
                # Branch based on the current state / selection.
                try:
                    c = int(chunk)
                except Exception:
                    # Recover from a failure case and return a safe default.
                    continue
                try:
                    st = float(start); en = float(end)
                except Exception:
                    continue
                trip = (c, st, en)
                if trip in seen_trip:
                    continue
                seen_trip.add(trip)
                res.append(
                    {
                        "chunk": c,
                        "t_start": float(start),
                        "t_end": float(end),
                    }
                )

        # Sort by leave time (earlier leaves first)
        res.sort(key=lambda it: it["t_end"])
        return res

    def links_for_chunk_in_segment(self, chunk, t0, t1):
        """
        For a given chunk, return a list of link intervals it traversed
        overlapping [t0, t1], sorted by finish time.

        Each element: {"src", "dst", "t_start", "t_end", "chunk"}
        """
        # Links for chunk in segment.
        try:
            chunk = int(chunk)
        except Exception:
            # Recover from a failure case and return a safe default.
            return []

        if not (0 <= chunk < self.chunkCount):
            # Validate inputs / state before continuing.
            return []

        try:
            t0 = float(t0)
            t1 = float(t1)
        except Exception:
            # Recover from a failure case and return a safe default.
            return []

        if t1 < t0:
            # Branch based on the current state / selection.
            t0, t1 = t1, t0

        res = []
        link_map = self.chunkLinkIntervals[chunk]
        for (src, dst), intervals in link_map.items():
            # Iterate over the relevant items and accumulate results.
            for start, end in intervals:
                # Iterate over the relevant items and accumulate results.
                if end >= t0 and start <= t1:
                    # Branch based on the current state / selection.
                    res.append(
                        {
                            "src": int(src),
                            "dst": int(dst),
                            "t_start": float(start),
                            "t_end": float(end),
                            "chunk": chunk,
                        }
                    )

        res.sort(key=lambda it: it["t_end"])
        return res



class LinkVar:
    """
    One link_var (Vartype='link'): generic numeric value on links vs time.
    We keep per-link step-series so we can color edges later.
    """
    def __init__(self, name: str, block: dict):
        # Init.
        self.name = name
        self.block = block
        self.vartype = (block.get("Vartype") or "").lower()

        raw_values = list(block.get("Values") or [])
        events = []
        per_link = {}
        tmax = 0.0

        raw_values_sorted = sorted(raw_values, key=lambda ev: float(ev.get("time", 0)))
        for ev in raw_values_sorted:
            # Iterate over the relevant items and accumulate results.
            try:
                t = float(ev.get("time", 0))
                link = ev.get("link") or ev.get("edge")
                if not isinstance(link, (list, tuple)) or len(link) != 2:
                    # Validate inputs / state before continuing.
                    continue
                src = int(link[0])
                dst = int(link[1])

                # generic numeric value: prefer "value", then "flow", then "val"
                value = ev.get("value")
                if value is None:
                    # Validate inputs / state before continuing.
                    value = ev.get("flow")
                if value is None:
                    # Validate inputs / state before continuing.
                    value = ev.get("val")
                value = float(value if value is not None else 0.0)
            except Exception:
                # Recover from a failure case and return a safe default.
                continue

            if t > tmax:
                # Branch based on the current state / selection.
                tmax = t

            events.append({"time": t, "src": src, "dst": dst, "value": value})
            per_link.setdefault((src, dst), []).append((t, value))

        for key, lst in per_link.items():
            # Iterate over the relevant items and accumulate results.
            lst.sort(key=lambda x: x[0])

        self.events = events
        self.per_link = per_link
        self.time = float(tmax)


class JsonVisualizer:
    """
    Adapter exposing the subset of interactiveinfo.Visualizer used by the app.
    JSON schema (flexible, supports variants seen so far):
    Varname{
      Vartype: (node|link|data)
      Varcount: <int>                 # data only: number of chunks
      Starting position: { node: 0/1, ... }   # data only, variant A (flag per node)
      Starting chunks: { node: [chunk_id, ...], ... }  # data only, variant B (explicit list)
      Values: [
        { time: <float>, entity_id: <int>, data_id: <int>, enum: "start"|"arrive"|"leave", src: <int> }
      ]
    }
    Semantics:
      - A send starts at enum="start" and ends at enum="arrive".
      - Events are emitted on the *destination* node (entity_id = dst) with src=sender.
      - Seeds from Starting position/Starting chunks appear in presence but are ignored for post-left.
    """
    def __init__(self, json_path: str, topo_path: str = None):
        # Init.
        with open(json_path, "r") as f:
            # Open the file and ensure it is closed correctly.
            root = json.load(f)

        # -------- 1) Scan for all Varname blocks --------
        data_blocks = []   # list[(name, dict)] for Vartype in {data,node}
        link_blocks = []   # list[(name, dict)] for Vartype == link

        if isinstance(root, dict):
            # Case A: whole file is a single Varname
            if "Vartype" in root:
                # Branch based on the current state / selection.
                vt = (root.get("Vartype") or "").lower()
                if vt in ("data", "node"):
                    # Branch based on the current state / selection.
                    data_blocks.append(("", root))
                elif vt == "link":
                    # Alternative branch for a different condition.
                    link_blocks.append(("", root))

            # Case B: top-level keys hold Varname blocks (Dvars, link_var1, link_var2, ...)
            for name, block in root.items():
                # Iterate over the relevant items and accumulate results.
                if not isinstance(block, dict) or "Vartype" not in block:
                    # Validate inputs / state before continuing.
                    continue
                vt = (block.get("Vartype") or "").lower()
                if vt in ("data", "node"):
                    # Branch based on the current state / selection.
                    data_blocks.append((str(name), block))
                elif vt == "link":
                    # Alternative branch for a different condition.
                    link_blocks.append((str(name), block))

        if not data_blocks:
            # Validate inputs / state before continuing.
            raise ValueError("JSON does not contain any data/node variable (Vartype='data'|'node').")

        # -------- 2) Create DataVar and LinkVar instances --------
        self.data_vars = [
            DataVar(name or f"data_var_{i}", block)
            for i, (name, block) in enumerate(data_blocks)
        ]
        self.link_vars = [
            LinkVar(name or f"link_var_{i}", block)
            for i, (name, block) in enumerate(link_blocks)
        ]

        # -------- 3) Choose a primary data_var for backwards compatibility --------
        # Prefer the one literally named "Dvars" if present; otherwise just take the first.
        primary = self.data_vars[0]
        for dv in self.data_vars:
            # Iterate over the relevant items and accumulate results.
            if dv.name == "Dvars":
                # Branch based on the current state / selection.
                primary = dv
                break

        self.primary_data = primary

        # Copy the fields the rest of the app expects directly on VIZ
        self.chunkCount = primary.chunkCount
        self.nodeLifeCycle = primary.nodeLifeCycle
        self.chunkLifeCycle = primary.chunkLifeCycle
        self.rankSendsByTime = primary.rankSendsByTime
        self.sends = primary.sends

        # rankCount for linkInfo shim
        self.rankCount = primary.rankCount

        # Global time = max(data_var time, all link_var times)
        tmax = primary.time
        for lv in self.link_vars:
            # Iterate over the relevant items and accumulate results.
            if lv.time > tmax:
                # Branch based on the current state / selection.
                tmax = lv.time

        self.time = float(tmax)
        self.linkInfo = _LinkInfoShim(rank_count=self.rankCount)

# === END JSON LOG ADAPTER ===

# Small helper for JS templates (avoids f-string brace issues)
def _js(template: str, **kwargs) -> str:
    """Return a JavaScript string from a Template with $PLACEHOLDERs."""
    # Js.
    return Template(template).substitute(**kwargs)

# =========================
# Paths & App
# =========================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
UPLOAD_DIR = os.path.join(BASE_DIR, "uploads")
os.makedirs(UPLOAD_DIR, exist_ok=True)

TOPO_FILE = ""
LOG_FILE = os.path.join(BASE_DIR, "visYarin.json")
PRESET_FILE = os.path.join(BASE_DIR, "saved_layout.json")  # positions-only
SESSION_FILE = os.path.join(BASE_DIR, "saved_session.json")  # full session
DEFAULTS_FILE = os.path.join(BASE_DIR, "view_defaults.json") # named position presets
GROUPS_FILE = os.path.join(BASE_DIR, "node_groups.json")     # user-defined node groups
os.makedirs(os.path.dirname(PRESET_FILE), exist_ok=True)

def _ensure_file(path, empty_obj):
    # Ensure file.
    if not os.path.exists(path):
        # Validate inputs / state before continuing.
        with open(path, "w") as f:
            # Open the file and ensure it is closed correctly.
            json.dump(empty_obj, f)

def _ensure_defaults_file():
    # Ensure defaults file.
    _ensure_file(DEFAULTS_FILE, {"defaults": {}})

def _ensure_groups_file():
    # Ensure groups file.
    _ensure_file(GROUPS_FILE, {"groups": {}})

_ensure_defaults_file()
_ensure_groups_file()

# IMPORTANT: components appear only after you click a toolbar button
app = Dash(__name__, suppress_callback_exceptions=True)
server = app.server

# =========================
# Styles
# =========================
BASE_STYLESHEET = [
    {"selector": "node", "style": {
        "content": "data(label)",
        "font-size": 11,
        "text-valign": "center",
        "text-halign": "center",
    }},
    {"selector": ".switch", "style": {
        "shape": "round-rectangle",
        "background-color": "#ffd166",
        "border-width": 2, "border-color": "#b78600",
        "width": 46, "height": 30
    }},
    {"selector": ".host", "style": {
        "shape": "ellipse",
        "background-color": "#7aa6ff",
        "border-width": 1, "border-color": "#4d71b3",
        "width": 26, "height": 26
    }},
    {"selector": "edge", "style": {
        "curve-style": "bezier", "width": 2, "line-color": "#b5b5b5",
    }},
    {"selector": "edge.peer", "style": {"curve-style": "bezier", "width": 2, "line-color": "#b5b5b5"}},
    {"selector": "edge.uplink", "style": {"curve-style": "bezier", "width": 2, "line-color": "#b5b5b5"}},
    {"selector": "edge:selected", "style": {
        "label": "data(label)", "font-size": 8, "text-rotation": "autorotate",
        "text-margin-y": -6, "z-index": 9999, "width": 4
    }},
    {"selector": ".has-chunk", "style": {"border-width": 5, "border-color": "#2a9d8f", "z-index": 10000}},
]
TOPBAR_STYLE = {
    "background": "#ffffff", "border": "1px solid #e1e7ef", "borderRadius": "12px",
    "padding": "12px 16px", "display": "grid", "gridTemplateColumns": "1fr auto",
    "alignItems": "center", "gap": "12px", "boxShadow": "0 1px 0 rgba(12, 18, 28, 0.03)"
}
TOPBAR_BTNS_STYLE = {"display": "flex", "gap": "12px", "flexWrap": "wrap"}
BTN = {
    "border": "1px solid #e1e7ef", "background": "#f5f7fa",
    "borderRadius": "10px", "padding": "8px 14px",
    "fontWeight": 600, "cursor": "pointer"
}
LAYOUT_STYLE = {
    "width": "100%", "minHeight": "100vh", "padding": "16px",
    "boxSizing": "border-box", "overflowX": "hidden", "background": "#f8fafd",
}
MAIN_GRID = {
    "display": "grid",
    "gridTemplateColumns": "300px 1fr 300px",  # LEFT | CENTER | RIGHT
    "gap": "16px",
    "height": "calc(100vh - 120px)",
}
CARD = {
    "background": "#fff",
    "border": "1px solid #e1e7ef",
    "borderRadius": "12px",
    "height": "100%",
}
LEFT_CARD = {**CARD, "padding": "16px", "overflow": "auto"}
RIGHT_CARD = {**CARD, "padding": "16px", "overflow": "auto"}   # ← new
CENTER_CARD = {**CARD, "display": "grid", "gridTemplateRows": "1fr auto"}  # graph + time segment controls

LABEL_MUTED = {"color": "#5b6470", "fontSize": "12px"}


def parse_topology(filename):
    # Load and parse log data, then update the derived metrics used by plots and filters.
    with open(filename, "r") as f:
        # Open the file and ensure it is closed correctly.
        raw_lines = [ln.rstrip("\n") for ln in f]

    lines = [ln.strip() for ln in raw_lines if ln.strip() and not ln.lstrip().startswith("#")]
    if len(lines) < 2:
        # Branch based on the current state / selection.
        raise ValueError("Topology file too short.")

    # Find header
    header_idx = None
    header_ints = None
    for i, line in enumerate(lines):
        # Iterate over the relevant items and accumulate results.
        parts = line.split()
        ints = []
        for tok in parts:
            # Iterate over the relevant items and accumulate results.
            try: ints.append(int(tok))
            except ValueError: continue
        if len(ints) >= 2:
            # Branch based on the current state / selection.
            header_idx = i; header_ints = ints; break

    if header_idx is None:
        # Validate inputs / state before continuing.
        raise ValueError("No header line found.")

    num_nodes, num_switches = header_ints[0], header_ints[1]
    switch_ids = set(range(num_nodes - num_switches, num_nodes))

    # Initialize the graph structure representing the topology.
    G = nx.Graph()
    edges = []
    
    # Track min/max for every parameter we find
    param_ranges = {} 

    for n in range(num_nodes):
        # Iterate over the relevant items and accumulate results.
        G.add_node(n)

    # Helper to clean numbers with units (e.g. "10000.0Gbps" -> 10000.0)
    def clean_val(val):
        # Clean val.
        s = str(val).lower()
        for unit in ["gbps", "mbps", "kbps", "bps", "us", "ms", "s"]:
            # Iterate over the relevant items and accumulate results.
            s = s.replace(unit, "")
        try:
            return float(s)
        except ValueError:
            # Recover from a failure case and return a safe default.
            return val # Return original if not a number

    for line in lines[header_idx + 1 :]:
        # Iterate over the relevant items and accumulate results.
        if not line or line.startswith("#"): continue
        parts = line.split()
        if len(parts) < 2: continue

        # Skip obvious non-link lines (like the switch ID list if it appears)
        # The switch list usually has many integers and no units/decimals.
        if len(parts) > 6 and "Gbps" not in line and "PDR" not in line:
            # Quick heuristic check: if it's just a long list of ints, skip it
            try: 
                if all(x.isdigit() for x in parts): continue
            except: pass

        # Parse row params
        row_params = {}
        
        # --- NEW: Check for PDR format explicitly ---
        # Format: "src dst bw lat PDR val"
        if len(parts) >= 5 and "PDR" in parts:
             # Branch based on the current state / selection.
             src, dst = parts[0], parts[1]
             row_params["capacity"] = clean_val(parts[2])
             row_params["latency"] = clean_val(parts[3])
        
        # --- Existing Heuristics (modified to use clean_val) ---
        # Heuristic for standard 4-column "src dst cap lat"
        elif len(parts) == 4:
            # Alternative branch for a different condition.
            src, dst = parts[0], parts[1]
            row_params["capacity"] = clean_val(parts[2])
            row_params["latency"] = clean_val(parts[3])

        # Heuristic for 6-column "src ? dst ? cap lat"
        elif len(parts) >= 6:
            # Alternative branch for a different condition.
            src, dst = parts[0], parts[2]
            row_params["capacity"] = clean_val(parts[4])
            row_params["latency"] = clean_val(parts[5])
            for k, val in enumerate(parts[6:], start=6):
                # Iterate over the relevant items and accumulate results.
                row_params[f"param_{k}"] = clean_val(val)
        
        # Generic catch-all
        else:
            src, dst = parts[0], parts[1]
            for k, val in enumerate(parts[2:], start=2):
                # Iterate over the relevant items and accumulate results.
                key = "capacity" if k==2 else "latency" if k==3 else f"param_{k}"
                row_params[key] = clean_val(val)

        # Default fills
        if "capacity" not in row_params: row_params["capacity"] = 1.0
        if "latency" not in row_params: row_params["latency"] = 0.0

        try:
            src_i, dst_i = int(src), int(dst)
        except ValueError: continue

        # Update ranges
        for k, v in row_params.items():
            # Iterate over the relevant items and accumulate results.
            if isinstance(v, (int, float)):
                # Branch based on the current state / selection.
                if k not in param_ranges: param_ranges[k] = [v, v]
                else:
                    param_ranges[k][0] = min(param_ranges[k][0], v)
                    param_ranges[k][1] = max(param_ranges[k][1], v)

        G.add_node(src_i); G.add_node(dst_i)
        G.add_edge(src_i, dst_i, **row_params)
        
        edges.append((src_i, dst_i, row_params))

    return G, num_nodes, switch_ids, edges, param_ranges
    


def generate_preset_layout(G, switch_ids):
    """
    Level-based layout with circular placement for intra-level connected components ("clique groups").

    Fix for large gaps on the first layer:
    - We compress the *desired* X-centers of groups on level 1 before packing them left-to-right.
      This reduces excessive whitespace between groups without allowing overlap.
    - We also tighten level 0 so level 1 isn't anchored to an overly wide host row.
    """
    import networkx as nx
    import math
    import statistics
    from collections import deque

    # -------------------------
    # 1) Pick BFS roots ("hosts")
    # -------------------------
    # Prefer non-switch nodes as the bottom layer; fallback to leaf nodes; fallback to any node.
    hosts = [n for n in G.nodes() if n not in switch_ids]
    if not hosts and G.nodes():
        degrees = dict(G.degree())
        hosts = [n for n, d in degrees.items() if d == 1]
    if not hosts and G.nodes():
        hosts = [min(G.nodes())]

    # -------------------------
    # 2) Compute BFS levels from hosts
    # -------------------------
    levels = {n: -1 for n in G.nodes()}
    q = deque()

    for h in hosts:
        levels[h] = 0
        q.append(h)

    visited = set(hosts)
    max_level = 0

    while q:
        u = q.popleft()
        lu = levels[u]
        max_level = max(max_level, lu)

        for v in G.neighbors(u):
            if v not in visited:
                visited.add(v)
                levels[v] = lu + 1
                q.append(v)

    # Any disconnected leftovers get treated as level 0 so everything is placed.
    level_nodes = {}
    for n, l in levels.items():
        if l == -1:
            l = 0
            levels[n] = 0
        level_nodes.setdefault(l, []).append(n)

    # -------------------------
    # Layout knobs (tune here)
    # -------------------------
    LEVEL_HEIGHT = 225

    NODE_ARC = 45          # Controls clique circle radius: larger -> bigger circles
    MIN_GROUP_RADIUS = 5

    # Tighten host row so the first switch layer doesn't spread out too much.
    L0_NODE_SPACING = 100
    GROUP_PADDING_L0 = 30

    # First layer (level 1):
    GROUP_PADDING_L1 = 100
    TARGET_COMPRESS_L1 = 0.8  # <1 compresses spread; smaller => tighter groups

    # Higher layers: mild compression to avoid.
    GROUP_PADDING_OTHER = 100
    TARGET_COMPRESS_OTHER = 0.8

    def _radius(cnt: int) -> float:
        """Convert group size into a circle radius."""
        if cnt <= 1:
            return 0.0
        circumference = cnt * NODE_ARC
        return max(MIN_GROUP_RADIUS, circumference / (2.0 * math.pi))

    def _compress_targets(xs, factor: float):
        """
        Shrink horizontal spread around the mean, preserving order.
        This reduces large gaps caused by widely spaced anchors (e.g., children far apart).
        """
        if not xs:
            return xs
        mu = statistics.mean(xs)
        return [mu + factor * (x - mu) for x in xs]

    def _pack_groups(groups, padding: float):
        """
        Place groups left-to-right, enforcing non-overlap:
            center[i] >= center[i-1] + r[i-1] + r[i] + padding
        """
        groups = sorted(groups, key=lambda g: g["target_x"])
        centers = []

        for i, g in enumerate(groups):
            if i == 0:
                cx = g["target_x"]
            else:
                prev = groups[i - 1]
                min_cx = centers[i - 1] + prev["radius"] + g["radius"] + padding
                cx = max(g["target_x"], min_cx)
            centers.append(cx)

        # Shift the whole row to stay near the desired "gravity" point.
        if centers:
            desired_mu = statistics.mean([g["target_x"] for g in groups])
            placed_mu = statistics.mean(centers)
            shift = desired_mu - placed_mu
            centers = [c + shift for c in centers]

        return groups, centers

    pos = {}

    # -------------------------
    # 3) Place nodes level-by-level
    # -------------------------
    for l in range(0, max_level + 1):
        nodes = level_nodes.get(l, [])
        if not nodes:
            continue

        # Identify intra-level connected components ("clique groups" / clusters).
        subg = G.subgraph(nodes)
        components = list(nx.connected_components(subg))
        components.sort(key=lambda c: min(c))  # deterministic ordering

        # Build group metadata: member nodes, radius, and desired X target.
        groups = []
        for i, comp in enumerate(components):
            cnodes = sorted(comp)
            r = _radius(len(cnodes))

            if l == 0:
                # Tight, predictable spacing at bottom.
                target_x = i * (L0_NODE_SPACING + 2.0 * r)
            else:
                # Anchor a group above its children (neighbors in level l-1).
                child_xs = []
                for u in cnodes:
                    for v in G.neighbors(u):
                        if levels.get(v) == l - 1 and v in pos:
                            child_xs.append(pos[v]["x"])

                target_x = statistics.mean(child_xs) if child_xs else i * (L0_NODE_SPACING + 2.0 * r)

            groups.append({"nodes": cnodes, "radius": r, "target_x": target_x})

        # Compress desired centers to reduce excessive spacing between groups.
        targets = [g["target_x"] for g in groups]
        if l == 0:
            targets = _compress_targets(targets, 0.80)
            pad = GROUP_PADDING_L0
        elif l == 1:
            targets = _compress_targets(targets, TARGET_COMPRESS_L1)
            pad = GROUP_PADDING_L1
        else:
            targets = _compress_targets(targets, TARGET_COMPRESS_OTHER)
            pad = GROUP_PADDING_OTHER

        for g, t in zip(groups, targets):
            g["target_x"] = t

        # Pack groups with non-overlap constraints.
        packed_groups, centers = _pack_groups(groups, pad)

        # Place groups on this level.
        base_y = -l * LEVEL_HEIGHT

        for g, cx in zip(packed_groups, centers):
            cnodes = g["nodes"]
            cnt = len(cnodes)
            r = g["radius"]

            if cnt == 1:
                pos[cnodes[0]] = {"x": float(cx), "y": float(base_y)}
                continue

            # Circular placement for nodes inside a group.
            start_angle = math.pi / 2.0
            step = (2.0 * math.pi) / cnt

            for k, n in enumerate(cnodes):
                ang = start_angle + k * step
                pos[n] = {
                    "x": float(cx + r * math.cos(ang)),
                    "y": float(base_y + r * math.sin(ang)),
                }

        # Keep each level roughly centered above its children (doesn't affect gaps, only drift).
        if l > 0:
            placed = [n for g in packed_groups for n in g["nodes"] if n in pos]
            if placed:
                current_xs = [pos[n]["x"] for n in placed]
                current_mid = (min(current_xs) + max(current_xs)) / 2.0

                child_xs_all = []
                for n in placed:
                    for v in G.neighbors(n):
                        if levels.get(v) == l - 1 and v in pos:
                            child_xs_all.append(pos[v]["x"])

                if child_xs_all:
                    ideal_mid = statistics.mean(child_xs_all)
                    shift = ideal_mid - current_mid
                    for n in placed:
                        pos[n]["x"] = float(pos[n]["x"] + shift)

    return pos






def to_cytoscape_elements(G, switch_ids, edges, positions):
    # Build or update the topology graph model and any derived per-node/per-edge metadata.
    elements = []
    for node in G.nodes():
        # Iterate over the relevant items and accumulate results.
        data = {"id": str(node), "label": f"{'S' if node in switch_ids else ''}{node}"}
        # Add node attributes if you have them (future proofing)
        classes = "switch" if node in switch_ids else "host"
        elements.append({
            "data": data,
            "position": positions.get(node, {"x": 0.0, "y": 0.0}),
            "classes": classes,
        })

    for src, dst, params in edges:
        # Iterate over the relevant items and accumulate results.
        base_class = "uplink" if ((src in switch_ids) ^ (dst in switch_ids)) else "peer"
        etype = (
            "etype-switch-switch" if (src in switch_ids and dst in switch_ids) else
            "etype-host-host" if (src not in switch_ids and dst not in switch_ids) else
            "etype-host-switch"
        )
        
        # Build label from standard params if present
        cap = params.get("capacity", "")
        lat = params.get("latency", "")
        lbl = ""
        if cap != "" and lat != "":
            # Branch based on the current state / selection.
            lbl = f"{int(cap) if isinstance(cap,float) and cap.is_integer() else cap}/{lat}ms"
            
        data = {
            "source": str(src),
            "target": str(dst),
            "label": lbl
        }
        # MERGE ALL PARAMS into data
        data.update(params)

        elements.append({
            "data": data,
            "classes": f"{base_class} {etype}",
        })

    return elements


# =========================
# Load data & Visualizer
# =========================

# Start with an empty topology; user will load one via the UI.
G = nx.Graph()
NUM_NODES = 0
SWITCH_IDS = set()
EDGES = []
POS = {}
ELEMS = []  # no cytoscape elements yet

# Default capacity range used by the filters until a topology is loaded
CAP_MIN = 0.0
CAP_MAX = 1.0

# NEW: Cache for topologies to make switching instant
TOPOLOGY_STATE = {}

def _get_or_create_topo_state(topo_id, path=None):
    """Ensure a cache entry exists. If path is provided, load the graph data."""
    # Get or create topology state.
    topo_id = int(topo_id)
    
    if topo_id not in TOPOLOGY_STATE:
        # Validate inputs / state before continuing.
        TOPOLOGY_STATE[topo_id] = {
            "path": path,
            "elements": [],
            "G": None,
            "pos": {},
            "cap_range": (0.0, 1.0),
            "logs": [],              
            "logs_selected": [],
            "layout_data": None,
            "layout_path": PRESET_FILE,
            "time_bounds": (0.0, 100.0),
            "segment": [0.0, 100.0]
        }

    state = TOPOLOGY_STATE[topo_id]
    
    # Lazy Load Graph Data
    if path and not state["elements"]:
        # Validate inputs / state before continuing.
        new_G, new_num_nodes, new_switch_ids, new_edges, new_ranges = parse_topology(path) # <--- Catch ranges
        new_pos = generate_preset_layout(new_G, new_switch_ids)
        new_elems = to_cytoscape_elements(new_G, new_switch_ids, new_edges, new_pos)
        
        state.update({
            "path": path,
            "G": new_G,
            "pos": new_pos,
            "elements": new_elems,
            "param_ranges": new_ranges # <--- Store this!
        })
        
        # Globals update (legacy support)
        global G, NUM_NODES, SWITCH_IDS, EDGES, ELEMS, TOPO_FILE, PARAM_RANGES
        G = new_G
        NUM_NODES = new_num_nodes
        SWITCH_IDS = new_switch_ids
        EDGES = new_edges
        ELEMS = new_elems
        TOPO_FILE = path
        PARAM_RANGES = new_ranges

    return state

def _recompute_topology_from_file(path: str):
    """
    Parse topology, compute positions, and update globals.
    Uses TOPO_CACHE to avoid re-parsing/re-computing layout on every switch.
    """
    # Recompute topology from file.
    global TOPO_FILE, G, NUM_NODES, SWITCH_IDS, EDGES, POS, ELEMS, CAP_MIN, CAP_MAX, TOPO_CACHE

    # Normalize path to ensure consistent keys
    # Resolve and validate filesystem paths before using them.
    path = os.path.abspath(path)

    # --- CACHE HIT: Return pre-calculated data immediately ---
    if path in TOPO_CACHE:
        # Branch based on the current state / selection.
        cache = TOPO_CACHE[path]
        TOPO_FILE = path
        G = cache["G"]
        NUM_NODES = cache["NUM_NODES"]
        SWITCH_IDS = cache["SWITCH_IDS"]
        EDGES = cache["EDGES"]
        POS = cache["POS"]
        ELEMS = cache["ELEMS"]
        CAP_MIN = cache["CAP_MIN"]
        CAP_MAX = cache["CAP_MAX"]
        return ELEMS

    # --- CACHE MISS: Compute everything from scratch ---
    TOPO_FILE = path
    G, NUM_NODES, SWITCH_IDS, EDGES = parse_topology(path)
    
    # This is the slow part (layout algorithm) -> runs only once per file now
    POS = generate_preset_layout(G, SWITCH_IDS)
    
    ELEMS = to_cytoscape_elements(G, SWITCH_IDS, EDGES, POS)

    cap_values = [cap for _, _, cap, _ in EDGES] or [0.0]
    CAP_MIN = float(min(cap_values))
    CAP_MAX = float(max(cap_values))
    if CAP_MIN == CAP_MAX:
        # Branch based on the current state / selection.
        CAP_MIN = max(0.0, CAP_MIN - 1.0)
        CAP_MAX = CAP_MAX + 1.0

    # Save results to cache
    TOPO_CACHE[path] = {
        "G": G,
        "NUM_NODES": NUM_NODES,
        "SWITCH_IDS": SWITCH_IDS,
        "EDGES": EDGES,
        "POS": POS,
        "ELEMS": ELEMS,
        "CAP_MIN": CAP_MIN,
        "CAP_MAX": CAP_MAX
    }

    return ELEMS


VIZ = None
def _init_visualizer(log_path, topo_path=None):
    """(Re)initialize the global Visualizer."""
    # Init visualizer.
    global VIZ, LOG_FILE
    LOG_FILE = log_path

    # If caller didn't pass topo_path, use the currently loaded topology
    topo_path = topo_path or TOPO_FILE

    try:
        # Only initialize if we actually have both paths and both exist
        if log_path and topo_path and os.path.exists(log_path) and os.path.exists(topo_path):
            # Branch based on the current state / selection.
            if str(log_path).lower().endswith(".json"):
                # Branch based on the current state / selection.
                VIZ = JsonVisualizer(log_path, topo_path)
            else:
                VIZ = interactiveinfo.Visualizer(log_path, topo_path)
        else:
            VIZ = None
    except Exception as e:
        # Recover from a failure case and return a safe default.
        print(f"[warn] Visualizer init failed: {e}")
        VIZ = None


def _time_bounds_from_viz():
    # Time bounds from visualization.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return 0.0, 0.0
    tmax = float(getattr(VIZ, "time", 0.0) or 0.0)
    for (t0, t1) in getattr(VIZ, "rankSendsByTime", {}).keys():
        # Iterate over the relevant items and accumulate results.
        tmax = max(tmax, float(t0), float(t1))
    for ch in range(len(getattr(VIZ, "chunkLifeCycle", []))):
        # Iterate over the relevant items and accumulate results.
        for _rank, arrivals in VIZ.chunkLifeCycle[ch].items():
            # Iterate over the relevant items and accumulate results.
            for (t, _msg) in arrivals:
                # Iterate over the relevant items and accumulate results.
                tmax = max(tmax, float(t))
    return 0.0, tmax

TIME_MIN, TIME_MAX = _time_bounds_from_viz()
SLIDER_STEP = max(1.0, round((TIME_MAX - TIME_MIN) / 500.0, 3)) if TIME_MAX > TIME_MIN else 1.0
# =========================
# Multi-log (XY overlay) support
# =========================
# Keep serializer-friendly metadata in dcc.Store (per log), and keep the heavy
# Visualizer objects in a process-level dict keyed by the same "id".
MULTI_VIZ_OBJS = {}  # id -> interactiveinfo.Visualizer

from contextlib import contextmanager

def _active_viz_from_multi(multi_logs, include_ids):
    """Return the Visualizer of the lowest selected log id, or None."""
    # Active visualization from multi.
    try:
        ids = sorted(int(i) for i in (include_ids or []))
    except Exception:
        # Recover from a failure case and return a safe default.
        ids = []
    if not ids:
        # Validate inputs / state before continuing.
        return None
    lid = ids[0]
    V = MULTI_VIZ_OBJS.get(lid)
    if V is None:
        # try to reconstruct from multi_logs store
        for it in (multi_logs or []):
            # Iterate over the relevant items and accumulate results.
            try:
                if int(it.get("id")) == lid:
                    # Branch based on the current state / selection.
                    path = it.get("path")
                    if path:
                        # Branch based on the current state / selection.
                        try:
                            V = JsonVisualizer(path, TOPO_FILE) if str(path).lower().endswith(".json") else interactiveinfo.Visualizer(path, TOPO_FILE)
                            MULTI_VIZ_OBJS[lid] = V
                        except Exception:
                            # Recover from a failure case and return a safe default.
                            V = None
                    break
            except Exception:
                # Recover from a failure case and return a safe default.
                continue
    return V

@contextmanager
def _use_viz(V):
    """Temporarily swap the global VIZ to V inside a with-block."""
    # Use visualization.
    global VIZ
    old = VIZ
    if V is not None:
        # Validate inputs / state before continuing.
        VIZ = V
    try:
        yield VIZ
    finally:
        VIZ = old


# Keep the "primary" stores (store-sends / start/finish maps) aligned with the active multi-log selection.
# This ensures that loading a session (or switching included logs) immediately re-populates the throughput plots
# and any other components that depend on these stores, without requiring the user to re-select parameters.
@app.callback(
    Output("store-sends", "data", allow_duplicate=True),
    Output("store-chunk-finish-times", "data", allow_duplicate=True),
    Output("store-chunk-start-times", "data", allow_duplicate=True),
    Input("multi-logs", "data"),
    Input("multi-logs-include", "data"),
    prevent_initial_call="initial_duplicate"
)
def sync_primary_stores_from_active_log(multi_logs, include_ids):
    # Choose the active log (lowest selected id) if any; otherwise fall back to the most recent log in multi_logs.
    logs = multi_logs or []
    chosen_id = None
    try:
        ids = sorted(int(i) for i in (include_ids or []))
        if ids:
            chosen_id = ids[0]
    except Exception:
        chosen_id = None

    if chosen_id is None and logs:
        try:
            chosen_id = int(logs[-1].get("id"))
        except Exception:
            chosen_id = None

    if chosen_id is None:
        return [], {}, {}

    bundle = None
    for it in logs:
        if not isinstance(it, dict):
            continue
        try:
            if int(it.get("id")) == int(chosen_id):
                bundle = it
                break
        except Exception:
            continue

    if not bundle:
        return [], {}, {}

    sends = bundle.get("sends") or []
    fin_map = bundle.get("fin_map") or {}
    start_map = bundle.get("start_map") or {}
    return sends, fin_map, start_map



# color palette for per-log traces
_MULTI_PAL = [
    "#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd",
    "#8c564b", "#e377c2", "#7f7f7f", "#bcbd22", "#17becf",
    "#4c78a8", "#f58518", "#54a24b", "#e45756", "#b279a2",
    "#9e765f", "#72b7b2", "#eeca3b", "#b07aa1", "#59a14f"
]
def _next_color(i): return _MULTI_PAL[i % len(_MULTI_PAL)]

def _build_log_bundle(path: str, label: str, color: str, log_id: int):
    """
    Build a serializable bundle for XY-plotting for a given .vis path.
    Also store the Visualizer object in MULTI_VIZ_OBJS[log_id].
    """
    # Next color.
    # Resolve and validate filesystem paths before using them.
    path = os.path.expanduser(path)
    if not os.path.isabs(path):
        # Validate inputs / state before continuing.
        # Resolve and validate filesystem paths before using them.
        path = os.path.join(BASE_DIR, path)

    if not os.path.exists(path):
        # Validate inputs / state before continuing.
        raise FileNotFoundError(path)

    # Instantiate a fresh Visualizer (independent of global VIZ)
    try:
        V = JsonVisualizer(path, TOPO_FILE) if str(path).lower().endswith('.json') else interactiveinfo.Visualizer(path, TOPO_FILE)
    except Exception as e:
        # Recover from a failure case and return a safe default.
        raise RuntimeError(f"Visualizer init failed for {path}: {e}")

    # Temporarily swap global VIZ so we can reuse the existing helpers.
    global VIZ
    _old = VIZ
    VIZ = V
    try:
        tmin, tmax = _time_bounds_from_viz()
        df_sends = _extract_sends_df()
        finish_map = _compute_chunk_finish_times()
        start_map  = _compute_chunk_start_times()
        chunk_cnt = int(getattr(V, "chunkCount", 0))
    finally:
        VIZ = _old

    MULTI_VIZ_OBJS[log_id] = V
    return {
        "id": int(log_id),
        "path": path,
        "label": label,
        "color": color,
        "tmin": float(tmin),
        "tmax": float(tmax),
        "sends": df_sends.to_dict("records"),
        "fin_map": {int(k): float(v) for k, v in (finish_map or {}).items()},
        "start_map": {int(k): float(v) for k, v in (start_map or {}).items()},
        "chunk_count": int(chunk_cnt),
    }


def panel_topology_details():
    """Panel for editing a topology (rename, load layout from file or defaults)."""
    return html.Div([
        html.H3("Topology Page", style={"margin": "0 0 12px"}),
        html.Div(id="topo-details-header", style=LABEL_MUTED | {"marginBottom": "12px"}),

        # --- 1. Rename Section ---
        html.H4("Rename Topology", style={"margin": "8px 0 6px"}),
        html.Div([
            dcc.Input(id="topo-rename-input", type="text", placeholder="Enter new name", style={"flex": "1"}),
            html.Button("Save Name", id="topo-rename-btn", n_clicks=0, style={"marginLeft": "8px"}),
        ], style={"display": "flex", "alignItems": "center"}),

        html.Hr(),

                html.Hr(),

        # --- Saved Layouts (Defaults) ---
        html.H4("Saved Layouts (Defaults)", style={"margin": "8px 0 6px"}),

        html.Div([
            html.Button("Refresh", id="defaults-refresh", n_clicks=0, style={"marginRight": "8px"}),

            dcc.Dropdown(
                id="default-select",
                options=[],
                placeholder="Select a saved default…",
                style={"flex": "1"}
            ),

            html.Button("Load", id="default-load-btn", n_clicks=0, style={"marginLeft": "8px"}),
            html.Button("Delete", id="default-delete-btn", n_clicks=0, style={"marginLeft": "8px"}),
        ], style={"display": "flex", "alignItems": "center"}),

        html.Div(id="default-selected-name", style=LABEL_MUTED | {"marginTop": "6px"}),
        html.Div(id="defaults-status", style=LABEL_MUTED | {"marginTop": "4px", "fontStyle": "italic"}),

        html.Div("Save Current View as New Default:",
                 style={"fontSize": "12px", "fontWeight": "600", "marginTop": "12px"}),

        html.Div([
            dcc.Input(
                id="default-name-input",
                type="text",
                placeholder="Layout Name (e.g. 'star_view')",
                style={"flex": "1"}
            ),
            html.Button("Save", id="default-save-btn", n_clicks=0, style={"marginLeft": "8px"}),
        ], style={"display": "flex", "marginTop": "4px"}),

        html.Hr(),

        # --- Layout JSON File (path is remembered the same way as before) ---
        html.H4("Layout JSON File", style={"margin": "8px 0 6px"}),

        dcc.Upload(
            id="upload-layout",
            children=html.Div(["Drag & Drop or ", html.A("Select .json")]),
            style={
                "width": "100%", "height": "40px", "lineHeight": "40px",
                "borderWidth": "1px", "borderStyle": "dashed", "borderRadius": "8px",
                "textAlign": "center", "marginBottom": "8px"
            },
            multiple=False
        ),

        html.Label("Path to JSON file:",
                   style={"fontSize": "12px", "fontWeight": "600", "marginTop": "6px"}),

        dcc.Input(
            id="path-input",
            type="text",
            value=PRESET_FILE,      # same default behavior as the old preset panel
            debounce=True,
            style={"width": "100%"}
        ),

        html.Div([
            html.Button("Save Layout", id="do-save", n_clicks=0, style={"marginRight": "8px"}),
            html.Button("Load Layout", id="do-load", n_clicks=0),
        ], style={"marginTop": "8px"}),

    ])

def panel_param_filters():
    """New dedicated panel for Parameter-based filtering."""
    return html.Div([
        html.H3("Parameter Filters", style={"margin": "0 0 12px"}),
        html.Div(
            "Filter edges by parameter range. Edges outside the range will be hidden.",
            style=LABEL_MUTED
        ),
        
        # 1. Select Parameter
        html.Label("Parameter", style={"fontWeight": 600, "marginTop": "12px", "display": "block"}),
        dcc.Dropdown(
            id="filter-param-dropdown",
            options=[],
            placeholder="Select parameter to filter...",
            clearable=True,
            style={"width": "100%"}
        ),
        
        # 2. Dynamic Range Slider
        html.Label("Range", style={"fontWeight": 600, "marginTop": "12px", "display": "block"}),
        html.Div(id="filter-slider-container", style={"padding": "0 10px 20px 10px"}, children=[
             dcc.RangeSlider(
                id="filter-param-slider",
                min=0, max=100, step=1,
                value=[0, 100],
                tooltip={"placement": "bottom", "always_visible": True}
             )
        ]),
        
        # 3. Action Buttons
        html.Div([
            html.Button("Apply Filter", id="apply-param-filter", n_clicks=0, style={"marginRight": "8px"}),
            html.Button("Clear", id="clear-param-filter", n_clicks=0),
        ], style={"marginTop": "8px"}),
        # Optional chunk filter (shown when a DataVar is selected above)
        html.Div(
            id="paramfilter-chunk-filter-container",
            style={"display": "none", "marginTop": "14px", "paddingTop": "12px", "borderTop": "1px solid #e1e7ef"},
            children=[
                html.Div("Chunk Filter", style={"fontWeight": 700, "marginBottom": "6px"}),
                html.Div(
                    "Restrict which chunks are included (optional).",
                    style=LABEL_MUTED
                ),
                dcc.Textarea(
                    id="pf-chunk-filter-text",
                    placeholder="Enter chunks: 1,2,5-9 ... (optional)",
                    style={"width": "100%", "height": "64px", "marginTop": "6px"}
                ),
                html.Div(
                    [
                        dcc.Input(id="pf-chunk-range-start", type="number", placeholder="start", style={"width": "70px", "marginRight": "6px"}),
                        dcc.Input(id="pf-chunk-range-end", type="number", placeholder="end", style={"width": "70px", "marginRight": "6px"}),
                        dcc.Input(id="pf-chunk-range-step", type="number", placeholder="step", value=1, style={"width": "70px", "marginRight": "6px"}),
                        html.Button("Add range", id="pf-chunk-add-range-btn", n_clicks=0),
                    ],
                    style={"display": "flex", "alignItems": "center", "gap": "6px", "marginTop": "8px", "flexWrap": "wrap"}
                ),
                html.Div(
                    [
                        html.Label("Min nodes at t_end (optional)", style={"fontWeight": 600, "marginRight": "8px"}),
                        dcc.Input(id="pf-chunk-min-nodes", type="number", placeholder="e.g., 2", style={"width": "90px"}),
                    ],
                    style={"display": "flex", "alignItems": "center", "gap": "6px", "marginTop": "10px", "flexWrap": "wrap"}
                ),
                html.Div(
                    [
                        html.Button("Apply Chunk Filter", id="pf-apply-chunk-filter", n_clicks=0, style={"marginRight": "8px"}),
                        html.Button("Clear", id="pf-clear-chunk-filter", n_clicks=0),
                    ],
                    style={"marginTop": "10px"}
                ),
                html.Div(id="pf-chunk-filter-status", style=LABEL_MUTED | {"marginTop": "10px"}),
            ]
        ),


        html.Div(id="filter-status-msg", style=LABEL_MUTED | {"marginTop": "12px"})
    # Update the viewport pan/translation for the network graph.
    ])

def _rank_count():
    # Rank count.
    try:
        return int(VIZ.linkInfo.rankCount)
    except Exception:
        # Recover from a failure case and return a safe default.
        return NUM_NODES

# =========================
# Small helpers (sim)
# =========================

# ---------- Throughput / Load helpers ----------
def _atomic_json_write(path, obj):
    # Atomic json write.
    # Resolve and validate filesystem paths before using them.
    path = os.path.expanduser(path)
    # Resolve and validate filesystem paths before using them.
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        # Open the file and ensure it is closed correctly.
        json.dump(obj, f, indent=2)
    os.replace(tmp, path)

def _extract_sends_df():
    # Returns a DataFrame with at least t_start, t_end columns; other columns are optional.
    # Extract sends dataframe.
    cols = ["t_start", "t_end", "chunk", "src", "dst"]
    if VIZ is None:
        # Validate inputs / state before continuing.
        return pd.DataFrame(columns=cols)

    recs = []

    # Heuristic 1: rankSendsByTime as dict with (t0,t1)->list(...)
    rsbt = getattr(VIZ, "rankSendsByTime", None)
    if isinstance(rsbt, dict) and rsbt:
        # Branch based on the current state / selection.
        for k, v in rsbt.items():
            # Iterate over the relevant items and accumulate results.
            try:
                t0, t1 = k
                t0 = float(t0); t1 = float(t1)
            except Exception:
                # Recover from a failure case and return a safe default.
                continue
            # If we don't know per-send metadata, still record the interval.
            if isinstance(v, (list, tuple)) and v:
                # Branch based on the current state / selection.
                for _item in v:
                    # Iterate over the relevant items and accumulate results.
                    recs.append({"t_start": t0, "t_end": t1, "chunk": None, "src": None, "dst": None})
            else:
                recs.append({"t_start": t0, "t_end": t1, "chunk": None, "src": None, "dst": None})

    # Heuristic 2: sendIntervals / sends as iterable of dicts/tuples with time fields
    for attr in ("sendIntervals", "sends"):
        # Iterate over the relevant items and accumulate results.
        obj = getattr(VIZ, attr, None)
        if isinstance(obj, (list, tuple)):
            # Branch based on the current state / selection.
            for it in obj:
                # Iterate over the relevant items and accumulate results.
                t0 = t1 = None
                if isinstance(it, dict):
                    # Branch based on the current state / selection.
                    for k in ("t0", "t_start", "start", "begin"):
                        # Iterate over the relevant items and accumulate results.
                        if k in it: t0 = it[k]; break
                    for k in ("t1", "t_end", "end", "finish"):
                        # Iterate over the relevant items and accumulate results.
                        if k in it: t1 = it[k]; break
                    c  = it.get("chunk") if "chunk" in it else None
                    s  = it.get("src") if "src" in it else None
                    d  = it.get("dst") if "dst" in it else None
                elif isinstance(it, (list, tuple)) and len(it) >= 2:
                    # Alternative branch for a different condition.
                    t0, t1 = it[0], it[1]
                    c = s = d = None
                else:
                    continue
                try:
                    t0 = float(t0); t1 = float(t1)
                    if t1 < t0: t0, t1 = t1, t0
                    recs.append({"t_start": t0, "t_end": t1, "chunk": c, "src": s, "dst": d})
                except Exception:
                    # Recover from a failure case and return a safe default.
                    pass

    if not recs:
        # Validate inputs / state before continuing.
        return pd.DataFrame(columns=cols)
    # Create a DataFrame to make filtering/aggregation/plotting simpler.
    df = pd.DataFrame.from_records(recs)
    # Ensure required columns exist
    for c in cols:
        # Iterate over the relevant items and accumulate results.
        if c not in df.columns:
            # Validate inputs / state before continuing.
            df[c] = None
    return df[cols]


def _line_fig(x, y, title, yaxis_title):


    # Compute the current visualization and return an updated Plotly figure and related UI state.
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    mask = np.isfinite(x) & np.isfinite(y)

    # Build a fresh Plotly figure for the current view.
    fig = go.Figure()
    if mask.sum() == 0:
        # Branch based on the current state / selection.
        fig.add_annotation(
            text="No data in current range",
            x=0.5, y=0.5, xref="paper", yref="paper",
            showarrow=False, font=dict(size=14)
        )
        fig.update_layout(
            title=title,
            xaxis_title="time",
            yaxis_title=yaxis_title,
            margin=dict(l=40, r=10, t=48, b=40),
            uirevision="xy"
        )
        return fig

    # Add/update figure traces and styling.
    fig.add_trace(go.Scatter(x=x[mask], y=y[mask], mode="lines", name=title, connectgaps=False))
    fig.update_layout(
        title=title,
        xaxis_title="time",
        yaxis_title=yaxis_title,
        margin=dict(l=40, r=10, t=48, b=40),
        uirevision="xy",
        hovermode="x unified",
    )
    # Add/update figure traces and styling.
    fig.update_xaxes(rangeslider=dict(visible=True))
    # Add/update figure traces and styling.
    fig.update_yaxes(rangemode="tozero")
    return fig



# --- robust arrival time helpers ---

def _first_time(arrivals):
    """Return earliest time in an arrivals list that may be [(t,msg)] OR [t] OR single t."""
    # First time.
    if arrivals is None:
        # Validate inputs / state before continuing.
        return None
    try:
        # [(t, msg), ...]
        return min(float(a[0]) for a in arrivals if a is not None and len(a) >= 1)
    except Exception:
        # Recover from a failure case and return a safe default.
        try:
            # [t, t, ...]
            return min(float(a) for a in arrivals if a is not None)
        except Exception:
            # Recover from a failure case and return a safe default.
            try:
                # scalar t
                return float(arrivals)
            except Exception:
                # Recover from a failure case and return a safe default.
                return None

def _compute_chunk_finish_times():
    """Finish time = the latest among per-target first-arrivals (i.e., last target to first-get it)."""
    # Compute chunk finish times.
    out = {}
    if VIZ is None:
        # Validate inputs / state before continuing.
        return out
    clc = getattr(VIZ, "chunkLifeCycle", [])
    for cid in range(len(clc)):
        # Iterate over the relevant items and accumulate results.
        arrivals_dict = clc[cid]
        # accept both dict (rank->arrivals) and list (idx->arrivals)
        if not isinstance(arrivals_dict, (dict, list, tuple)):
            # Validate inputs / state before continuing.
            continue
        times = []
        it = arrivals_dict.items() if isinstance(arrivals_dict, dict) else enumerate(arrivals_dict)
        for _rank, arrivals in it:
            # Iterate over the relevant items and accumulate results.
            t_first = _first_time(arrivals)
            if t_first is not None:
                # Validate inputs / state before continuing.
                times.append(float(t_first))
        if times:
            # Branch based on the current state / selection.
            out[int(cid)] = float(max(times))
    return out

def _compute_chunk_start_times():
    """Start time = the earliest among per-target first-arrivals (i.e., first target to first-get it)."""
    # Compute chunk start times.
    out = {}
    if VIZ is None:
        # Validate inputs / state before continuing.
        return out
    clc = getattr(VIZ, "chunkLifeCycle", [])
    for cid in range(len(clc)):
        # Iterate over the relevant items and accumulate results.
        arrivals_dict = clc[cid]
        if not isinstance(arrivals_dict, (dict, list, tuple)):
            # Validate inputs / state before continuing.
            continue
        times = []
        it = arrivals_dict.items() if isinstance(arrivals_dict, dict) else enumerate(arrivals_dict)
        for _rank, arrivals in it:
            # Iterate over the relevant items and accumulate results.
            t_first = _first_time(arrivals)
            if t_first is not None:
                # Validate inputs / state before continuing.
                times.append(float(t_first))
        if times:
            # Branch based on the current state / selection.
            out[int(cid)] = float(min(times))
    return out


def _series_wip_from_intervals(df, bins=300):
    """Active sends at time t: (# starts <= t) - (# ends <= t)."""
    # Series wip from intervals.
    if df.empty:
        # Branch based on the current state / selection.
        return [], []
    t0 = float(df["t_start"].min()); t1 = float(df["t_end"].max())
    if t1 <= t0: t1 = t0 + 1.0
    t = np.linspace(t0, t1, bins, dtype=float)
    s = np.sort(df["t_start"].to_numpy(dtype=float))
    e = np.sort(df["t_end"].to_numpy(dtype=float))
    wip = np.searchsorted(s, t, side="right") - np.searchsorted(e, t, side="right")
    return t, wip


def _series_cum_finished(fin_map, bins=300):
    # Series cum finished.
    if not fin_map:
        # Validate inputs / state before continuing.
        return [], []
    ft = np.array([float(v) for v in fin_map.values()], dtype=float)
    t0, t1 = float(np.min(ft)), float(np.max(ft))
    if t1 <= t0: t1 = t0 + 1.0
    edges = np.linspace(t0, t1, bins + 1)
    counts = np.histogram(ft, bins=edges)[0]
    cum = np.cumsum(counts)
    centers = (edges[:-1] + edges[1:]) / 2.0
    return centers, cum-1

def _series_avg_send_duration(df, bins=300, anchor="t_end"):
    # Series avg send duration.
    if df.empty:
        # Branch based on the current state / selection.
        return [], []
    t0 = float(df[anchor].min()); t1 = float(df[anchor].max())
    if t1 <= t0: t1 = t0 + 1.0
    edges = np.linspace(t0, t1, bins + 1)
    durations = (df["t_end"].astype(float) - df["t_start"].astype(float)).clip(lower=0.0).values
    sums   = np.histogram(df[anchor].astype(float).values, bins=edges, weights=durations)[0]
    counts = np.histogram(df[anchor].astype(float).values, bins=edges)[0]
    with np.errstate(divide="ignore", invalid="ignore"):
        # Use a context manager to manage resources safely.
        avg = np.where(counts > 0, sums / counts, np.nan)
    centers = (edges[:-1] + edges[1:]) / 2.0
    return centers, avg

def _chunk_wip_from_start_finish(starts_map, fins_map, bins=300):
    # Chunk wip from start finish.
    if not starts_map or not fins_map:
        # Validate inputs / state before continuing.
        return [], []
    t0 = min(float(v) for v in starts_map.values())
    t1 = max(float(v) for v in fins_map.values())
    if t1 <= t0: t1 = t0 + 1.0
    edges = np.linspace(t0, t1, bins + 1)
    starts = np.histogram([float(v) for v in starts_map.values()], bins=edges)[0]
    fins   = np.histogram([float(v) for v in fins_map.values()],   bins=edges)[0]
    wip = np.cumsum(starts - fins)
    centers = (edges[:-1] + edges[1:]) / 2.0
    return centers, wip


# ---- Fast path cache for Post-left chart ----
from bisect import bisect_right

def _safe_min(seq, default=None):
    # Safe min.
    try:
        return min(seq)
    except ValueError:
        # Recover from a failure case and return a safe default.
        return default

def panel_color():
    return html.Div([
        html.Div(
            [
                html.Button(
                    "Filters",
                    id="btn-links-filters-shortcut",
                    n_clicks=0,
                    style={"fontSize": "11px", "padding": "2px 8px", "borderRadius": "8px", "border": "1px solid #e1e7ef", "background": "#f5f7fa", "cursor": "pointer"}
                ),
                html.Span("Go to Link Filters", style=LABEL_MUTED),
            ],
            style={
                "display": "flex",
                "justifyContent": "flex-end",
                "alignItems": "center",
                "marginBottom": "6px",
            },
        ),
        html.H3("Coloring", style={"margin": "0 0 12px"}),
        
        html.H4("Standard Modes", style={"margin": "8px 0 4px"}),
        dcc.RadioItems(
            id="color-mode-radio",
            options=[
                {"label": "None", "value": "none"},
                {"label": "By capacity", "value": "capacity"},
                {"label": "By latency", "value": "latency"},
                {"label": "By avg flow (segment)", "value": "flow"},
                {"label": "By avg flow / cap", "value": "flow_frac"},
                # This option is auto-selected when you pick a parameter below
                {"label": "By Parameter (Custom)", "value": "parameter"},
            ],
            value="none",
            inline=False,
            style={"marginBottom": "16px"},
        ),

        html.Hr(),
        html.H4("Log Parameters", style={"margin": "8px 0 4px"}),
        html.Div("Select a parameter from the imported file (e.g. 'Flow'). Colors will represent the average value over the current time segment.", style=LABEL_MUTED),
        
        dcc.Dropdown(
            id="param-select-dropdown",
            options=[],
            placeholder="Select a parameter...",
            clearable=True,
            style={"marginTop": "8px", "width": "100%"}
        ),
        
        html.Div(id="param-stats-info", style=LABEL_MUTED | {"marginTop": "8px"}),
    # Update the viewport pan/translation for the network graph.
    ])

def _get_viz_parameters(viz=None):
    """Scan the given VIZ object (or global if None) for LinkVars AND DataVars."""
    # Get visualization parameters.
    target = viz if viz is not None else VIZ
    params = []
    if target is None:
        # Validate inputs / state before continuing.
        return params
    
    # 1. Link Variables
    for lv in getattr(target, "link_vars", []):
        # Iterate over the relevant items and accumulate results.
        params.append({"label": f"{lv.name} (Link)", "value": lv.name, "type": "link"})

    # 2. Data Variables
    for dv in getattr(target, "data_vars", []):
        # Iterate over the relevant items and accumulate results.
        params.append({"label": f"{dv.name} (Data/Chunks)", "value": dv.name, "type": "data"})
    
    return params

def _compute_chunk_finish_times_from_lifecycle(chunk_lc):
    """Finish time = latest among per-target first-arrivals for a given chunkLifeCycle list."""
    out = {}
    if not chunk_lc:
        return out
    try:
        L = len(chunk_lc)
    except Exception:
        return out
    for cid in range(L):
        arrivals_dict = chunk_lc[cid]
        if not isinstance(arrivals_dict, (dict, list, tuple)):
            continue
        times = []
        it = arrivals_dict.items() if isinstance(arrivals_dict, dict) else enumerate(arrivals_dict)
        for _rank, arrivals in it:
            t_first = _first_time(arrivals)
            if t_first is not None:
                times.append(float(t_first))
        if times:
            out[int(cid)] = float(max(times))
    return out


def _compute_chunk_start_times_from_lifecycle(chunk_lc):
    """Start time = earliest among per-target first-arrivals for a given chunkLifeCycle list."""
    out = {}
    if not chunk_lc:
        return out
    try:
        L = len(chunk_lc)
    except Exception:
        return out
    for cid in range(L):
        arrivals_dict = chunk_lc[cid]
        if not isinstance(arrivals_dict, (dict, list, tuple)):
            continue
        times = []
        it = arrivals_dict.items() if isinstance(arrivals_dict, dict) else enumerate(arrivals_dict)
        for _rank, arrivals in it:
            t_first = _first_time(arrivals)
            if t_first is not None:
                times.append(float(t_first))
        if times:
            out[int(cid)] = float(min(times))
    return out


def _select_data_var_for_collective(V, coll_obj):
    """
    Resolve the *active* data/chunk variable object for a given collective/log.

    Rules:
      - If the collective explicitly chose "(none)" => return None.
      - If active_data_param is missing => auto-pick the first non-hidden data var (or primary_data) if available.
      - If active_data_param is set but not found => return None (do not silently fall back).
    """
    if V is None:
        return None

    coll = coll_obj or {}
    explicit_key = ("active_data_param" in coll)

    wanted = None
    if explicit_key:
        raw = coll.get("active_data_param")
        if raw is None:
            return None
        raw_s = str(raw).strip()
        if raw_s == "" or raw_s.lower() in ("__none__", "none", "(none)"):
            return None
        wanted = raw_s  # explicit selection
    else:
        wanted = None   # auto selection

    hidden = set(coll.get("hidden_params", []) or [])

    dvs = getattr(V, "data_vars", None)
    if isinstance(dvs, (list, tuple)) and len(dvs) > 0:
        if wanted is not None:
            for dv in dvs:
                nm = getattr(dv, "name", None)
                if nm is not None and str(nm) == str(wanted):
                    return dv
            return None
        # auto: first non-hidden
        for dv in dvs:
            nm = getattr(dv, "name", None)
            if nm is None:
                continue
            if str(nm) in hidden:
                continue
            return dv
        return dvs[0]

    primary = getattr(V, "primary_data", None)
    if primary is not None:
        if wanted is None:
            return primary
        nm = getattr(primary, "name", None)
        if nm is not None and str(nm) == str(wanted):
            return primary
        return None

    # Fallback: treat the visualizer itself as the data source (single-var backends).
    if wanted is None:
        return V
    # If the collective explicitly picked a named var but we cannot resolve it, do not guess.
    return V if not explicit_key else None



def _dv_chunk_counts_in_segment(dv, t0, t1):
    """
    For a DataVar-like object, compute how many DISTINCT chunks were present on:
      - each node (as a host/location), and
      - each link (as an in-flight traversal)
    at ANY time overlapping the segment [t0, t1].

    Returns:
      (node_counts: dict[str,int], link_counts: dict[str,int])
    """
    try:
        t0 = float(t0); t1 = float(t1)
    except Exception:
        return {}, {}
    if t1 < t0:
        t0, t1 = t1, t0

    from collections import defaultdict

    node_chunks = defaultdict(set)  # node -> set(chunk)
    link_chunks = defaultdict(set)  # "src-dst" -> set(chunk)

    # --- Link presence: prefer explicit intervals if available ---
    try:
        lci = getattr(dv, "linkChunkIntervals", None)
        if isinstance(lci, dict):
            for (src, dst), intervals in lci.items():
                if not intervals:
                    continue
                key = f"{int(src)}-{int(dst)}"
                for rec in intervals:
                    try:
                        st, en, ch = rec
                        st = float(st); en = float(en); ch = int(ch)
                    except Exception:
                        continue
                    if en >= t0 and st <= t1:
                        link_chunks[key].add(ch)
    except Exception:
        pass

    # --- Node presence: if we have sends, infer node intervals; else fall back to arrival-only heuristic ---
    sends = getattr(dv, "sends", None)
    if isinstance(sends, list) and sends:
        # Group sends by chunk.
        by_chunk = defaultdict(list)
        max_t = 0.0
        for s in sends:
            try:
                ch = int(s.get("chunk"))
                st = float(s.get("t_start"))
                en = float(s.get("t_end"))
                src = int(s.get("src"))
                dst = int(s.get("dst"))
            except Exception:
                continue
            by_chunk[ch].append((st, en, src, dst))
            if en > max_t:
                max_t = en
        sim_end = float(getattr(dv, "time", max_t) or max_t)

        # Helper: best-effort initial arrival on a node for a chunk (includes seeds).
        node_lc = getattr(dv, "nodeLifeCycle", None)
        def _initial_arrival(node_id: int, chunk_id: int, default_t: float) -> float:
            try:
                if isinstance(node_lc, list) and 0 <= node_id < len(node_lc):
                    arrs = node_lc[node_id].get(chunk_id)
                    if arrs:
                        return float(min(float(ts) for (ts, _msg) in arrs))
            except Exception:
                pass
            return float(default_t)

        for ch, lst in by_chunk.items():
            lst.sort(key=lambda it: it[0])  # by t_start
            # Initialize from the src of the first send.
            st0, en0, src0, dst0 = lst[0]
            cur_node = int(src0)
            cur_arr = _initial_arrival(cur_node, ch, st0)

            for st, en, src, dst in lst:
                # If the log is inconsistent, realign to the stated src.
                if int(src) != cur_node:
                    # Close previous interval (best-effort) up to this start.
                    if cur_node is not None:
                        a0, a1 = float(cur_arr), float(st)
                        if a1 >= t0 and a0 <= t1:
                            node_chunks[int(cur_node)].add(int(ch))
                    cur_node = int(src)
                    cur_arr = _initial_arrival(cur_node, ch, st)

                # Chunk is on src from last arrival until this send starts.
                a0, a1 = float(cur_arr), float(st)
                if a1 < a0:
                    a0, a1 = a1, a0
                if a1 >= t0 and a0 <= t1:
                    node_chunks[int(cur_node)].add(int(ch))

                # After the send, chunk arrives at dst at time en.
                cur_node = int(dst)
                cur_arr = float(en)

            # After last arrival, assume chunk remains on the last node until sim_end.
            a0, a1 = float(cur_arr), float(sim_end)
            if a1 < a0:
                a0, a1 = a1, a0
            if a1 >= t0 and a0 <= t1:
                node_chunks[int(cur_node)].add(int(ch))
    else:
        # Arrival-only heuristic: count any chunk that arrived by t1.
        node_lc = getattr(dv, "nodeLifeCycle", None)
        if isinstance(node_lc, list):
            for nid in range(len(node_lc)):
                arrivals_dict = node_lc[nid]
                if not isinstance(arrivals_dict, dict):
                    continue
                for ch, arrs in arrivals_dict.items():
                    if not arrs:
                        continue
                    try:
                        t_first = float(min(float(ts) for (ts, _msg) in arrs))
                    except Exception:
                        continue
                    # We cannot infer leave time without sends; treat "arrived by t1" as "present in window".
                    if t_first <= t1:
                        try:
                            node_chunks[int(nid)].add(int(ch))
                        except Exception:
                            pass

    node_counts = {str(n): len(s) for n, s in node_chunks.items()}
    link_counts = {k: len(s) for k, s in link_chunks.items()}
    return node_counts, link_counts



def _calculate_param_values(param_name, t0, t1, data_id=None, viz=None):
    """Calculate values for the named parameter on a specific VIZ object."""
    # Calculate param values.
    target_var = None
    var_type = "link"
    target_viz = viz if viz is not None else VIZ
    
    if target_viz is None or not param_name:
        # Validate inputs / state before continuing.
        return {}

    # Find the variable in the specific VIZ
    for lv in getattr(target_viz, "link_vars", []):
        # Iterate over the relevant items and accumulate results.
        if lv.name == param_name:
            # Branch based on the current state / selection.
            target_var = lv; var_type = "link"; break
    
    if target_var is None:
        # Validate inputs / state before continuing.
        for dv in getattr(target_viz, "data_vars", []):
            # Iterate over the relevant items and accumulate results.
            if dv.name == param_name:
                # Branch based on the current state / selection.
                target_var = dv; var_type = "data"; break

    if target_var is None:
        # Validate inputs / state before continuing.
        return {}

    # --- LINK LOGIC ---
    if var_type == "link":
        # Branch based on the current state / selection.
        values = {}
        vals_list = []
        per_link = getattr(target_var, "per_link", {})
        for (src, dst), series in per_link.items():
            # Iterate over the relevant items and accumulate results.
            avg = _avg_series_on_segment(series, t0, t1)
            key = f"{src}-{dst}"
            values[key] = avg
            vals_list.append(avg)
        
        vmin, vmax = (min(vals_list), max(vals_list)) if vals_list else (0.0, 1.0)
        return {"type": "link", "data": values, "min": vmin, "max": vmax, "name": param_name}

    # --- DATA LOGIC ---
    elif var_type == "data":
        # DataVars support two different usages:
        #   (A) "counts" mode (data_id is None): compute per-node/per-link DISTINCT chunk counts in [t0,t1]
        #       and use that for filtering.
        #   (B) "trace" mode (data_id provided): trace a specific chunk through nodes/links in [t0,t1]
        #       and use that for coloring/highlighting.
        if data_id is None:
            node_counts, link_counts = _dv_chunk_counts_in_segment(target_var, t0, t1)
            all_vals = []
            try:
                all_vals.extend([int(v) for v in (node_counts or {}).values()])
                all_vals.extend([int(v) for v in (link_counts or {}).values()])
            except Exception:
                pass
            # Always include 0 in the range (entities with no chunks are treated as 0).
            if all_vals:
                vmin, vmax = 0, max(all_vals)
            else:
                vmin, vmax = 0, 1
            return {
                "type": "data",
                "mode": "counts",
                "node_counts": node_counts,
                "link_counts": link_counts,
                "min": float(vmin),
                "max": float(vmax),
                "name": param_name,
            }

        # ---- trace mode (existing behavior) ----
        try:
            cid = int(data_id)
        except Exception:
            return {"type": "data", "error": "Invalid Data ID"}

        links = target_var.links_for_chunk_in_segment(cid, t0, t1)
        if links:
            t_vals = [l['t_end'] for l in links]
            l_min, l_max = min(t_vals), max(t_vals)
        else:
            l_min, l_max = t0, t1

        nodes_with_chunk = []
        node_lc = getattr(target_var, "nodeLifeCycle", [])
        for r in range(len(node_lc)):
            arrivals = node_lc[r].get(cid, [])
            if not arrivals:
                continue
            try:
                t_first = _safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0)
                if t_first <= t1:
                    nodes_with_chunk.append(r)
            except Exception:
                pass

        return {
            "type": "data",
            "mode": "trace",
            "links": links,
            "nodes": nodes_with_chunk,
            "t_min": l_min,
            "t_max": l_max,
            "name": param_name,
            "data_id": cid,
        }
    return {}



def _get_active_viz_list(active_coll_map, active_topo_id, topo_collectives):
    """
    Return list of VIZ objects for logs in ACTIVE COLLECTIVES of the active topology.
    """
    # Get active visualization list.
    if not active_topo_id: return []
    
    tid = str(active_topo_id)
    collectives = (topo_collectives or {}).get(tid, [])
    # Robustly handle active IDs (force int)
    raw_actives = (active_coll_map or {}).get(tid, [])
    active_cids = set(int(x) for x in raw_actives)
    
    viz_list = []
    
    for coll in collectives:
        # Iterate over the relevant items and accumulate results.
        if int(coll["id"]) in active_cids:
            # Branch based on the current state / selection.
            for log in coll.get("logs", []):
                # Iterate over the relevant items and accumulate results.
                lid = int(log["id"])
                V = MULTI_VIZ_OBJS.get(lid)
                if V is None:
                    # Lazy load fallback
                    path = log.get("path", "")
                    try:
                        if str(path).lower().endswith(".json"):
                            # Branch based on the current state / selection.
                            V = JsonVisualizer(path, TOPO_FILE)
                        else:
                            V = interactiveinfo.Visualizer(path, TOPO_FILE)
                        MULTI_VIZ_OBJS[lid] = V
                    except: V = None
                if V: viz_list.append(V)
                
    return viz_list

def _get_active_log_bundles(active_coll_map, active_topo_id, topo_collectives):
    """
    Return log bundles (dicts) for ACTIVE COLLECTIVES in the active topology.

    Notes:
    - Each returned item is a *copy* of the underlying log bundle (so we do not mutate store data).
    - We attach collective metadata for UI/legend grouping:
        * _coll_id    : int
        * _coll_name  : str
        * _coll_color : str (best-effort; prefers collective-level color if present)
    """
    if not active_topo_id:
        return []

    tid = str(active_topo_id)
    collectives = (topo_collectives or {}).get(tid, [])
    raw_actives = (active_coll_map or {}).get(tid, [])

    # Defensive parsing: collective IDs may arrive as strings.
    active_cids = set()
    for x in (raw_actives or []):
        try:
            active_cids.add(int(x))
        except Exception:
            continue

    out = []
    for ci, coll in enumerate(collectives or []):
        try:
            cid = int(coll.get("id"))
        except Exception:
            continue

        if cid not in active_cids:
            continue

        coll_name = coll.get("name") or f"Collective {cid}"

        # Prefer a collective-level color (if present); else fall back to the first log color; else palette.
        coll_color = coll.get("color")
        if not coll_color:
            logs0 = coll.get("logs") or []
            if logs0 and isinstance(logs0[0], dict):
                coll_color = logs0[0].get("color")
        if not coll_color:
            coll_color = _next_color(ci)

        for lb in (coll.get("logs") or []):
            if not isinstance(lb, dict):
                continue
            cp = dict(lb)
            cp["_coll_id"] = cid
            cp["_coll_name"] = coll_name
            cp["_coll_color"] = coll_color
            out.append(cp)

    return out

def _aggregate_param_values(param_name, t0, t1, data_id, viz_list):
    """Aggregate parameter values across multiple logs (Average for links, Union for data)."""
    # Aggregate param values.
    if not viz_list: return {}
    
    results = []
    for v in viz_list:
        # Iterate over the relevant items and accumulate results.
        res = _calculate_param_values(param_name, t0, t1, data_id, viz=v)
        if res: results.append(res)
            
    if not results: return {}
    
    # Use the type of the first result to decide aggregation strategy
    p_type = results[0].get("type")
    
    if p_type == "link":
        # AVERAGE the values per link
        merged = {}; counts = {}; all_vals = []
        for r in results:
            # Iterate over the relevant items and accumulate results.
            if r.get("type") != "link": continue
            for k, val in r.get("data", {}).items():
                # Iterate over the relevant items and accumulate results.
                merged[k] = merged.get(k, 0.0) + val
                counts[k] = counts.get(k, 0) + 1
        
        final_data = {}
        for k, total in merged.items():
            # Iterate over the relevant items and accumulate results.
            avg = total / counts[k]
            final_data[k] = avg
            all_vals.append(avg)
            
        vmin, vmax = (min(all_vals), max(all_vals)) if all_vals else (0.0, 1.0)
        return {"type": "link", "data": final_data, "min": vmin, "max": vmax, "name": param_name}

    elif p_type == "data":
        # DataVars can be aggregated in two modes:
        #   - mode='counts' (data_id is None): MAX per-node/per-link chunk counts across logs
        #   - mode='trace'  (data_id provided): UNION of highlighted nodes/links for the specific chunk
        mode0 = results[0].get("mode")

        if mode0 == "counts":
            node_max = {}
            link_max = {}
            for r in results:
                if r.get("type") != "data" or r.get("mode") != "counts":
                    continue
                for nid, cnt in (r.get("node_counts") or {}).items():
                    try:
                        k = str(nid)
                        v = int(cnt)
                    except Exception:
                        continue
                    node_max[k] = max(node_max.get(k, 0), v)

                for lk, cnt in (r.get("link_counts") or {}).items():
                    try:
                        k = str(lk)
                        v = int(cnt)
                    except Exception:
                        continue
                    link_max[k] = max(link_max.get(k, 0), v)

            all_vals = []
            try:
                all_vals.extend([int(v) for v in node_max.values()])
                all_vals.extend([int(v) for v in link_max.values()])
            except Exception:
                pass

            # Always include 0 in the range (entities with no chunks are treated as 0).
            if all_vals:
                vmin, vmax = 0, max(all_vals)
            else:
                vmin, vmax = 0, 1

            return {
                "type": "data",
                "mode": "counts",
                "node_counts": node_max,
                "link_counts": link_max,
                "min": float(vmin),
                "max": float(vmax),
                "name": param_name,
            }

        # ---- trace mode (existing behavior) ----
        all_links = []
        all_nodes = set()
        t_mins = []
        t_maxs = []
        for r in results:
            if r.get("type") != "data" or r.get("mode") != "trace":
                continue
            all_links.extend(r.get("links", []))
            all_nodes.update(r.get("nodes", []))
            t_mins.append(r.get("t_min", 0))
            t_maxs.append(r.get("t_max", 1))

        return {
            "type": "data",
            "mode": "trace",
            "links": all_links,
            "nodes": list(all_nodes),
            "t_min": min(t_mins) if t_mins else 0,
            "t_max": max(t_maxs) if t_maxs else 1,
            "name": param_name,
            "data_id": data_id,
        }
    return {}

def panel_filters_generic():
    return html.Div([
        html.H3("Filters", style={"margin": "0 0 12px"}),
        html.Div("Filter edges by parameter range:", style=LABEL_MUTED),
        
        # 1. Select Parameter
        dcc.Dropdown(
            id="filter-param-select", 
            options=[], 
            placeholder="Select parameter to filter...",
            style={"marginTop": "8px"}
        ),
        
        # 2. Dynamic Range Slider
        html.Div(id="filter-slider-container", style={"marginTop": "20px", "padding": "0 10px"}),
        
        html.Div(id="filter-status-generic", style=LABEL_MUTED | {"marginTop": "12px"})
    # Update the viewport pan/translation for the network graph.
    ])

_NODE_FIRSTS_ALL = {}       # node -> sorted list of first-arrival times (all chunks)
_NODE_FIRSTS_BY_CHUNK = {}  # node -> {chunk_id: first-arrival time}

def _warm_node_arrival_cache(hosts_only=True):
    """Build per-node first arrival times once; returns how many nodes were cached."""
    # Warm node arrival cache.
    global _NODE_FIRSTS_ALL, _NODE_FIRSTS_BY_CHUNK
    _NODE_FIRSTS_ALL = {}
    _NODE_FIRSTS_BY_CHUNK = {}
    if VIZ is None:
        # Validate inputs / state before continuing.
        return 0
    node_lc = getattr(VIZ, "nodeLifeCycle", [])
    count = 0
    for r in range(len(node_lc)):
        # Iterate over the relevant items and accumulate results.
        if hosts_only and r in SWITCH_IDS:
            # Branch based on the current state / selection.
            continue
        arrivals_dict = node_lc[r]
        if not isinstance(arrivals_dict, dict):
            # Validate inputs / state before continuing.
            continue
        perchunk = {}
        firsts = []
        for cid, arrivals in arrivals_dict.items():
            # Iterate over the relevant items and accumulate results.
            if not arrivals:
                # Validate inputs / state before continuing.
                continue
            try:
                t_first = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
                cid_int = int(cid)
            except Exception:
                # Recover from a failure case and return a safe default.
                continue
            perchunk[cid_int] = t_first
            firsts.append(t_first)
        firsts.sort()
        _NODE_FIRSTS_BY_CHUNK[r] = perchunk
        _NODE_FIRSTS_ALL[r] = firsts
        count += 1
    return count


def _node_events_list(rank):
    # Node events list.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return []
    try:
        r = int(rank)
    except (TypeError, ValueError):
        # Recover from a failure case and return a safe default.
        return []
    node_lc = getattr(VIZ, "nodeLifeCycle", [])
    if r < 0 or r >= len(node_lc):
        # Branch based on the current state / selection.
        return []
    first_by_chunk = {}
    for cid, arrivals in node_lc[r].items():
        # Iterate over the relevant items and accumulate results.
        if arrivals:
            # Branch based on the current state / selection.
            t_first = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
            first_by_chunk[int(cid)] = t_first
    by_time = {}
    for cid, t in first_by_chunk.items():
        # Iterate over the relevant items and accumulate results.
        by_time.setdefault(t, []).append(cid)
    return [{"time": float(t), "chunks": sorted(cids)} for t, cids in sorted(by_time.items())]

def _chunk_events_list(chunk_id):
    # Chunk events list.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return []
    try:
        cid = int(chunk_id)
    except (TypeError, ValueError):
        # Recover from a failure case and return a safe default.
        return []
    clc = getattr(VIZ, "chunkLifeCycle", [])
    if not (0 <= cid < len(clc)):
        # Validate inputs / state before continuing.
        return []
    first_by_node = {}
    for rank, arrivals in clc[cid].items():
        # Iterate over the relevant items and accumulate results.
        if arrivals:
            # Branch based on the current state / selection.
            t_first = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
            first_by_node[int(rank)] = t_first
    by_time = {}
    for node, t in first_by_node.items():
        # Iterate over the relevant items and accumulate results.
        by_time.setdefault(t, []).append(node)
    return [{"time": float(t), "nodes": sorted(nodes)} for t, nodes in sorted(by_time.items())]

def _nodes_with_chunk_by_time(chunk_id, t):
    # Nodes with chunk by time.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return set(), "No simulation loaded (set a .vis in Logs)."
    try:
        cid = int(chunk_id)
    except (TypeError, ValueError):
        # Recover from a failure case and return a safe default.
        return set(), "Enter a valid chunk id."
    if not (0 <= cid < len(VIZ.chunkLifeCycle)):
        # Validate inputs / state before continuing.
        return set(), f"Chunk {cid} out of range."
    have = set()
    for rank, arrivals in VIZ.chunkLifeCycle[cid].items():
        # Iterate over the relevant items and accumulate results.
        if arrivals and min(float(ts) for (ts, _msg) in arrivals) <= float(t):
            # Branch based on the current state / selection.
            have.add(int(rank))
    return have, f"OK: {len(have)} node(s) have chunk {cid} by t={t:.3f}."

def _nodes_with_chunk_in_segment(chunk_id, t0, t1):
    # Nodes with chunk in segment.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return set(), "No simulation loaded (set a .vis in Logs)."
    try:
        cid = int(chunk_id)
    except (TypeError, ValueError):
        # Recover from a failure case and return a safe default.
        return set(), "Enter a valid chunk id."
    if not (0 <= cid < len(VIZ.chunkLifeCycle)):
        # Validate inputs / state before continuing.
        return set(), f"Chunk {cid} out of range."
    have = set()
    for rank, arrivals in VIZ.chunkLifeCycle[cid].items():
        # Iterate over the relevant items and accumulate results.
        if not arrivals:
            # Validate inputs / state before continuing.
            continue
        t_first = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
        if float(t0) <= t_first <= float(t1):
            # Branch based on the current state / selection.
            have.add(int(rank))
    return have, f"OK: {len(have)} node(s) first-got chunk {cid} in [{t0:.3f},{t1:.3f}]."

def _chunks_on_node_in_segment(rank, t0, t1):
    # Chunks on node in segment.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return [], "No simulation loaded (set a .vis in Logs)."
    try:
        r = int(rank)
    except (TypeError, ValueError):
        # Recover from a failure case and return a safe default.
        return [], "Enter a valid node id."
    if r < 0 or r >= len(getattr(VIZ, "nodeLifeCycle", [])):
        # Branch based on the current state / selection.
        return [], "Rank out of range."
    have = []
    for chunk_id, arrivals in VIZ.nodeLifeCycle[r].items():
        # Iterate over the relevant items and accumulate results.
        if not arrivals:
            # Validate inputs / state before continuing.
            continue
        t_first = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
        if float(t0) <= t_first <= float(t1):
            # Branch based on the current state / selection.
            have.append(int(chunk_id))
    have.sort()
    return have, f"OK: node {r} has {len(have)} new chunk(s) in [{t0:.3f},{t1:.3f}]."

def _post_conditions_left(rank, t):
    # Post conditions left.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return 0
    r = int(rank)
    # Try several shapes VIZ may expose (fast paths first)
    for meth in ("post_conditions_left", "postConditionsLeft", "get_post_conditions_left", "post_conditions_left_at_time", "postConditionsLeftAtTime"):
        # Iterate over the relevant items and accumulate results.
        f = getattr(VIZ, meth, None)
        if callable(f):
            # Branch based on the current state / selection.
            try:
                return int(f(r, float(t))) if f.__code__.co_argcount >= 2 else int(f(r))
            except Exception:
                # Recover from a failure case and return a safe default.
                pass
    for attr in ("postConditionsLeftByNode", "nodePostConditionsLeft", "postConditionsLeft"):
        # Iterate over the relevant items and accumulate results.
        obj = getattr(VIZ, attr, None)
        if isinstance(obj, dict):
            # Branch based on the current state / selection.
            v = obj.get(r)
            if isinstance(v, (int, float)):
                # Branch based on the current state / selection.
                return int(v)
            if isinstance(v, (list, tuple)):
                # Branch based on the current state / selection.
                try:
                    best = None
                    for pair in v:
                        # Iterate over the relevant items and accumulate results.
                        if isinstance(pair, (list, tuple)) and len(pair) >= 2:
                            # Branch based on the current state / selection.
                            tt = float(pair[0]); vv = int(pair[1])
                            if tt <= float(t) and (best is None or tt > best[0]):
                                # Validate inputs / state before continuing.
                                best = (tt, vv)
                    if best is not None:
                        # Validate inputs / state before continuing.
                        return int(best[1])
                except Exception:
                    # Recover from a failure case and return a safe default.
                    pass
        if isinstance(obj, (list, tuple)):
            # Branch based on the current state / selection.
            try:
                return int(obj[r])
            except Exception:
                # Recover from a failure case and return a safe default.
                pass
    # Fallback: derive from chunk arrivals (slower but safe)
    try:
        cmax = int(getattr(VIZ, "chunkCount", 0))
        if cmax <= 0:
            # Branch based on the current state / selection.
            return 0
        lc = getattr(VIZ, "nodeLifeCycle", [])
        if r < 0 or r >= len(lc):
            # Branch based on the current state / selection.
            return 0
        got = 0
        for _cid, arrivals in lc[r].items():
            # Iterate over the relevant items and accumulate results.
            if arrivals:
                # Branch based on the current state / selection.
                t_first = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
                if t_first <= float(t):
                    # Branch based on the current state / selection.
                    got += 1
        return max(0, cmax - got)
    except Exception:
        # Recover from a failure case and return a safe default.
        return 0

def panel_param_coloring():
    """New dedicated panel for Parameter-based coloring."""
    return html.Div([
        html.H3("Log Parameters", style={"margin": "0 0 12px"}),
        html.Div(
            "Select a parameter from the imported log file.",
            style=LABEL_MUTED
        ),
        
        # 1. Parameter Selection
        dcc.Dropdown(
            id="param-select-dropdown",
            options=[],
            placeholder="Select a parameter...",
            clearable=True,
            style={"marginTop": "12px", "width": "100%"}
        ),

        # 2. Data ID Input (Hidden unless type='data')
        html.Div(id="param-data-input-container", style={"display": "none", "marginTop": "12px"}, children=[
            html.Label("Data ID (e.g. Chunk #)", style={"fontWeight": 600, "fontSize": "12px"}),
            dcc.Input(
                id="param-data-id",
                type="number",
                placeholder="0",
                min=0,
                step=1,
                style={"width": "100%", "marginTop": "4px"}
            ),
            html.Div("Enter the ID of the chunk to trace.", style=LABEL_MUTED | {"marginTop": "4px"})
        ]),
        
        html.Div(id="param-stats-info", style=LABEL_MUTED | {"marginTop": "8px"}),
        
        html.Hr(),
        html.Div("Note: Selecting a parameter here overrides standard coloring modes.", style=LABEL_MUTED),
    # Update the viewport pan/translation for the network graph.
    ])

# =========================
# Node & chunk filter helpers
# =========================
def _parse_num_spec(spec: str):
    """Accepts tokens like: 1, 3-7, 12 or range(0,10) / range(0,10,2) / 'for i in range(0,10,2)'."""
    # Parse num spec.
    if not spec:
        # Validate inputs / state before continuing.
        return []
    out = set()
    tokens = [t.strip() for t in spec.replace("\n", ",").replace(";", ",").split(",") if t.strip()]
    for tok in tokens:
        # Iterate over the relevant items and accumulate results.
        try_tok = tok
        if tok.startswith("for ") and "range(" in tok:
            # Branch based on the current state / selection.
            try_tok = tok[tok.index("range("):]
        if try_tok.startswith("range(") and try_tok.endswith(")"):
            # Branch based on the current state / selection.
            inner = try_tok[len("range("):-1]
            parts = [p.strip() for p in inner.split(",") if p.strip()]
            try:
                if len(parts) == 1:
                    # Branch based on the current state / selection.
                    stop = int(parts[0]); start, step = 0, 1
                elif len(parts) == 2:
                    # Alternative branch for a different condition.
                    start, stop = int(parts[0]), int(parts[1]); step = 1
                else:
                    start, stop, step = int(parts[0]), int(parts[1]), int(parts[2])
                for i in range(start, stop, step):
                    # Iterate over the relevant items and accumulate results.
                    out.add(int(i))
                continue
            except Exception:
                # Recover from a failure case and return a safe default.
                pass
        if "-" in tok:
            # Branch based on the current state / selection.
            a, b = tok.split("-", 1)
            try:
                a = int(a.strip()); b = int(b.strip())
                if a <= b:
                    # Branch based on the current state / selection.
                    for i in range(a, b + 1):
                        # Iterate over the relevant items and accumulate results.
                        out.add(i)
                else:
                    for i in range(b, a + 1):
                        # Iterate over the relevant items and accumulate results.
                        out.add(i)
                continue
            except Exception:
                # Recover from a failure case and return a safe default.
                pass
        try:
            out.add(int(tok))
        except Exception:
            # Recover from a failure case and return a safe default.
            pass
    return sorted(out)

# NEW: visible nodes helper (Node filter ∩ Isolate snapshot − Hidden)
def _visible_node_ids(all_elements, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes):
    # Visible node ids.
    base_nodes = set()
    for el in all_elements or []:
        # Iterate over the relevant items and accumulate results.
        d = el.get("data", {})
        if "id" in d:
            # Branch based on the current state / selection.
            try:
                base_nodes.add(int(d["id"]))
            except Exception:
                # Recover from a failure case and return a safe default.
                pass
    if node_filter_ids:
        # Branch based on the current state / selection.
        allowed = set(int(i) for i in node_filter_ids if str(i).isdigit())
    else:
        allowed = set(base_nodes)
    if isolate_mode and isolate_snapshot:
        # Branch based on the current state / selection.
        snap = set(int(i) for i in isolate_snapshot if str(i).isdigit())
        allowed &= snap
    hidden = set(int(i) for i in (hidden_nodes or []) if str(i).isdigit())
    allowed -= hidden
    return sorted(allowed)

# =========================
# Core components
# =========================
def button(id_, label):
    # Button.
    return html.Button(label, id=id_, n_clicks=0, style=BTN)

cy = cyto.Cytoscape(
    id="network-graph",
    layout={"name": "preset", "fit": False, "padding": 30},
    style={"width": "100%", "height": "100%"},
    elements=ELEMS,
    stylesheet=BASE_STYLESHEET,
    boxSelectionEnabled=True,
    minZoom=0.1, maxZoom=5.0, zoom=1, pan={"x": 0, "y": 0},
    zoomingEnabled=True, userZoomingEnabled=False, panningEnabled=True, userPanningEnabled=True,
)

@app.callback(
    Output("network-graph", "zoom", allow_duplicate=True),
    Output("zoom-label", "children", allow_duplicate=True),
    Input("zoom-in", "n_clicks"),
    Input("zoom-out", "n_clicks"),
    State("network-graph", "zoom"),
    State("network-graph", "minZoom"),
    State("network-graph", "maxZoom"),
    prevent_initial_call=True
)
def nudge_zoom(n_plus, n_minus, cur_zoom, zmin, zmax):
    # Adjust the graph zoom level based on the zoom-in / zoom-out controls.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    if not ctx.triggered:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    which = ctx.triggered[0]["prop_id"].split(".")[0]
    step = 0.10
    z = float(cur_zoom or 1.0)
    if which == "zoom-in":
        # Branch based on the current state / selection.
        z = min(z + step, float(zmax or 1.6))
    else:
        z = max(z - step, float(zmin or 0.6))
    return z, f"{int(round(z * 100))}%"

# =========================
# Panels
# =========================
def panel_session_save():
    """Panel strictly for SAVING sessions."""
    return html.Div([
        html.H3("Save Session", style={"margin": "0 0 12px"}),
        html.Div("Save current state to a JSON file.", style=LABEL_MUTED),
        
        html.Label("Path for saving:"),
        dcc.Input(id="session-path-input", type="text", value=SESSION_FILE, style={"width": "100%"}),
        
        html.Button("Save Session", id="save-session", n_clicks=0, style={"marginTop": "8px"}),
        html.Div(id="session-status", style=LABEL_MUTED | {"marginTop": "8px"}),
    # Update the viewport pan/translation for the network graph.
    ])

def panel_session_load():
    """Panel strictly for LOADING sessions."""
    return html.Div([
        html.H3("Load Session", style={"margin": "0 0 12px"}),
        html.Div("Restore state from a JSON file.", style=LABEL_MUTED),
        
        dcc.Upload(
            id="upload-session",
            children=html.Div(["Drag & Drop or ", html.A("Select .json")]),
            style={
                "width": "100%", "height": "48px", "lineHeight": "48px",
                "borderWidth": "1px", "borderStyle": "dashed", "borderRadius": "8px",
                "textAlign": "center", "marginBottom": "8px", "background": "#fafbff",
            },
            accept=".json",
        ),
        html.Label("Or path to file:"),
        # Note: We reuse the same ID 'session-path-input' for logic simplicity, 
        # or you can create a new ID 'session-path-input-load' and update the callback if you want them truly separate.
        # For now, let's reuse the input since the logic already binds to it.
        dcc.Input(id="session-path-input-load", type="text", value=SESSION_FILE, style={"width": "100%"}),
        
        html.Button("Load Session", id="load-session", n_clicks=0, style={"marginTop": "8px"}),
        # You might want a separate status div for loading
        html.Div(id="session-load-status", style=LABEL_MUTED | {"marginTop": "8px"}),
    # Update the viewport pan/translation for the network graph.
    ])

def panel_topology_file():
    """Panel strictly for LOADING TOPOLOGY files."""
    return html.Div([
        html.H3("Topology File", style={"margin": "0 0 12px"}),
        html.Div("Load a topology text file.", style=LABEL_MUTED),
        
        html.H4("Upload topology file", style={"margin": "8px 0 6px"}),
        dcc.Upload(
            id="upload-topology",
            children=html.Div(["Drag & Drop or ", html.A("Select topology file")]),
            style={
                "width": "100%", "height": "48px", "lineHeight": "48px",
                "borderWidth": "1px", "borderStyle": "dashed",
                "borderRadius": "8px", "textAlign": "center",
                "marginBottom": "8px", "background": "#fafbff",
            },
            accept=".txt,.topo,.dat,.json",
        ),
        html.H4("Path to topology text file", style={"margin": "8px 0 6px"}),
        dcc.Input(
            id="topology-path-input", type="text", value=TOPO_FILE, debounce=True, style={"width": "100%"},
        ),
        html.Button("Load topology", id="load-topology-btn", n_clicks=0, style={"marginTop": "8px"}),
        html.Div(id="topology-status", style=LABEL_MUTED | {"marginTop": "6px"}),
    # Update the viewport pan/translation for the network graph.
    ])



def panel_color():
    """Standard Links/Coloring panel (opened by Top Bar 'Links' button)."""
    return html.Div([
        html.Div(
            [
                html.Button(
                    "Filters",
                    id="btn-links-filters-shortcut",
                    n_clicks=0,
                    style={"fontSize": "11px", "padding": "2px 8px", "borderRadius": "8px", "border": "1px solid #e1e7ef", "background": "#f5f7fa", "cursor": "pointer"}
                ),
                html.Span("Go to Link Filters", style=LABEL_MUTED),
            ],
            style={"display": "flex", "justifyContent": "flex-end", "alignItems": "center", "marginBottom": "6px"},
        ),
        html.H3("Link Coloring", style={"margin": "0 0 12px"}),
        html.Div("Choose a standard coloring mode:", style=LABEL_MUTED),
        
        dcc.RadioItems(
            id="color-mode-radio",
            options=[
                {"label": "None", "value": "none"},
                {"label": "By capacity", "value": "capacity"},
                {"label": "By latency", "value": "latency"},
                {"label": "By avg link flow (segment)", "value": "flow"},
                {"label": "By avg flow / capacity (segment)", "value": "flow_frac"},
                # We keep 'parameter' as an option so the system can auto-switch to it, 
                # but we hide it from the UI list if possible, or leave it for visibility.
                {"label": "By Parameter", "value": "parameter", "disabled": True},
            ],
            value="none",
            inline=False,
            style={"marginTop": "8px"},
        ),
    # Update the viewport pan/translation for the network graph.
    ])

def panel_plots():
    return html.Div([
        html.H3("Plots", style={"margin": "0 0 12px"}),

        dcc.RadioItems(
            id="plot-visible-toggle",
            options=[
                {"label": "Topology", "value": "topology"},
                {"label": "Presence Grid", "value": "grid"},
                {"label": "Graph (Custom X/Y)", "value": "xy"},
            ],
            value="topology",
            inline=False,
            style={"marginBottom": "8px"}
        ),

        html.Div("Presence Grid uses X = Chunks, Y = Nodes; switches are hidden.", style=LABEL_MUTED),

        html.Hr(),
        html.H4("Custom X/Y"),
        
        # --- NEW: Toggle between Data (Chunks) and Link variables ---
        html.Div([
            html.Label("Metric Type:", style={"fontWeight": 600, "marginRight": "8px"}),
            dcc.RadioItems(
                id="xy-mode-toggle",
                options=[
                    {"label": " Chunk/Data Metrics", "value": "data"},
                    {"label": " Link/Network Metrics", "value": "link"},
                ],
                value="data",
                inline=True,
                style={"display": "inline-block", "fontSize": "13px"}
            )
        ], style={"marginBottom": "8px", "padding": "6px", "background": "#f1f5f9", "borderRadius": "6px"}),
        # ------------------------------------------------------------

        
        html.Div(
            "Pick X and Y axes. 'Link' mode calculates the SUM of the variable across all edges (Total).",
            style=LABEL_MUTED
        ),

        # --- Per-collective context (click name to open the Collective Page) ---
        html.Div(
            id="xy-collectives-param-box",
            style={
                "marginTop": "8px",
                "marginBottom": "8px",
                "padding": "8px",
                "border": "1px solid #e1e7ef",
                "borderRadius": "8px",
                "background": "#ffffff",
            },
            children=[
                html.Div(
                    "Active collectives (click a name to open Collective Page):",
                    style={"fontWeight": 600, "marginBottom": "6px", "fontSize": "12px"},
                ),
                html.Div(id="xy-collectives-param-box-rows"),
            ],
        ),
        # ---------------------------------------------------------------------

        html.Div([
            html.Div([
                html.Div("Y axis", style={"fontWeight": 600}),
                dcc.Dropdown(
                    id="xy-y-select", 
                    options=XY_OPTIONS, 
                    value="postleft_avg", 
                    clearable=False,
                    style={"minWidth": "200px"}
                ),
            ], style={"display": "flex", "flexDirection": "column", "gap": "6px"}),

            html.Div([
                html.Div("X axis", style={"fontWeight": 600}),
                dcc.Dropdown(
                    id="xy-x-select", 
                    options=XY_OPTIONS, 
                    value="time", 
                    clearable=False,
                    style={"minWidth": "200px"}
                ),
            ], style={"display": "flex", "flexDirection": "column", "gap": "6px"}),
        ], style={"display": "flex", "flexDirection": "column", "gap": "12px", "marginTop": "6px"}),html.Div(style={"height": "6px"}),

        html.Div([
            html.Button("Export XY → CSV", id="btn-xy-export-csv", n_clicks=0, style={"marginRight": "8px"}),
        ], style={"display": "flex", "alignItems": "center"}),

        dcc.Download(id="download-xy-data"),
        html.Div(id="xy-export-status", style=LABEL_MUTED | {"marginTop": "6px"}),
    ])

def subsection_links():
    return html.Div(id="filters-links-section", children=[
        html.H4("Edge Filters", style={"margin": "4px 0 8px"}),
        html.Label("Capacity range"),
        dcc.RangeSlider(
            id="cap-range", min=CAP_MIN, max=CAP_MAX,
            step=(CAP_MAX - CAP_MIN) / 100.0 if CAP_MAX > CAP_MIN else 1.0,
            value=[CAP_MIN, CAP_MAX], allowCross=False, marks=None,
            tooltip={"always_visible": False}, updatemode="mouseup",
        ),
        html.Div(style={"height": "8px"}),
        html.Label("Edge types"),
        dcc.Checklist(
            id="edge-types",
            options=[
                {"label": "node→node", "value": "etype-host-host"},
                {"label": "switch→switch","value": "etype-switch-switch"},
                {"label": "node→switch", "value": "etype-host-switch"},
            ],
            value=["etype-host-host", "etype-switch-switch", "etype-host-switch"],
            inline=True,
        ),
    # Subsection links.
    ])


def panel_node():
    # Node panel: Inspector + Node Coloring only (no filters/hide here)
    return html.Div([
        html.Div(
            [
                html.Button(
                    "Filters",
                    id="btn-node-filters-shortcut",
                    n_clicks=0,
                    style={"fontSize": "11px", "padding": "2px 8px", "borderRadius": "8px", "border": "1px solid #e1e7ef", "background": "#f5f7fa", "cursor": "pointer"}
                ),
                html.Span("Go to Node Filters", style=LABEL_MUTED),
            ],
            style={"display": "flex", "justifyContent": "flex-end", "alignItems": "center", "marginBottom": "6px"},
        ),
        html.H3("Nodes", style={"margin": "0 0 12px"}),

        html.H4("Inspect a single node", style={"margin":"8px 0 6px"}),
        html.Div("Type a node (rank). Lists chunks whose first-arrival is within the current segment (also obeys chunk filter).", style=LABEL_MUTED),
        html.Div([
            dcc.Input(id="node-id", type="number", placeholder="node (rank)", min=0, step=1, style={"width": "140px", "marginRight": "12px"}),
        ], style={"marginTop": "8px", "display": "flex", "gap": "12px", "alignItems": "center"}),
        dcc.Store(id="node-contents"),
        html.Div(id="node-status", style=LABEL_MUTED | {"marginTop": "6px"}),
        html.Div(id="node-chunk-list",
                 style={"maxHeight": "140px","overflowY": "auto","border": "1px solid #eee", "borderRadius": "6px",
                        "padding": "6px","marginTop": "6px","fontSize": "12px"}),
        html.Div("Arrival timeline within segment:", style=LABEL_MUTED | {"marginTop": "8px"}),
        dcc.Store(id="node-events"),
        html.Div(id="node-timeline",
                 style={"maxHeight": "220px","overflowY": "auto","border": "1px solid #eee", "borderRadius": "6px",
                        "padding": "6px","marginTop": "6px", "fontSize": "12px", "lineHeight": "1.35","background": "white"}),

        html.Hr(),

        html.H4("Node Coloring (thresholds)", style={"margin":"8px 0 8px"}),
        html.Div([
            dcc.Input(id="chunk-count-threshold", type="number", placeholder="min chunks by t_end", min=0, step=1, style={"width":"200px","marginRight":"8px"}),
            html.Button("Color nodes by chunks ≥", id="btn-color-chunk-thresh", n_clicks=0, style={"marginRight":"12px"}),
            dcc.Input(id="postleft-threshold", type="number", placeholder="min post-left by t_end", min=0, step=1, style={"width":"220px","marginRight":"8px"}),
            html.Button("Color nodes by post-left ≥", id="btn-color-postleft-thresh", n_clicks=0, style={"marginRight":"12px"}),
            html.Button("Clear highlights", id="btn-clear-highlights", n_clicks=0),
        ], style={"display":"flex","flexWrap":"wrap","gap":"8px","alignItems":"center"}),
        html.Div(id="node-ops-status", style=LABEL_MUTED | {"marginTop": "8px"}),
    # Update the viewport pan/translation for the network graph.
    ])



def subsection_node_filters():
    # Node Filters ONLY: hide/clear + id/range filters + groups (no inspector, no coloring here)
    return html.Div(id="filters-nodes-section", children=[
        html.H4("Node Operations (visibility)", style={"margin":"4px 0 8px"}),
        html.Button("Isolate selected nodes (toggle)", id="isolate-btn", n_clicks=0, style={"marginRight":"8px"}),
        html.Button("Hide selected", id="hide-selected-btn", n_clicks=0, style={"marginRight":"8px"}),
        html.Button("Clear", id="clear-view-btn", n_clicks=0),
        html.Div(id="hidden-status", style=LABEL_MUTED | {"marginTop":"6px"}),

        html.Hr(),

        html.H4("Node Filters", style={"margin":"4px 0 8px"}),
        html.Div("Enter nodes or ranges (e.g. 1, 3-7, 12) or Python-style range: range(0,10,2) or 'for i in range(...)'", style=LABEL_MUTED),
        dcc.Textarea(id="node-filter-text",
                     placeholder="1, 3-7, 12 or range(0,10) or for i in range(0,10,2)",
                     style={"width":"100%","height":"68px","marginTop":"6px"}),
        html.Div(style={"height":"8px"}),
        html.Div([
            html.Div([
                html.Div("Range Builder", style={"fontWeight":600, "marginBottom":"4px"}),
                html.Div([
                    dcc.Input(id="range-start", type="number", placeholder="start", style={"width":"90px","marginRight":"6px"}),
                    dcc.Input(id="range-end", type="number", placeholder="end", style={"width":"90px","marginRight":"6px"}),
                    dcc.Input(id="range-step", type="number", placeholder="step", value=1, style={"width":"90px","marginRight":"6px"}),
                    html.Button("Add range", id="add-range-btn", n_clicks=0)
                ])
            ], style={"flex":"1"}),
        ], style={"display":"flex","gap":"12px","alignItems":"flex-end"}),
        html.Div(style={"height":"8px"}),
        html.Div([
            dcc.Input(id="node-post-left-min", type="number", placeholder="min post-conditions left", min=0, step=1, style={"width":"220px","marginRight":"8px"}),
            html.Button("Apply node filter", id="apply-node-filter", n_clicks=0, style={"marginRight":"8px"}),
            html.Button("Clear node filter", id="clear-node-filter", n_clicks=0),
        ]),
        html.Div(id="node-filter-status", style=LABEL_MUTED | {"marginTop": "8px"}),

        html.Hr(),

        html.H4("Node Groups", style={"margin":"8px 0 6px"}),
        html.Div("Save your selections/specs as named groups and reuse later.", style=LABEL_MUTED),
        html.Div([
            dcc.Input(id="group-name-input", type="text", placeholder="group name (e.g. rack-0-15)", style={"flex":"1"}),
            html.Button("Save (from text/range or current filter)", id="group-save-btn", n_clicks=0, style={"marginLeft":"8px"}),
        ], style={"display":"flex","gap":"8px","alignItems":"center","marginTop":"6px"}),
        html.Div([
            html.Button("Save from selection", id="group-save-from-selection-btn", n_clicks=0, style={"marginRight":"8px"}),
            html.Button("Refresh", id="groups-refresh", n_clicks=0, style={"marginRight":"8px"}),
            dcc.Dropdown(id="group-select", options=[], placeholder="choose a group", style={"flex":"1"}),
            html.Button("Load → filter", id="group-load-btn", n_clicks=0, style={"marginLeft":"8px"}),
            html.Button("Delete", id="group-delete-btn", n_clicks=0, style={"marginLeft":"8px"}),
        ], style={"display":"flex","gap":"8px","alignItems":"center","marginTop":"8px"}),
        html.Div(id="group-selected-name", style={"marginTop":"6px","fontWeight":700}),
        html.Div(id="groups-status", style=LABEL_MUTED | {"marginTop":"4px"}),
    # Apply the current filter settings and compute the resulting subset for display.
    ])


def subsection_chunk_presence():
    # Data / Chunks: chunk-level operations on the currently loaded log (no filters here)
    return html.Div(
        id="data-chunks-section",
        children=[
            html.H3("Data / Chunks", style={"margin": "0 0 6px"}),
            html.Div(
                "Chunk-level operations on the currently loaded log.",
                style=LABEL_MUTED
            ),
            html.H4("Chunk Presence / Navigation", style={"margin": "12px 0 8px"}),
            html.Div(
                "Pick a chunk; nodes that FIRST got it will light up; stepping moves within the current segment. "
                "The segment will glow (grid ignores start).",
                style=LABEL_MUTED
            ),
            html.Div(
                [
                    dcc.Input(
                        id="chunk-id",
                        type="number",
                        placeholder="chunk id",
                        min=0,
                        step=1,
                        style={"width": "120px", "marginRight": "12px"},
                    ),
                    html.Button(
                        "Prev arrival",
                        id="chunk-prev",
                        n_clicks=0,
                        style={"marginRight": "8px"},
                    ),
                    html.Button("Next arrival", id="chunk-next", n_clicks=0),
                ],
                style={
                    "marginTop": "8px",
                    "display": "flex",
                    "gap": "12px",
                    "alignItems": "center",
                },
            ),
            dcc.Store(id="chunk-presence"),
            dcc.Store(id="chunk-events"),
            html.Div(id="chunk-status", style=LABEL_MUTED | {"marginTop": "6px"}),
            html.Div(
                id="chunk-event-info",
                style=LABEL_MUTED | {"marginTop": "6px"},
            ),
        ],
    # Subsection chunk presence.
    )


def subsection_chunks():
    # Filters panel: Chunk filters only (no presence/navigation here)
    return html.Div(
        id="filters-chunks-section",
        children=[
            html.H4("Chunk Filters", style={"margin": "4px 0 8px"}),
            html.Div(
                "Enter chunks or ranges (e.g. 2, 5-12) or Python-style range",
                style=LABEL_MUTED,
            ),
            dcc.Textarea(
                id="chunk-filter-text",
                placeholder="...,4)",
                style={"width": "100%", "height": "60px", "marginTop": "6px"},
            ),
            html.Div(style={"height": "8px"}),
            html.Div(
                [
                    dcc.Input(
                        id="chunk-range-start",
                        type="number",
                        placeholder="start",
                        style={"width": "90px", "marginRight": "6px"},
                    ),
                    dcc.Input(
                        id="chunk-range-end",
                        type="number",
                        placeholder="end",
                        style={"width": "90px", "marginRight": "6px"},
                    ),
                    dcc.Input(
                        id="chunk-range-step",
                        type="number",
                        placeholder="step",
                        value=1,
                        style={"width": "90px", "marginRight": "6px"},
                    ),
                    html.Button(
                        "Add range",
                        id="chunk-add-range-btn",
                        n_clicks=0,
                    ),
                ],
                style={"display": "flex", "alignItems": "center"},
            ),
            html.Div(style={"height": "8px"}),
            html.Div(
                [
                    dcc.Input(
                        id="chunk-min-nodes",
                        type="number",
                        placeholder="min nodes who saw chunk",
                        min=0,
                        step=1,
                        style={"width": "220px", "marginRight": "8px"},
                    ),
                    html.Button(
                        "Apply chunk filter",
                        id="apply-chunk-filter",
                        n_clicks=0,
                        style={"marginRight": "8px"},
                    ),
                    html.Button(
                        "Clear",
                        id="clear-chunk-filter",
                        n_clicks=0,
                    ),
                ]
            ),
            html.Div(
                id="chunk-filter-status",
                style=LABEL_MUTED | {"marginTop": "6px"},
            ),
        ],
    # Subsection chunks.
    )
def subnav_filters():
    # Sub-navigation for Filters panel: three small buttons to switch sub-sections.
    btn_style = {"border":"1px solid #e1e7ef","background":"#f5f7fa","borderRadius":"8px",
    # Apply the current filter settings and compute the resulting subset for display.
                 "padding":"6px 10px","fontWeight":600,"cursor":"pointer","fontSize":"12px"}
    return html.Div(
        id="subnav-filters",
        style={"display":"flex","gap":"8px","alignItems":"center","marginBottom":"8px"},
        children=[
            html.Button("Links",  id="filters-sub-links",  n_clicks=0, style=btn_style),
            html.Button("Nodes",  id="filters-sub-nodes",  n_clicks=0, style=btn_style),
            html.Button("Chunks", id="filters-sub-chunks", n_clicks=0, style=btn_style),
        ]
    )

def panel_filters():
    return html.Div([
        subnav_filters(),
        html.Div(
            [
                html.Button(
                    "Clear all filters",
                    id="clear-all-filters",
                    n_clicks=0,
                    style={"fontSize": "11px", "padding": "2px 8px", "borderRadius": "8px", "border": "1px solid #e1e7ef", "background": "#f5f7fa", "cursor": "pointer"}
                ),
            ],
            style={"display": "flex", "justifyContent": "flex-end", "marginBottom": "6px"},
        ),
        dcc.Store(id="filters-submode", data="links"),
        subsection_links(),
        subsection_node_filters(),
        subsection_chunks(),
    # Update the viewport pan/translation for the network graph.
    ])

def panel_save():
    return html.Div([
        html.H3("Save / Load Session", style={"margin": "0 0 12px"}),
        html.Div(
            "Save everything: node positions, zoom/pan, layout, filters, hidden nodes, active panel, chunk/node ids.",
            style=LABEL_MUTED,
        ),

        html.H4("Upload session JSON", style={"margin": "12px 0 6px"}),
        dcc.Upload(
            id="upload-session",
            children=html.Div(["Drag & Drop or ", html.A("Select .json")]),
            style={
                "width": "100%",
                "height": "48px",
                "lineHeight": "48px",
                "borderWidth": "1px",
                "borderStyle": "dashed",
                "borderRadius": "8px",
                "textAlign": "center",
                "marginBottom": "8px",
                "background": "#fafbff",
            },
            accept=".json",
        ),

        html.Label("Path to session JSON"),
        dcc.Input(
            id="session-path-input",
            type="text",
            value=SESSION_FILE,
            debounce=True,
            style={"width": "100%"},
        ),
        html.Div(
            "Tip: share this file; loading it fully restores the session.",
            style=LABEL_MUTED | {"marginTop": "6px"},
        ),
        html.Div(style={"height": "8px"}),
        html.Div([
            html.Button("Save session", id="save-session", n_clicks=0, style={"marginRight": "8px"}),
            html.Button("Load session", id="load-session", n_clicks=0),
        ]),
        html.Div(id="session-status", style=LABEL_MUTED | {"marginTop": "8px"}),
    # Update the viewport pan/translation for the network graph.
    ])



def panel_chunk():
    return html.Div([
        html.Div(
            [
                html.Button(
                    "Filters",
                    id="btn-chunks-filters-shortcut",
                    n_clicks=0,
                    style={"fontSize": "11px", "padding": "2px 8px", "borderRadius": "8px", "border": "1px solid #e1e7ef", "background": "#f5f7fa", "cursor": "pointer"}
                ),
                html.Span("Go to Chunk Filters", style=LABEL_MUTED),
            ],
            style={"display": "flex", "justifyContent": "flex-end", "alignItems": "center", "marginBottom": "6px"},
        ),
        subsection_chunk_presence(),
    # Update the viewport pan/translation for the network graph.
    ])

def panel_collective_details():
    """Panel for editing a collective (rename + active parameter selection)."""
    return html.Div([
        html.H3("Collective Page", style={"margin": "0 0 12px"}),
        html.Div(id="coll-details-header", style=LABEL_MUTED | {"marginBottom": "12px"}),

        # Rename Section
        html.H4("Rename", style={"margin": "8px 0 6px"}),
        html.Div([
            dcc.Input(id="coll-rename-input", type="text", placeholder="Enter new name", style={"flex": "1"}),
            html.Button("Save Name", id="coll-rename-btn", n_clicks=0, style={"marginLeft": "8px"}),
        ], style={"display": "flex", "alignItems": "center"}),

        html.Hr(),

        # Flow parameters (link vars)
        html.H4("Flow Parameters", style={"margin": "8px 0 6px"}),
        html.Div(
            "Choose exactly one flow (link) parameter to expose from this collective.",
            style=LABEL_MUTED
        ),
        html.Div(
            id="coll-flow-params-container",
            style={
                "marginTop": "8px",
                "border": "1px solid #e1e7ef",
                "borderRadius": "6px",
                "padding": "8px",
                "maxHeight": "220px",
                "overflowY": "auto",
                "backgroundColor": "#f9f9f9",
                "fontSize": "12px"
            },
            children=[]
        ),

        html.Hr(),

        # Chunk/data parameters (data vars)
        html.H4("Chunk (Data) Parameters", style={"margin": "8px 0 6px"}),
        html.Div(
            "Choose exactly one chunk (data) parameter to expose from this collective.",
            style=LABEL_MUTED
        ),
        html.Div(
            id="coll-data-params-container",
            style={
                "marginTop": "8px",
                "border": "1px solid #e1e7ef",
                "borderRadius": "6px",
                "padding": "8px",
                "maxHeight": "220px",
                "overflowY": "auto",
                "backgroundColor": "#f9f9f9",
                "fontSize": "12px"
            },
            children=[]
        ),

    ])

def panel_logs():
    return html.Div([
        html.Hr(),
        html.H3("Logs", style={"margin": "0 0 12px"}),
        html.Div("Load a simulation log (.vis or .json). Upload or set a path, then click Load Log.", style=LABEL_MUTED),
        html.H4("Upload .vis or .json", style={"margin": "12px 0 6px"}),
        dcc.Upload(
            id="upload-log",
            children=html.Div(["Drag & Drop or ", html.A("Select .vis/.json")]),
            style={
                "width": "100%", "height": "48px", "lineHeight": "48px", "borderWidth": "1px", "borderStyle": "dashed",
                "borderRadius": "8px", "textAlign": "center", "marginBottom": "8px", "background": "#fafbff"
            },
            accept=".vis,.json"
        ),
        html.H4("Path to .vis or .json", style={"margin": "8px 0 6px"}),
        dcc.Input(id="log-path-input", type="text", value=LOG_FILE, debounce=True, style={"width": "100%"}),
        html.Div(style={"height": "8px"}),
        html.Button("Load Log", id="load-log-btn", n_clicks=0),
        html.Div(id="data-status", style=LABEL_MUTED | {"marginTop": "8px"}),

        html.Hr(),
        html.Div("Loaded logs now appear in the 'Topologies & Logs' tree on the left panel.", style=LABEL_MUTED | {"fontStyle": "italic"}),
        
        # We REMOVED dcc.Checklist(id="multi-logs-include") from here
        # We also removed the remove/clear buttons since management is now done via the tree.
    # Update the viewport pan/translation for the network graph.
    ])

# =========================
# Layout
# =========================
app.layout = html.Div(
    style=LAYOUT_STYLE,
    children=[
        # Top bar
        html.Div(
            style=TOPBAR_STYLE,
            className="menubar",  # optional, works with menubar.css
            children=[
                # LEFT: File menu + all buttons
                html.Div(
                    style=TOPBAR_BTNS_STYLE,
                    children=[
                        # --- File menu (pure CSS hover) ---
                        html.Div(
                            className="menu",
                            children=[
                                html.Button(
                                    "File",
                                    className="menu__btn",
                                    type="button",
                                    style=BTN,  # <-- makes it look like your other buttons
                                ),

                                html.Div(
                                    className="menu__content",
                                    children=[
                                        html.Button(
                                            "Save session",
                                            id="menu-save",
                                            className="menu__item",
                                        ),
                                        html.Button(
                                            "Load session",
                                            id="menu-load",
                                            className="menu__item",
                                        ),
                                        html.Button(
                                            "New…",
                                            id="menu-new",
                                            className="menu__item",
                                        ),
                                        html.Button("Topology file…", id="menu-topology-file", className="menu__item"),
                                        html.Div(className="menu__sep"),
                                    ],
                                ),

                            ],
                        ),
                        # --- end File menu ---

                        # other top buttons
                        button("btn-plots", "Plots"),
                        button("btn-filters", "Filters"),
                        button("btn-color", "Links"),
                        button("btn-node", "Nodes"),
                        button("btn-chunks", "Chunk"),
                    ],
                ),

                # RIGHT: title
                html.Div(
                    [
                        html.Span(
                            "Topology Visualizer",
                            style={
                                "fontWeight": 800,
                                "fontSize": "20px",
                                "paddingLeft": "4px",
                            },
                        )
                    ]
                ),
            ],
        ),

    # Floating selection details popup (bottom-right)
        html.Div(
            id="current-selection-modal",
            style={
                "display": "none",
                "position": "fixed",
                "right": "24px",
                "bottom": "90px",
                "width": "320px",
                "maxHeight": "40vh",
                "overflowY": "auto",
                "background": "#ffffff",
                "border": "1px solid #e1e7ef",
                "borderRadius": "10px",
                "boxShadow": "0 4px 12px rgba(15,23,42,0.25)",
                "padding": "10px 12px",
                "zIndex": 20,
            },
            children=[
                html.Div(
                    [
                        html.Span("Current selection", style={"fontWeight": 600}),
                        html.Button(
                            "✕",
                            id="current-selection-close",
                            n_clicks=0,
                            style={
                                "border": "none",
                                "background": "transparent",
                                "cursor": "pointer",
                                "fontSize": "14px",
                            },
                        ),
                    ],
                    style={
                        "display": "flex",
                        "justifyContent": "space-between",
                        "alignItems": "center",
                    },
                ),
                html.Hr(style={"margin": "8px 0"}),
                html.Div(id="current-selection-details", style={"fontSize": "12px"}),
            ],
        ),

        # "New session" confirmation modal
        html.Div(
            id="new-session-modal",
            style={
                "display": "none",
                "position": "fixed",
                "top": 0,
                "left": 0,
                "right": 0,
                "bottom": 0,
                "background": "rgba(15,23,42,0.55)",
                "zIndex": 10000,
                "alignItems": "center",
                "justifyContent": "center",
            },
            children=[
                html.Div(
                    style={
                        "background": "#ffffff",
                        "borderRadius": "10px",
                        "padding": "18px 20px",
                        "minWidth": "320px",
                        "maxWidth": "420px",
                        "boxShadow": "0 4px 16px rgba(15,23,42,0.35)",
                        "fontSize": "14px",
                    },
                    children=[
                        html.H4(
                            "Start new session?",
                            style={"marginTop": 0, "marginBottom": "8px"},
                        ),
                        html.P(
                            "This will clear the current topology and view and return to an empty canvas. "
                            "Unsaved changes will be lost.",
                            style={"marginBottom": "14px"},
                        ),
                        html.Div(
                            style={
                                "display": "flex",
                                "justifyContent": "flex-end",
                                "gap": "8px",
                            },
                            children=[
                                html.Button(
                                    "Cancel",
                                    id="new-session-cancel",
                                    n_clicks=0,
                                    style={"padding": "4px 10px"},
                                ),
                                html.Button(
                                    "Yes, start new",
                                    id="new-session-confirm",
                                    n_clicks=0,
                                    style=BTN | {"padding": "4px 10px"},
                                ),
                            ],
                        ),
                    ],
                ),
            ],
        ),

        # Main grid (left rail + center + right)
        html.Div(
            id="main-grid",
            style=MAIN_GRID,
            children=[
                # Left rail (now visually empty, only stores + close button)
                html.Div(
                    style=LEFT_CARD,
                    children=[
                        dcc.Store(id="active-panel", data="filters"),
                        dcc.Store(id="avail-params", data=[]),    # Stores list of parameters found in the log
                        dcc.Store(id="param-values", data={}),    # Stores calculated values for coloring
                        dcc.Store(id="param-filter-store", data=None),  # Stores {name, min, max} for filtering

                        dcc.Store(id="editing-collective-id", data=None),
                        dcc.Store(id="topo-states", data={}),
                        dcc.Store(id="file-path", data=PRESET_FILE),
                        dcc.Store(id="session-file-path", data=SESSION_FILE),
                        dcc.Store(id="editing-topology-id", data=None),

                        # Tracks which collective is currently waiting for a log upload
                        dcc.Store(id="target-collective-id", data=None),
                        # Tracks the active collectives (IDs) for each topology
                        dcc.Store(id="active-collectives-map", data={}),

                        dcc.Store(id="saved-layout", data=None),
                        dcc.Store(id="layout-has-positions", data=False),

                        # time bounds + slider step
                        dcc.Store(id="time-min", data=TIME_MIN),
                        dcc.Store(id="time-max", data=TIME_MAX),
                        dcc.Store(id="slider-step", data=SLIDER_STEP),

                        # throughput/load derived data
                        dcc.Store(id="store-sends", data=[]),                 # list[ {t_start, t_end, chunk?, src?, dst?} ]
                        dcc.Store(id="store-chunk-finish-times", data={}),    # { chunk_id: t_finish }
                        dcc.Store(id="store-chunk-start-times", data={}),     # { chunk_id: t_start (first seen anywhere) }

                        # elements base (topology)
                        dcc.Store(id="elements-base", data=ELEMS),

                        # filtering/isolation/hidden state
                        dcc.Store(id="isolate-snapshot", data=None),
                        dcc.Store(id="isolate-mode", data=False),
                        dcc.Store(id="hidden-nodes", data=[]),

                        dcc.Store(id="color-mode", data="none"),
                        dcc.Store(id="selected-nodes", data=[]),

                        # NEW: currently selected node/link + popup state
                        dcc.Store(id="current-selection", data=None),
                        dcc.Store(id="current-selection-open", data=False),

                        dcc.Store(id="node-filter-ids", data=[]),

                        # chunk filtering
                        dcc.Store(id="chunk-filter-ids", data=[]),

                        # plots
                        dcc.Store(id="plot-visible", data=False),     # Presence grid
                        dcc.Store(id="postleft-visible", data=False), # Post-conditions chart
                        dcc.Store(id="wip-visible", data=False),
                        dcc.Store(id="cum-visible", data=False),
                        dcc.Store(id="avg-visible", data=False),
                        dcc.Store(id="xy-visible", data=False),
                        dcc.Store(id="postleft-matrix-visible", data=False),
                        # Per-topology logs: topo_id -> [log_bundle, ...]
                        dcc.Store(id="topo-logs", data={}),
                        dcc.Store(id="multi-topos", data=[]),
                        # Multi .vis support (XY overlay only)
                        dcc.Store(id="multi-logs", data=[]),
                        # node highlight (threshold) stores
                        dcc.Store(id="highlight-chunk-nodes", data=[]),
                        dcc.Store(id="highlight-postleft-nodes", data=[]),

                        # NEW: chunk → link highlight store
                        dcc.Store(id="highlight-chunk-links", data=[]),

                        # time segment
                        dcc.Store(id="segment-start", data=TIME_MIN),
                        dcc.Store(id="segment-end", data=TIME_MAX),
                        dcc.Store(id="lock-window", data=False),

                        # NEW: guard to suppress snapping on programmatic changes
                        dcc.Store(id="suppress-snap", data=False),

                        # NEW: left/right panel open state
                        dcc.Store(id="left-panel-open", data=True),
                        dcc.Store(id="right-panel-open", data=True),

                        # Right-panel navigation history (for the Back button)
                        dcc.Store(id="right-panel-history", data={"stack": [], "current": "filters"}),

                        visdcc.Run_js(id="runjs"),

                        # ... inside the children=[ ... ] of LEFT_CARD ...

                        # ... inside the children list of the LEFT_CARD Div ...

                        html.Div(
                            id="topology-list-panel",
                            style={"flex": "1", "overflowY": "auto", "marginTop": "10px"},
                            children=[
                                html.H4("Topologies & Logs", style={"marginBottom": "8px"}),
                                html.Div(
                                    "Click a topology name to make it Active (for loading). Check logs to include them in plots.",
                                    style=LABEL_MUTED
                                ),

                                # The new container for your Topology Tree
                                html.Div(id="topology-groups-container", style={"marginTop": "10px"}),

                                # --- HIDDEN CONTROLS ---
                                html.Div(
                                    style={"display": "none"},
                                    children=[
                                        # The main radio that determines which topology file is processed
                                        dcc.RadioItems(id="topology-radio", options=[], value=None),
                                        
                                        # CHANGED: Use Store instead of Checklist so it doesn't auto-prune values
                                        dcc.Store(id="multi-logs-include", data=[]), 
                                    ]
                                ),
                            ],
                        ),


                    ],
                ),

                # Floating left/right panel toggles (always visible)
                html.Button(
                    "✕",
                    id="toggle-left-panel",
                    n_clicks=0,
                    title="Show/hide left panel",
                    style={
                        "position": "fixed",
                        "left": "4px",
                        "top": "10%",
                        "transform": "translateY(-50%)",
                        "zIndex": 50,
                        "borderRadius": "0 8px 8px 0",
                        "border": "1px solid #e1e7ef",
                        "background": "#ffffff",
                        "cursor": "pointer",
                        "fontSize": "14px",
                        "padding": "4px 6px",
                    },
                ),
                html.Button(
                    "✕",
                    id="toggle-right-panel",
                    n_clicks=0,
                    title="Show/hide right panel",
                    style={
                        "position": "fixed",
                        "right": "4px",
                        "top": "10%",
                        "transform": "translateY(-50%)",
                        "zIndex": 50,
                        "borderRadius": "8px 0 0 8px",
                        "border": "1px solid #e1e7ef",
                        "background": "#ffffff",
                        "cursor": "pointer",
                        "fontSize": "14px",
                        "padding": "4px 6px",
                    },
                ),

                html.Button(
                    "↩",
                    id="right-panel-back",
                    n_clicks=0,
                    title="Back",
                    style={
                        "position": "fixed",
                        "right": "4px",
                        "top": "calc(10% + 34px)",
                        "transform": "translateY(-50%)",
                        "zIndex": 50,
                        "borderRadius": "8px 0 0 8px",
                        "border": "1px solid #e1e7ef",
                        "background": "#ffffff",
                        "cursor": "pointer",
                        "fontSize": "14px",
                        "padding": "4px 6px",
                    },
                ),


                # Center: Graph/Grid/PostLeft + Time segment controls
                html.Div(
                    style=CENTER_CARD,
                    children=[
                        html.Div(
                            id="center-stack",
                            style={"position": "relative"},
                            children=[
                                html.Div(
                                    id="graph-pane",
                                    style={"position": "absolute", "inset": "0", "display": "block"},
                                    children=[
                                    cy,                                   
                                    html.Div(
                                        id="empty-state-msg",
                                        children="Go to File and load a topology",
                                        style={
                                            "position": "absolute", 
                                            "top": "50%", 
                                            "left": "50%",
                                            "transform": "translate(-50%, -50%)",
                                            "fontSize": "22px", 
                                            "color": "#94a3b8", # Subtle gray
                                            "fontWeight": "600",
                                            "textAlign": "center", 
                                            "pointerEvents": "none", # Allows clicking through to the graph if needed
                                            "zIndex": 0,
                                            "width": "100%"
                                        }
                                    )],
                                ),
                                html.Div(
                                    id="grid-pane",
                                    style={"position": "absolute", "inset": "0", "display": "none"},
                                    children=[
                                        dcc.Graph(
                                            id="presence-grid", figure=go.Figure(),
                                            style={"width": "100%", "height": "100%"},
                                            config={"displaylogo": False, "responsive": True},
                                        )
                                    ],
                                ),
                                html.Div(
                                    id="postleft-pane",
                                    style={"position": "absolute", "inset": "0", "display": "none"},
                                    children=[
                                        dcc.Graph(
                                            id="postleft-chart", figure=go.Figure(),
                                            style={"width": "100%", "height": "100%"},
                                            config={"displaylogo": False, "responsive": True},
                                        )
                                    ],
                                ),

                                html.Div(
                                    id="wip-pane",
                                    style={"position": "absolute", "inset": "0", "display": "none"},
                                    children=[
                                        dcc.Graph(
                                            id="wip-over-time", figure=go.Figure(),
                                            style={"width": "100%", "height": "100%"},
                                            config={"displaylogo": False, "responsive": True},
                                        )
                                    ],
                                ),
                                html.Div(
                                    id="cum-pane",
                                    style={"position": "absolute", "inset": "0", "display": "none"},
                                    children=[
                                        dcc.Graph(
                                            id="cum-finished-over-time", figure=go.Figure(),
                                            style={"width": "100%", "height": "100%"},
                                            config={"displaylogo": False, "responsive": True},
                                        )
                                    ],
                                ),
                                html.Div(
                                    id="avg-pane",
                                    style={"position": "absolute", "inset": "0", "display": "none"},
                                    children=[
                                        dcc.Graph(
                                            id="avg-send-duration-over-time", figure=go.Figure(),
                                            style={"width": "100%", "height": "100%"},
                                            config={"displaylogo": False, "responsive": True},
                                        )
                                    ],
                                ),

                                html.Div(
                                    id="xy-pane",
                                    style={"position": "absolute", "inset": "0", "display": "none"},
                                    children=[
                                        dcc.Graph(
                                            id="xy-plot", figure=go.Figure(),
                                            style={"width": "100%", "height": "100%"},
                                            config={"displaylogo": False, "responsive": True},
                                        )
                                    ],
                                ),
                                html.Div(
                                    id="postleft-matrix-pane",
                                    style={"position": "absolute", "inset": "0", "display": "none"},
                                    children=[
                                        dcc.Graph(
                                            id="postleft-matrix", figure=go.Figure(),
                                            style={"width": "100%", "height": "100%"},
                                            config={"displaylogo": False, "responsive": True},
                                        )
                                    ],
                                ),

                                # floating zoom overlay
                                html.Div(
                                    [
                                        html.Button("＋", id="zoom-in", n_clicks=0, style={
                                            "width":"32px","height":"32px","padding":"0","lineHeight":"1",
                                            "border":"1px solid #e1e7ef","borderRadius":"8px","background":"#fff",
                                            "fontWeight":700,"cursor":"pointer"
                                        }),
                                        html.Div(id="zoom-label", children="100%", style={
                                            "fontSize":"12px","fontWeight":600,"padding":"2px 0",
                                            "minWidth":"40px","textAlign":"center"
                                        }),
                                        html.Button("−", id="zoom-out", n_clicks=0, style={
                                            "width":"32px","height":"32px","padding":"0","lineHeight":"1",
                                            "border":"1px solid #e1e7ef","borderRadius":"8px","background":"#fff",
                                            "fontWeight":700,"cursor":"pointer"
                                        }),
                                    ],
                                    style={
                                        "position": "absolute", "right": "12px", "bottom": "196px",
                                        "display": "flex","flexDirection": "column","alignItems": "center","gap": "6px",
                                        "padding": "6px","background": "rgba(255,255,255,0.9)",
                                        "border": "1px solid #e1e7ef","borderRadius": "10px",
                                        "boxShadow": "0 2px 8px rgba(0,0,0,0.06)",
                                        "zIndex": 5,
                                    },
                                ),
                            ],
                        ),

                        # Time segment controls
                        html.Div(
                            style={"padding": "10px 12px"},
                            children=[
                                html.Div("Time segment", style=LABEL_MUTED),

                                dcc.RangeSlider(
                                    id="segment-range",
                                    min=TIME_MIN,
                                    max=TIME_MAX + SLIDER_STEP,
                                    step=None,  # continuous
                                    value=[TIME_MIN, TIME_MAX],
                                    allowCross=False,
                                    marks=None,
                                    tooltip={"always_visible": False},
                                    updatemode="mouseup",
                                ),

                                # main time navigation row + currently selected on the same row
                                html.Div(
                                    [
                                        # LEFT: time navigation controls
                                        html.Div(
                                            [
                                                html.Span(
                                                    id="segment-label",
                                                    style={"fontWeight": 600, "marginRight": "10px"},
                                                ),

                                                html.Button(
                                                    "◀ Prev",
                                                    id="global-prev",
                                                    n_clicks=0,
                                                    style={
                                                        "fontSize": "12px",
                                                        "padding": "4px 8px",
                                                        "marginRight": "6px",
                                                    },
                                                ),

                                                html.Button(
                                                    "Next ▶",
                                                    id="global-next",
                                                    n_clicks=0,
                                                    style={
                                                        "fontSize": "12px",
                                                        "padding": "4px 8px",
                                                        "marginRight": "16px",
                                                    },
                                                ),

                                                dcc.Input(
                                                    id="play-speed",
                                                    type="number",
                                                    placeholder="speed (segments/sec)",
                                                    value=1.0,
                                                    step=0.1,
                                                    style={"width": "180px", "marginRight": "8px"},
                                                ),

                                                dcc.Checklist(
                                                    id="lock-window-toggle",
                                                    options=[{"label": " lock window", "value": "lock"}],
                                                    value=[],
                                                    style={
                                                        "display": "inline-block",
                                                        "marginRight": "8px",
                                                    },
                                                ),

                                                html.Button(
                                                    "Move ▶",
                                                    id="move-step",
                                                    n_clicks=0,
                                                    style={
                                                        "fontSize": "12px",
                                                        "padding": "4px 10px",
                                                        "marginRight": "6px",
                                                    },
                                                ),

                                                html.Span(
                                                    id="global-nav-info",
                                                    style=LABEL_MUTED | {"marginLeft": "10px"},
                                                ),
                                                html.Button(
                                                    "",
                                                    id="chunk-filter-banner",
                                                    n_clicks=0,
                                                    title="Go to chunk filtering",
                                                    style={
                                                        "display": "none",
                                                        "marginLeft": "10px",
                                                        "padding": "2px 8px",
                                                        "borderRadius": "999px",
                                                        "border": "1px solid #ffe08a",
                                                        "background": "#fff6d6",
                                                        "color": "#7a5a00",
                                                        "fontSize": "12px",
                                                        "fontWeight": 700,
                                                        "cursor": "pointer",
                                                    },
                                                ),
                                                html.Button(
                                                    "topo view",
                                                    id="btn-topo-view",
                                                    n_clicks=0,
                                                    title="Switch to topology view",
                                                    style={
                                                        "display": "none",
                                                        "marginLeft": "10px",
                                                        "padding": "2px 8px",
                                                        "borderRadius": "999px",
                                                        "border": "1px solid #cbd5e1",
                                                        "background": "#ffffff",
                                                        "color": "#334155",
                                                        "fontSize": "12px",
                                                        "fontWeight": 700,
                                                        "cursor": "pointer",
                                                    },
                                                ),
                                            ],
                                            style={
                                                "display": "flex",
                                                "alignItems": "center",
                                                "flexWrap": "wrap",
                                                "gap": "6px",
                                            },
                                        ),

                                        # RIGHT: currently selected (same row, right-aligned)
                                        html.Div(
                                            [
                                                html.Span(
                                                    "Currently selected:",
                                                    style=LABEL_MUTED | {"marginRight": "6px"},
                                                ),
                                                html.Span(
                                                    id="current-selection-summary",
                                                    children="None",
                                                    style={"fontWeight": 600, "marginRight": "12px"},
                                                ),
                                                html.Button(
                                                    "Details",
                                                    id="current-selection-btn",
                                                    n_clicks=0,
                                                    style={"fontSize": "12px", "padding": "4px 10px"},
                                                ),
                                            ],
                                            style={
                                                "display": "flex",
                                                "alignItems": "center",
                                                "gap": "6px",
                                                "marginLeft": "auto",  # push this block to the right
                                            },
                                        ),
                                    ],
                                    style={
                                        "marginTop": "10px",
                                        "display": "flex",
                                        "alignItems": "center",
                                        "flexWrap": "wrap",
                                        "gap": "6px",
                                    },
                                )
                            ],
                        ),
                    ],
                ),

                # Right panel: all the controls that used to be on the left
                # In app.layout -> children=[ ... -> main-grid -> RIGHT_CARD:

                html.Div(
                    style=RIGHT_CARD,
                    children=[
                        # Header row
                        html.Div(
                            style={
                                "display": "flex",
                                "alignItems": "center",
                                "marginBottom": "4px",
                            },
                            children=[
                                html.Span("Controls", style={"fontWeight": 600}),
                            ],
                        ),

                        # --- UNIFIED CONTAINER (Replace your two duplicate divs with this one) ---
                        # [Inside app.layout -> main-grid -> right-card -> left-panel-container]
                        html.Div(
                            id="left-panel-container",
                            children=[
                                # 1. File / Session Panels
                                html.Div(panel_session_save(), id="panel-session-save", style={"display": "none"}),
                                html.Div(panel_session_load(), id="panel-session-load", style={"display": "none"}),
                                html.Div(panel_topology_file(), id="panel-topology-file", style={"display": "none"}),
                                
                                # --- THIS IS THE MISSING PART THAT CAUSES THE BUG ---
                                html.Div(panel_collective_details(), id="panel-collective-details", style={"display": "none"}),
                                html.Div(panel_topology_details(), id="panel-topology-details", style={"display": "none"}),
                                # ----------------------------------------------------

                                # 2. Plotting & Coloring
                                html.Div(panel_plots(), id="panel-plots", style={"display": "none"}),
                                html.Div(panel_color(), id="panel-color", style={"display": "none"}),
                                html.Div(panel_param_coloring(), id="panel-param-coloring", style={"display": "none"}), 
                                html.Div(panel_param_filters(), id="panel-param-filters", style={"display": "none"}),

                                # 3. Filtering & Analysis
                                html.Div(panel_node(), id="panel-node", style={"display": "none"}),
                                html.Div(panel_filters(), id="panel-filters", style={"display": "block"}),
                                html.Div(panel_chunk(), id="panel-data", style={"display": "none"}),
                                html.Div(panel_logs(), id="panel-logs", style={"display": "none"}),
                            ],
                        ),
                        # ------------------------------------------------------------------------

                        html.Hr(),
                        html.Div(id="layout-status", style=LABEL_MUTED),
                    ],
                ),


            ],
        ),

    ],
)

# =========================
# Toolbar interactions / Left-rail nav
# =========================
@app.callback(
    # NOTE: Output active-panel logic remains the same
    Output("active-panel", "data", allow_duplicate=True),
    Output("filters-submode", "data", allow_duplicate=True),
    # Top buttons
    Input("btn-plots", "n_clicks"), 
    Input("btn-color", "n_clicks"), 
    Input("btn-filters", "n_clicks"),
    Input("btn-node", "n_clicks"), 
    Input("btn-chunks", "n_clicks"),
    # Menu items - Ensure these IDs match your layout
    Input("menu-save", "n_clicks"), 
    Input("menu-load", "n_clicks"),
Input("menu-topology-file", "n_clicks"), 
    prevent_initial_call=True,
)
def set_active_panel(n_plots, n_color, n_filters, n_node, n_chunks,
                     n_save, n_load, n_topofile):
    ctx = dash.callback_context
    if not ctx.triggered:
        raise PreventUpdate

    which = ctx.triggered[0]["prop_id"].split(".")[0]
    sub = "links"
    if which == "btn-node":
        sub = "links"

    # Mapping button ID -> Panel Name (internal string key)
    mapping = {
        "btn-plots": "plots",
        "btn-color": "color",
        "btn-filters": "filters",
        "btn-node": "node",
        "btn-chunks": "data",
        
        # New split mappings
        "menu-save": "session_save",      # Key for Save Panel
        "menu-load": "session_load",      # Key for Load Panel
"menu-topology-file": "topo_file",# Key for Topology File Panel
    }

    target = mapping.get(which, "filters")
    return target, sub


@app.callback(
    [
        Output("panel-topology-file", "style"),
        Output("panel-session-save", "style"),
        Output("panel-session-load", "style"),
        Output("panel-plots", "style"),
        Output("panel-color", "style"),
        Output("panel-param-coloring", "style"),
        Output("panel-param-filters", "style"),
        Output("panel-filters", "style"),
        Output("panel-node", "style"),
        Output("panel-data", "style"),
        Output("panel-logs", "style"),
        Output("panel-collective-details", "style"),
        Output("panel-topology-details", "style"),
    ],
    Input("active-panel", "data"),
)
def update_panels(active):
    if not active:
        active = "filters"
    if isinstance(active, dict):
        active = list(active.values())[0]

    def sty(name):
        return {"display": "block"} if active == name else {"display": "none"}

    return (
        sty("topo_file"),
        sty("session_save"),
        sty("session_load"),
        sty("plots"),
        sty("color"),
        sty("param_coloring"),
        sty("param_filters"),
        sty("filters"),
        sty("node"),
        sty("data"),
        sty("logs"),
        sty("collective_details"),
        sty("topology_details"),
    )


# Sub-mode switching inside Filters
@app.callback(
    Output("filters-links-section", "style"),
    Output("filters-nodes-section", "style"),
    Output("filters-chunks-section", "style"),
    Input("filters-submode", "data"),
    Input("filters-sub-links", "n_clicks"),
    Input("filters-sub-nodes", "n_clicks"),
    Input("filters-sub-chunks", "n_clicks"),
    State("filters-submode", "data"),
    prevent_initial_call=False
)
def show_filters_submode(current, nL, nN, nC, state_val):
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    sub = current or state_val or "links"
    if ctx.triggered:
        # Branch based on the current state / selection.
        which = ctx.triggered[0]["prop_id"].split(".")[0]
        if which == "filters-sub-links":
            # Branch based on the current state / selection.
            sub = "links"
        elif which == "filters-sub-nodes":
            # Alternative branch for a different condition.
            sub = "nodes"
        elif which == "filters-sub-chunks":
            # Alternative branch for a different condition.
            sub = "chunks"
    def sty(name): return {"display": "block"} if sub == name else {"display": "none"}
    return sty("links"), sty("nodes"), sty("chunks")

# Center-pane toggling

@app.callback(
    Output("graph-pane", "style"),
    Output("grid-pane", "style"),
    Output("postleft-pane", "style"),
    Output("wip-pane", "style"),
    Output("cum-pane", "style"),
    Output("avg-pane", "style"),
    Output("xy-pane", "style"),
    Output("postleft-matrix-pane", "style"),
    Input("plot-visible", "data"),
    Input("postleft-visible", "data"),
    Input("wip-visible", "data"),
    Input("cum-visible", "data"),
    Input("avg-visible", "data"),
    Input("xy-visible", "data"),
    Input("postleft-matrix-visible", "data"),
    prevent_initial_call=False
)
def toggle_center(grid_on, postleft_on, wip_on, cum_on, avg_on, xy_on, postleft_matrix_on):
    base = {"position": "absolute", "inset": "0"}
    def shown(b): 
        # Shown.
        return {**base, "display": "block"} if b else {**base, "display": "none"}

    # exactly one visible at a time
    if xy_on:
        # Branch based on the current state / selection.
        return shown(False), shown(False), shown(False), shown(False), shown(False), shown(False), shown(True),  shown(False)
    if postleft_on:
        # Branch based on the current state / selection.
        return shown(False), shown(False), shown(True),  shown(False), shown(False), shown(False), shown(False), shown(False)
    if postleft_matrix_on:
        # Branch based on the current state / selection.
        return shown(False), shown(False), shown(False), shown(False), shown(False), shown(False), shown(False), shown(True)
    if grid_on:
        # Branch based on the current state / selection.
        return shown(False), shown(True),  shown(False), shown(False), shown(False), shown(False), shown(False), shown(False)
    if wip_on:
        # Branch based on the current state / selection.
        return shown(False), shown(False), shown(False), shown(True),  shown(False), shown(False), shown(False), shown(False)
    if cum_on:
        # Branch based on the current state / selection.
        return shown(False), shown(False), shown(False), shown(False), shown(True),  shown(False), shown(False), shown(False)
    if avg_on:
        # Branch based on the current state / selection.
        return shown(False), shown(False), shown(False), shown(False), shown(False), shown(True),  shown(False), shown(False)

    # default (topology)
    return shown(True), shown(False), shown(False), shown(False), shown(False), shown(False), shown(False), shown(False)


@app.callback(
    Output("runjs", "run", allow_duplicate=True),
    Input("do-save", "n_clicks"),
    State("file-path", "data"),
    prevent_initial_call=True,
)
def save_layout_js(_n, path):
    # Save layout js.
    # Resolve and validate filesystem paths before using them.
    p = os.path.expanduser(path or PRESET_FILE)
    if not os.path.isabs(p):
        # Validate inputs / state before continuing.
        # Resolve and validate filesystem paths before using them.
        p = os.path.join(BASE_DIR, p)
    # Encode Python objects into JSON for storage/transport.
    path_js = json.dumps(p)
    return _js(r"""
    (function(){
      const status=(m)=>{const el=document.getElementById('layout-status'); if(el) el.textContent=m;};
      const host=document.getElementById('network-graph');
      if(!host){ status('Save failed: #network-graph not found'); return; }
      function getCy(){
        if (window.cy && typeof window.cy.nodes==='function') return window.cy;
        const inner=host.querySelector('.dash-cytoscape, .cytoscape-container');
        const cy=host._cy||host.cy||host.__cy||(inner?(inner._cy||inner.cy||inner.__cy):null);
        if (cy && typeof cy.nodes==='function') return cy;
        const first=host.firstElementChild;
        if(first && (first._cy||first.cy||first.__cy)){
          const c2=first._cy||first.cy||first.__cy;
          if(c2 && typeof c2.nodes==='function') return c2;
        }
        return null;
      }
      let tries=0;
      (function capture(){
        const cy=getCy();
        if(!cy){
          if(tries++<100){return setTimeout(capture,50);}
          status('Save failed: Cytoscape not ready'); return;
        }
        const pos={};
        cy.nodes().forEach(n=>{ const p=n.position(); pos[n.id()]={x:p.x,y:p.y}; });
        fetch('/save_layout',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({positions:pos,captured_at:Date.now(),path:$PATH_JS})})
          .then(r=>r.json()).then(js=>status(js && js.message?js.message:'Saved.'))
          .catch(e=>status('Save failed: '+e));
      })();
    })();
    """, PATH_JS=path_js)

@app.callback(
    Output("saved-layout", "data", allow_duplicate=True),
    Output("layout-status", "children", allow_duplicate=True),
    Output("layout-has-positions", "data", allow_duplicate=True),
    Input("do-load", "n_clicks"),
    State("path-input", "value"),
    State("topology-radio", "value"),
    prevent_initial_call=True
)
def do_load_layout(_n, path, active_tid):
    try:
        p = os.path.expanduser(path or PRESET_FILE)
        if not os.path.isabs(p):
            p = os.path.join(BASE_DIR, p)

        with open(p, "r") as f:
            data = json.load(f) or {}

        pos_map = data.get("positions", {})
        if not pos_map:
            return no_update, f"No positions found in {p}.", no_update

        # Remember per-topology immediately (so it behaves like your old preset flow)
        try:
            if active_tid is not None and int(active_tid) in TOPOLOGY_STATE:
                TOPOLOGY_STATE[int(active_tid)]["layout_path"] = p
        except Exception:
            pass

        return data, f"Loaded layout for {len(pos_map)} node(s) from {p}", True

    except FileNotFoundError:
        return no_update, f"File not found: {p}", no_update
    except Exception as e:
        return no_update, f"Failed to load from {p}: {e}", no_update


@app.callback(
    Output("elements-base", "data", allow_duplicate=True),
    Output("multi-logs", "data", allow_duplicate=True),
    Output("multi-logs-include", "data", allow_duplicate=True),
    Output("saved-layout", "data", allow_duplicate=True),
    Output("file-path", "data", allow_duplicate=True),
    Output("time-min", "data", allow_duplicate=True),
    Output("time-max", "data", allow_duplicate=True),
    Output("segment-range", "value", allow_duplicate=True),
    Output("cap-range", "min", allow_duplicate=True),
    Output("cap-range", "max", allow_duplicate=True),
    Output("cap-range", "value", allow_duplicate=True),
    Output("topology-radio", "value", allow_duplicate=True),
    Output("topology-status", "children", allow_duplicate=True),
    Output("multi-topos", "data"),
    Output("topology-radio", "options"),
    Output("network-graph", "layout", allow_duplicate=True),
    Output("network-graph", "pan", allow_duplicate=True),

    Input("load-topology-btn", "n_clicks"),
    State("topology-path-input", "value"),
    State("multi-topos", "data"),
    State("multi-logs-include", "data"),
    State("network-graph", "elements"),
    State("network-graph", "pan"),
    State("network-graph", "zoom"),
    prevent_initial_call=True,
)
def load_topology_from_file(n_clicks, path, topo_list, current_global_selection, cur_elements, cur_pan, cur_zoom):
    # Load a topology file and rebuild all derived structures used for visualization and filtering.
    if not n_clicks:
        # Guard: only run after the user triggers the action.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    topo_list = topo_list or []
    if not path:
        # Validate inputs / state before continuing.
        return (no_update,) * 15 + (no_update,)

    # Resolve and validate filesystem paths before using them.
    p = os.path.expanduser(path)
    if not os.path.isabs(p):
        # Validate inputs / state before continuing.
        # Resolve and validate filesystem paths before using them.
        p = os.path.join(BASE_DIR, p)

    if not os.path.exists(p):
        # Validate inputs / state before continuing.
        msg = f"Topology file not found: {p}"
        return (no_update,) * 12 + (msg, no_update, no_update, no_update)

    # 1. Determine ID
    existing_id = None
    for it in topo_list:
        # Iterate over the relevant items and accumulate results.
        if it.get("path") == p:
            # Branch based on the current state / selection.
            existing_id = int(it["id"])
            break
    
    if existing_id is None:
        # Validate inputs / state before continuing.
        used_ids = [int(item.get("id", 0)) for item in topo_list]
        new_id = (max(used_ids) + 1) if used_ids else 1
        # Resolve and validate filesystem paths before using them.
        label = os.path.basename(p)
        entry = {"id": int(new_id), "path": p, "label": label}
        topo_list = topo_list + [entry]
        active_id = new_id
    else:
        active_id = existing_id

    options = [{"label": f"[{it['id']}] {it['label']}", "value": int(it["id"])} for it in topo_list]

    # 2. Load State (Calculates positions automatically if new)
    new_state = _get_or_create_topo_state(active_id, p)
    
    elements = new_state["elements"]
    logs_data = new_state["logs"]
    
    # 3. Prepare Layout 
    layout_data = new_state.get("layout_data")
    saved_pos = layout_data.get("positions", {}) if layout_data else {}
    
    # --- FIX START: Explicitly retrieve calculated positions ---
    # The _get_or_create_topo_state function generates default positions into 'pos' 
    # if no saved layout exists. We must use these.
    calculated_pos = new_state.get("pos", {})

    import time
    ts = int(time.time() * 1000)

    # Use saved positions if available, otherwise use the calculated defaults.
    final_pos = saved_pos if saved_pos else calculated_pos

    # Merge chosen positions into the outgoing elements so preset layout and element positions stay consistent.
    elements_out = []
    for el in (elements or []):
        new_el = dict(el)
        nid = new_el.get("data", {}).get("id")
        if nid is not None:
            key = str(nid)
            if key in final_pos:
                new_el["position"] = final_pos[key]
        elements_out.append(new_el)

    # Compute a new pan that recenters the new topology without auto-fitting.
    new_pan = no_update
    try:
        def _center_from_elements(elems):
            xs = []
            ys = []
            for e in (elems or []):
                p = e.get("position")
                d = e.get("data", {}) or {}
                if p and d.get("id") is not None:
                    xs.append(float(p.get("x", 0.0)))
                    ys.append(float(p.get("y", 0.0)))
            if not xs:
                return None
            return (sum(xs) / len(xs), sum(ys) / len(ys))

        old_center = _center_from_elements(cur_elements)
        new_center = _center_from_elements(elements_out)

        z = float(cur_zoom or 1.0)
        pan0 = (cur_pan or {"x": 0, "y": 0})
        px = float(pan0.get("x", 0.0))
        py = float(pan0.get("y", 0.0))

        if new_center:
            if old_center:
                anchor_x = old_center[0] * z + px
                anchor_y = old_center[1] * z + py
            else:
                # First load / no reliable previous center: put the new topology near a reasonable viewport point.
                anchor_x = 500.0
                anchor_y = 350.0
            new_pan = {"x": anchor_x - new_center[0] * z, "y": anchor_y - new_center[1] * z}
    except Exception:
        new_pan = no_update

    # We always pass 'positions' to the layout. This forces Cytoscape to 
    # move the nodes to these coordinates immediately.
    graph_layout = {
        "name": "preset",
        "positions": final_pos,
        "fit": False, 
        "animate": False,
        "ts": ts
    }
    # --- FIX END ---

    layout_path = new_state.get("layout_path", PRESET_FILE)
    tmin, tmax = new_state["time_bounds"]
    if tmin is None: tmin = 0.0
    if tmax is None: tmax = 100.0
    seg = new_state["segment"]
    if not seg or len(seg) != 2: seg = [tmin, tmax]
    cmin, cmax = new_state["cap_range"]
    if cmax <= cmin: cmax = cmin + 1.0

    # Resolve and validate filesystem paths before using them.
    msg = f"Loaded [{active_id}] {os.path.basename(p)}."

    # Update Globals
    global VIZ, TOPO_FILE, G
    VIZ = None
    TOPO_FILE = p
    G = new_state["G"]
    
    valid_ids_in_new_topo = set(int(l["id"]) for l in logs_data)
    global_selected_ids = set(map(int, current_global_selection or []))
    active_intersection = list(global_selected_ids.intersection(valid_ids_in_new_topo))
    active_intersection.sort()

    if active_intersection:
        # Branch based on the current state / selection.
        active_lid = active_intersection[0]
        active_log = next((l for l in logs_data if int(l["id"]) == active_lid), None)
        if active_log:
             # Branch based on the current state / selection.
             _active_viz_from_multi([active_log], [active_lid])
             VIZ = MULTI_VIZ_OBJS.get(active_lid)

    return (
        elements_out, 
        logs_data, 
        no_update,      
        layout_data, 
        layout_path,
        tmin, tmax, seg, cmin, cmax, [cmin, cmax],
        active_id, msg, topo_list, options,
        graph_layout,
        new_pan
    )

@app.callback(
    Output("topology-path-input", "value"),
    Output("topology-status", "children", allow_duplicate=True),
    Input("upload-topology", "contents"),
    State("upload-topology", "filename"),
    prevent_initial_call=True,
)
def handle_upload_topology(contents, filename):
    # Load a topology file and rebuild all derived structures used for visualization and filtering.
    if not contents or not filename:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    try:
        content_type, content_string = contents.split(",")
        decoded = base64.b64decode(content_string)
        # Resolve and validate filesystem paths before using them.
        safe_name = os.path.basename(filename)
        # Resolve and validate filesystem paths before using them.
        out_path = os.path.join(UPLOAD_DIR, safe_name)
        with open(out_path, "wb") as f:
            # Open the file and ensure it is closed correctly.
            f.write(decoded)
        msg = f"Uploaded topology to {out_path}. Click 'Load topology' to use it."
        return out_path, msg
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return no_update, f"Upload failed: {e}"

@app.callback(
    Output("path-input", "value"),
    Output("layout-status", "children", allow_duplicate=True),
    Input("upload-layout", "contents"),
    State("upload-layout", "filename"),
    prevent_initial_call=True,
)
def handle_upload_layout(contents, filename):
    if not contents or not filename:
        raise PreventUpdate
    try:
        content_type, content_string = contents.split(",")
        decoded = base64.b64decode(content_string)
        safe_name = os.path.basename(filename)
        out_path = os.path.join(UPLOAD_DIR, safe_name)
        with open(out_path, "wb") as f:
            f.write(decoded)
        msg = f"Uploaded layout to {out_path}. Click 'Load from path' to apply it."
        return out_path, msg
    except Exception as e:
        return no_update, f"Upload failed: {e}"


@app.callback(
    Output("new-session-modal", "style"),
    Input("menu-new", "n_clicks"),
    Input("new-session-cancel", "n_clicks"),
    Input("new-session-confirm", "n_clicks"),
    State("new-session-modal", "style"),
    prevent_initial_call=True,
)
def toggle_new_session_modal(n_new, n_cancel, n_confirm, style):
    # Toggle a UI feature/state and propagate the change to dependent components.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    if not ctx.triggered:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    which = ctx.triggered[0]["prop_id"].split(".")[0]
    style = dict(style or {})
    if which == "menu-new":
        # open modal
        style["display"] = "flex"
    else:
        # cancel or confirm -> close modal
        style["display"] = "none"
    return style


@app.callback(
    Output("runjs", "run", allow_duplicate=True),
    Input("new-session-confirm", "n_clicks"),
    prevent_initial_call=True,
)
def start_new_session(n_confirm):
    # Validate inputs.
    if not n_confirm:
        raise PreventUpdate

    # 1. Declare ALL globals that hold state
    global TOPO_FILE, LOG_FILE, G, NUM_NODES, SWITCH_IDS, EDGES, POS, ELEMS, CAP_MIN, CAP_MAX, VIZ
    global MULTI_VIZ_OBJS, TOPOLOGY_STATE, TOPO_CACHE, _NODE_FIRSTS_ALL, _NODE_FIRSTS_BY_CHUNK

    # 2. Reset Singleton Variables
    TOPO_FILE = "" 
    LOG_FILE = os.path.join(BASE_DIR, "visYarin.json") # Default or empty
    G = nx.Graph()
    NUM_NODES = 0
    SWITCH_IDS = set() # Ensure this is a set or list matching init
    EDGES = []
    POS = {}
    ELEMS = []
    CAP_MIN = 0.0
    CAP_MAX = 1.0
    VIZ = None

    # 3. Clear Dictionary Caches (Crucial!)
    # Using .clear() ensures the specific object instance is emptied
    if 'MULTI_VIZ_OBJS' in globals():
        MULTI_VIZ_OBJS.clear()
    
    if 'TOPOLOGY_STATE' in globals():
        TOPOLOGY_STATE.clear()
        
    # If you defined TOPO_CACHE earlier in the script (it appeared in _recompute_topology_from_file)
    if 'TOPO_CACHE' in globals():
        TOPO_CACHE.clear()

    # Clear helper caches
    if '_NODE_FIRSTS_ALL' in globals():
        _NODE_FIRSTS_ALL.clear()
    if '_NODE_FIRSTS_BY_CHUNK' in globals():
        _NODE_FIRSTS_BY_CHUNK.clear()

    # 4. Force Browser Reload
    # This clears all client-side dcc.Store components (assuming storage_type='memory')
    return "window.location.reload();"

# Defaults UI
@app.callback(
    Output("default-select", "options"),
    Output("default-select", "value"),
    Output("defaults-status", "children", allow_duplicate=True),
    Input("defaults-refresh", "n_clicks"),
    prevent_initial_call=True
)
def refresh_defaults(_n):
    # Refresh defaults.
    try:
        with open(DEFAULTS_FILE, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) or {"defaults": {}}
        names = sorted(list((data.get("defaults") or {}).keys()))
        opts = [{"label": n, "value": n} for n in names]
        val = (names[0] if names else None)
        msg = f"Found {len(names)} default(s)." if names else "No defaults saved yet."
        return opts, val, msg
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return no_update, no_update, f"Failed to list defaults: {e}"

@app.callback(
    Output("default-selected-name", "children"),
    Input("default-select", "value"),
    prevent_initial_call=False
)
def show_selected_default(name):
    # Show selected default.
    if not name: return ""
    return f"Selected default: {name}"

@app.callback(
    Output("saved-layout", "data", allow_duplicate=True),
    Output("layout-status", "children", allow_duplicate=True),
    Input("default-load-btn", "n_clicks"),
    State("default-select", "value"),
    prevent_initial_call=True
)
def load_default_layout(_n, name):
    # Load default layout.
    if not name:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    try:
        with open(DEFAULTS_FILE, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) or {"defaults": {}}
        defs = data.get("defaults", {})
        if name not in defs:
            # Validate inputs / state before continuing.
            return no_update, f"Default '{name}' not found."
        pos = defs[name].get("positions", {})
        if not pos:
            # Validate inputs / state before continuing.
            return no_update, f"Default '{name}' has no positions."
        return {"positions": pos}, f"Loaded default '{name}' ({len(pos)} positions)."
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return no_update, f"Failed to load default: {e}"

@app.callback(
    Output("defaults-status", "children", allow_duplicate=True),
    Input("default-delete-btn", "n_clicks"),
    State("default-select", "value"),
    prevent_initial_call=True
)
def delete_default(_n, name):
    # Delete default.
    if not name:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    try:
        with open(DEFAULTS_FILE, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) | {"defaults": {}}
        defs = data.get("defaults", {})
        if name not in defs:
            # Validate inputs / state before continuing.
            return f"Default '{name}' not found."
        del defs[name]
        data["defaults"] = defs
        _atomic_json_write(DEFAULTS_FILE, data)
        return f"Deleted default '{name}'. Click Refresh to update the list."
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return f"Failed to delete default: {e}"

@app.callback(
    Output("runjs", "run", allow_duplicate=True),
    Input("default-save-btn", "n_clicks"),
    State("default-name-input", "value"),
    prevent_initial_call=True
)
def save_default_js(_n, name):
    # Save default js.
    name = (name or "").strip()
    if not name:
        # Validate inputs / state before continuing.
        return "document.getElementById('defaults-status').textContent='Please enter a default name.';"
    # Encode Python objects into JSON for storage/transport.
    name_js = json.dumps(name)
    return _js(r"""
    (function(){
      const status=(m)=>{const el=document.getElementById('defaults-status'); if(el) el.textContent=m;};
      const host=document.getElementById('network-graph');
      if(!host){ status('Save failed: #network-graph not found'); return; }
      function getCy(){
        if (window.cy && typeof window.cy.nodes==='function') return window.cy;
        const inner=host.querySelector('.dash-cytoscape, .cytoscape-container');
        const cy=host._cy||host.cy||host.__cy||(inner?(inner._cy||inner.cy||inner.__cy):null);
        if (cy && typeof cy.nodes==='function') return cy;
        const first=host.firstElementChild;
        if(first && (first._cy||first.cy||first.__cy)){
          const c2=first._cy||first.cy||first.__cy;
          if(c2 && typeof c2.nodes==='function') return c2;
        }
        return null;
      }
      let tries=0;
      (function capture(){
        const cy=getCy();
        if(!cy){
          if(tries++<100){return setTimeout(capture,50);}
          status('Save failed: Cytoscape not ready'); return;
        }
        const pos={};
        cy.nodes().forEach(n=>{ const p=n.position(); pos[n.id()]={x:p.x,y:p.y}; });
        fetch('/defaults_layout',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({op:'save',name:$NAME_JS,positions:pos,captured_at:Date.now()})})
          .then(r=>r.json()).then(js=>status(js && js.message?js.message:'Saved default. Use "Refresh".'))
          .catch(e=>status('Save failed: '+e));
      })();
    })();
    """, NAME_JS=name_js)

# =========================
# Elements & styling (filters, isolation, hidden, chunk presence)
# =========================

def _filter_elements_by_nodes(all_elements, allowed_ids):
    # Apply the current filter settings and compute the resulting subset for display.
    if not allowed_ids:
        # Validate inputs / state before continuing.
        return all_elements
    sel = set(map(str, allowed_ids))
    keep = []
    # keep nodes
    for el in all_elements:
        # Iterate over the relevant items and accumulate results.
        data = el.get("data", {})
        if "id" in data and data["id"] in sel:
            # Branch based on the current state / selection.
            keep.append(el)
    # keep edges within set
    for el in all_elements:
        # Iterate over the relevant items and accumulate results.
        data = el.get("data", {})
        if "source" in data and "target" in data:
            # Branch based on the current state / selection.
            if data["source"] in sel and data["target"] in sel:
                # Branch based on the current state / selection.
                keep.append(el)
    return keep

@app.callback(
    Output("network-graph", "elements"),
    Input("elements-base", "data"),
    Input("node-filter-ids", "data"),
    Input("isolate-mode", "data"),
    Input("isolate-snapshot", "data"),
    Input("hidden-nodes", "data"),
    Input("chunk-presence", "data"),
    Input("selected-nodes", "data"),
    Input("highlight-chunk-nodes", "data"),
    Input("highlight-postleft-nodes", "data"),
    State("current-selection", "data"),
    prevent_initial_call=False
)
def build_elements(base_elements, node_filter_ids, isolate_mode, snapshot_ids, hidden_nodes,
                   presence, selected_nodes, highlight_chunk_nodes, highlight_postleft_nodes,
                   current_sel):

    base = base_elements or ELEMS
    # Copy elements to avoid mutating source
    elements = [{**el} for el in base]

    # Filter by visible nodes
    allowed_ids = _visible_node_ids(base, node_filter_ids, isolate_mode, snapshot_ids, hidden_nodes)
    elements = _filter_elements_by_nodes(elements, allowed_ids)

    # Mark Selections
    sel = set(map(str, selected_nodes or []))
    if sel:
        for el in elements:
            did = el.get("data", {}).get("id")
            if did and did in sel:
                el["selected"] = True

    if current_sel and isinstance(current_sel, dict) and current_sel.get("kind") == "edge":
        src_sel = str(current_sel.get("source"))
        dst_sel = str(current_sel.get("target"))
        for el in elements:
            d = el.get("data", {}) or {}
            if d.get("source") == src_sel and d.get("target") == dst_sel:
                el["selected"] = True
                break

    # Chunk Presence Glow
    if presence:
        have = set(str(n) for n in presence.get("nodes", []))
        for el in elements:
            nid = el.get("data", {}).get("id")
            if nid and nid in have:
                cls = el.get("classes", "")
                if "has-chunk" not in cls:
                    el["classes"] = (cls + " has-chunk").strip()

    # --- REMOVED: "el.pop('position', None)" ---
    # We now keep the positions so the graph doesn't reset or jump.
    # -------------------------------------------

    # Highlights (Thresholds)
    def _normalize_hstore(x):
        # Normalize hstore.
        if isinstance(x, dict): return set(str(i) for i in x.get("ids", []))
        return set(str(i) for i in (x or []))

    hi_chunks = _normalize_hstore(highlight_chunk_nodes)
    hi_post   = _normalize_hstore(highlight_postleft_nodes)
    
    if hi_chunks or hi_post:
        for el in elements:
            nid = el.get("data", {}).get("id")
            if not nid: continue
            cls = el.get("classes", "")
            parts = set(cls.split()) if cls else set()
            if nid in hi_chunks: parts.add("thresh-chunks")
            if nid in hi_post:   parts.add("thresh-postleft")
            if parts:
                el["classes"] = " ".join(sorted(parts))

    return elements

@app.callback(
    Output("isolate-mode", "data", allow_duplicate=True),
    Input("isolate-btn", "n_clicks"),
    State("isolate-mode", "data"),
    prevent_initial_call=True
)
def toggle_isolation(_n, cur):
    # Toggle a UI feature/state and propagate the change to dependent components.
    return not bool(cur)

@app.callback(
    Output("isolate-snapshot", "data", allow_duplicate=True),
    Input("isolate-mode", "data"),
    State("network-graph", "selectedNodeData"),
    prevent_initial_call=True
)
def snapshot_isolation(mode_on, selectedNodeData):
    # Snapshot isolation.
    if mode_on:
        # Branch based on the current state / selection.
        ids = [d.get("id") for d in (selectedNodeData or []) if d and "id" in d]
        return ids if ids else None
    return None

# Keep selected nodes store
@app.callback(
    Output("selected-nodes", "data", allow_duplicate=True),
    Input("network-graph", "selectedNodeData"),
    prevent_initial_call=True
)
def keep_selected(selectedNodeData):
    # Keep selected.
    return [d.get("id") for d in (selectedNodeData or []) if d and "id" in d]

# Keep a single "currently selected" node or link (node preferred)
@app.callback(
    Output("current-selection", "data"),
    Input("network-graph", "selectedNodeData"),
    Input("network-graph", "selectedEdgeData"),
    prevent_initial_call=False,
)
def update_current_selection(selectedNodeData, selectedEdgeData):
    # Prefer nodes if any are selected
    # Update current selection.
    if selectedNodeData:
        # Branch based on the current state / selection.
        last = None
        for d in (selectedNodeData or []):
            # Iterate over the relevant items and accumulate results.
            if d and isinstance(d, dict) and d.get("id") is not None:
                # Validate inputs / state before continuing.
                last = d
        if last:
            # Branch based on the current state / selection.
            nid = last.get("id")
            try:
                nid_int = int(nid)
            except Exception:
                # Recover from a failure case and return a safe default.
                nid_int = nid
            return {
                "kind": "node",
                "id": nid_int,
                "label": last.get("label") or str(nid_int),
            }

    # Otherwise, fall back to edges
    if selectedEdgeData:
        # Branch based on the current state / selection.
        last = None
        for d in (selectedEdgeData or []):
            # Iterate over the relevant items and accumulate results.
            if (
                d and isinstance(d, dict)
                and d.get("source") is not None
                and d.get("target") is not None
            ):
                last = d
        if last:
            # Branch based on the current state / selection.
            src = last.get("source")
            dst = last.get("target")
            try:
                src_int = int(src)
            except Exception:
                # Recover from a failure case and return a safe default.
                src_int = src
            try:
                dst_int = int(dst)
            except Exception:
                # Recover from a failure case and return a safe default.
                dst_int = dst
            return {
                "kind": "edge",
                "source": src_int,
                "target": dst_int,
                "capacity": last.get("capacity"),
                "latency": last.get("latency"),
                "label": last.get("label"),
            }

    # Nothing selected → keep previous selection
    return no_update


@app.callback(
    Output("current-selection-summary", "children"),
    Input("current-selection", "data"),
    prevent_initial_call=False,
)
def current_selection_summary(sel):
    # Current selection summary.
    if not sel or not sel.get("kind"):
        # Validate inputs / state before continuing.
        return "None"

    kind = sel.get("kind")
    if kind == "node":
        # Branch based on the current state / selection.
        nid = sel.get("id")
        return f"Node {nid}"

    if kind == "edge":
        # Branch based on the current state / selection.
        src = sel.get("source")
        dst = sel.get("target")
        return f"Link {src} → {dst}"

    return "None"



@app.callback(
    Output("current-selection-open", "data"),
    Input("current-selection-btn", "n_clicks"),
    Input("current-selection-close", "n_clicks"),
    State("current-selection-open", "data"),
    prevent_initial_call=True,
)
def toggle_current_selection_modal(n_open, n_close, is_open):
    # Toggle a UI feature/state and propagate the change to dependent components.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    if not ctx.triggered:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    which = ctx.triggered[0]["prop_id"].split(".")[0]
    if which == "current-selection-btn":
        # Branch based on the current state / selection.
        return True
    if which == "current-selection-close":
        # Branch based on the current state / selection.
        return False
    return is_open

@app.callback(
    Output("current-selection-details", "children"),
    Output("current-selection-modal", "style"),
    Input("current-selection-open", "data"),
    Input("current-selection", "data"),
    Input("segment-range", "value"),           
    Input("chunk-filter-ids", "data"),
    Input("active-collectives-map", "data"), # CHANGED
    Input("topology-radio", "value"),        # ADDED
    State("topo-logs", "data"),              # ADDED
    prevent_initial_call=False,
)
def render_current_selection_details(
    is_open,
    sel,
    seg,
    allowed_chunks,
    active_coll_map,
    active_topo_id,
    topo_logs
):
    # ... style def ...
    base_style = {
        "position": "fixed",
        "right": "24px",
        "bottom": "90px",
        "width": "320px",
        "maxHeight": "40vh",
        "overflowY": "auto",
        "background": "#ffffff",
        "border": "1px solid #e1e7ef",
        "borderRadius": "10px",
        "boxShadow": "0 4px 12px rgba(15,23,42,0.25)",
        "padding": "10px 12px",
        "zIndex": 20,
        "display": "block" if is_open else "none",
    }

    if not sel or not sel.get("kind"):
        return html.Div("No node or link selected."), base_style

    seg0, seg1 = (seg or [TIME_MIN, TIME_MAX])
    try: seg0=float(seg0); seg1=float(seg1)
    except: seg0=float(TIME_MIN); seg1=float(TIME_MAX)
    t1 = seg1
    if seg1 <= seg0: seg1 = seg0 + 1e-9

    allowed_chunk_set = (set(int(c) for c in (allowed_chunks or [])) if allowed_chunks else None)

    # Use helper
    viz_list = _get_active_viz_list(active_coll_map, active_topo_id, topo_logs)
    
    # We also need labels/colors, so we manually iterate bundles
    bundles = _get_active_log_bundles(active_coll_map, active_topo_id, topo_logs)
    selected_logs = []
    
    # Match bundles to VIZ objects (safe)
    for b in bundles:
        lid = int(b["id"])
        V = MULTI_VIZ_OBJS.get(lid)
        if V: selected_logs.append((lid, b.get("label"), b.get("color"), V))
        
    if not selected_logs and VIZ:
        # Fallback if VIZ exists but no bundles active? (Shouldn't happen with correct logic)
        pass

    if not is_open or not sel:
        return "", base_style

    children = []
    kind = sel.get("kind")

    # ... (Node Logic - Replace `logs_in` usage with `selected_logs`) ...
    if kind == "node":
        nid = sel.get("id")
        children.append(html.H4(f"Node {nid}", style={"margin": "0 0 6px"}))
        try: nid_int = int(nid)
        except: nid_int = nid

        chunks_seen = set()
        all_post_chunks = set()
        done_post_chunks = set()

        for _lid, _lbl, _col, V in selected_logs:
            # ... (Existing loop logic) ...
            node_lc = getattr(V, "nodeLifeCycle", [])
            if nid_int < 0 or nid_int >= len(node_lc): continue
            arrivals_dict = node_lc[nid_int]
            if not isinstance(arrivals_dict, dict): continue
            for cid, events in (arrivals_dict or {}).items():
                if not events: continue
                try: icid = int(cid)
                except: continue
                if allowed_chunk_set is not None and icid not in allowed_chunk_set: continue
                try: earliest_any = _safe_min([float(ts) for (ts, _msg) in events], default=None)
                except: earliest_any = None
                if earliest_any is not None and earliest_any <= t1: chunks_seen.add(icid)
                try: non_seed_times = [float(ts) for (ts, msg) in events if (msg is None or str(msg).lower() != "seed")]
                except: non_seed_times = []
                if non_seed_times:
                    try: earliest_non_seed = _safe_min(non_seed_times, default=None)
                    except: earliest_non_seed = None
                    if earliest_non_seed is not None:
                        all_post_chunks.add(icid)
                        if earliest_non_seed <= t1: done_post_chunks.add(icid)

        children.append(html.Div(f"Total chunks that traveled on this node so far: {len(chunks_seen)}"))
        children.append(html.Div(f"Post-conditions left on this node: {len(all_post_chunks - done_post_chunks)}"))

        segment_chunks = set()
        for (lid, label, color, V) in selected_logs:
            with _use_viz(V):
                try: chunks_here, _msg = _chunks_on_node_in_segment(nid_int, seg0, seg1)
                except: continue
            if allowed_chunk_set is not None:
                chunks_here = [c for c in chunks_here if c in allowed_chunk_set]
            for c in chunks_here: segment_chunks.add(int(c))

        if segment_chunks:
            shown = sorted(segment_chunks)[:100]
            pretty = ", ".join(map(str, shown)) + ("..." if len(segment_chunks)>100 else "")
            children.append(html.Hr())
            children.append(html.Div("Chunks on this node in current segment:", style={"marginTop": "4px"}))
            children.append(html.Pre(pretty, style={"whiteSpace": "pre-wrap", "margin": "4px 0 0"}))

    # ... (Edge Logic - Replace `logs_in` usage with `selected_logs`) ...
    elif kind == "edge":
        src = sel.get("source")
        dst = sel.get("target")
        cap = sel.get("capacity")
        lat = sel.get("latency")
        children.append(html.H4(f"Link {src} → {dst}", style={"margin": "0 0 6px"}))
        if cap: children.append(html.Div(f"Capacity: {cap}"))
        if lat: children.append(html.Div(f"Latency: {lat} ms"))

        try: src_int, dst_int = int(src), int(dst)
        except: src_int, dst_int = None, None

        has_vars = False
        for (lid, label, color, V) in selected_logs:
            if V is None: continue
            lvars = getattr(V, "link_vars", [])
            for lv in lvars:
                per_link = getattr(lv, "per_link", {}) or {}
                series = None
                if src_int is not None and dst_int is not None:
                    series = per_link.get((src_int, dst_int)) or per_link.get((dst_int, src_int))
                if series is None:
                    series = per_link.get((str(src), str(dst))) or per_link.get((str(dst), str(src)))
                if series:
                    has_vars = True
                    try:
                        avg_val = _avg_series_on_segment(series, seg0, seg1)
                        val_str = f"{avg_val:.3f}"
                        extra = ""
                        try:
                            if float(cap or 0) > 0: extra = f" ({(avg_val/float(cap))*100:.1f}%)"
                        except: pass
                        children.append(html.Div([
                            html.Span(f"{lv.name}", style={"fontWeight":"600"}),
                            html.Span(f" ({label}): ", style={"color":"#666", "fontSize":"0.9em"}),
                            html.Span(f"{val_str}{extra}")
                        ]))
                    except: pass
        if not has_vars:
             children.append(html.Div("No link metrics found.", style={"color":"#999", "marginTop":"6px", "fontStyle":"italic"}))

        link_intervals = []
        if src_int is not None and dst_int is not None:
            for (lid, label, color, V) in selected_logs:
                DV = getattr(V, "primary_data", None)
                if not DV: continue
                try: detailed = DV.link_chunks_detailed_in_segment(src_int, dst_int, seg0, seg1)
                except: detailed = []
                for rec in detailed:
                    c = int(rec.get("chunk"))
                    if allowed_chunk_set and c not in allowed_chunk_set: continue
                    link_intervals.append({
                        "chunk": c, "t_start": float(rec["t_start"]), "t_end": float(rec["t_end"]),
                        "label": label, "log_id": lid
                    })
        
        if link_intervals:
            link_intervals.sort(key=lambda it: it["t_end"])
            lines = []
            multi = len(selected_logs) > 1
            for rec in link_intervals[:120]:
                line = f"chunk {rec['chunk']}" + (f" ({rec['label']})" if multi else "") + f": {rec['t_start']:.3f} → {rec['t_end']:.3f}"
                lines.append(line)
            if len(link_intervals) > 120: lines.append("...")
            children.append(html.Hr())
            children.append(html.Div("Chunks on link:", style={"marginTop": "4px"}))
            children.append(html.Pre("\n".join(lines), style={"whiteSpace": "pre-wrap", "margin": "4px 0 0"}))

    return html.Div(children, style={"fontSize": "12px", "lineHeight": "1.4"}), base_style


# --- 2. Switch Radio to "Parameter" when Dropdown is Used ---
@app.callback(
    Output("color-mode-radio", "value"),
    Input("param-select-dropdown", "value"),
    State("color-mode-radio", "value"),
    prevent_initial_call=True
)
def switch_to_param_mode(param_name, current_mode):
    # If user picks a param, force mode to 'parameter'
    # Switch to param mode.
    if param_name:
        # Branch based on the current state / selection.
        return "parameter"
    # If user clears dropdown, revert to 'none' if currently on 'parameter'
    if current_mode == "parameter":
        # Branch based on the current state / selection.
        return "none"
    return no_update

# --- 3. Compute Parameter Values ---
@app.callback(
    Output("param-values", "data"),
    Output("param-stats-info", "children"),
    Input("param-select-dropdown", "value"),
    Input("segment-range", "value"),
    Input("param-data-id", "value"),
    Input("active-collectives-map", "data"), # CHANGED
    Input("topology-radio", "value"),
    State("topo-logs", "data"),
    State("avail-params", "data"),
    prevent_initial_call=True
)
def compute_coloring_values(param_name, seg, data_id, active_coll_map, active_topo_id, topo_logs, all_params):
    # Compute coloring values.
    if not param_name: return {}, ""

    # If this is a data/chunk parameter, require a specific Data ID for coloring.
    p_type = "link"
    for p in (all_params or []):
        try:
            if p.get("value") == param_name:
                p_type = p.get("type", "link")
                break
        except Exception:
            continue

    if p_type == "data" and data_id is None:
        return {}, "Enter a Data ID (chunk #) to color by this data parameter."

    viz_list = _get_active_viz_list(active_coll_map, active_topo_id, topo_logs)
    if not viz_list: return {}, "No active logs."

    t0, t1 = (seg or [TIME_MIN, TIME_MAX])
    result = _aggregate_param_values(param_name, float(t0), float(t1), data_id, viz_list)
    
    if not result: return {}, "No data found."

    if result.get("type") == "data":
        # Branch based on the current state / selection.
        c = result.get("data_id", "?")
        n_nodes = len(result.get("nodes", []))
        n_links = len(result.get("links", []))
        return result, f"Chunk {c}: Present on {n_nodes} nodes (union), traversed {n_links} links."
        
    vmin = result.get("min", 0)
    vmax = result.get("max", 0)
    return result, f"Range (avg) in segment: {vmin:.2f} to {vmax:.2f}"

# Hide selected (Clear hidden REMOVED per request)
@app.callback(
    Output("hidden-nodes", "data", allow_duplicate=True),
    Output("hidden-status", "children", allow_duplicate=True),
    Input("hide-selected-btn", "n_clicks"),
    State("hidden-nodes", "data"),
    State("network-graph", "selectedNodeData"),
    prevent_initial_call=True
)
def hide_selected(n_hide, hidden, selectedNodeData):
    # Hide selected.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    if not ctx.triggered:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    current = set(int(i) for i in (hidden or []) if str(i).isdigit())
    sel = set()
    for d in (selectedNodeData or []):
        # Iterate over the relevant items and accumulate results.
        try:
            sel.add(int(d.get("id")))
        except Exception:
            # Recover from a failure case and return a safe default.
            pass
    if not sel:
        # Validate inputs / state before continuing.
        return no_update, "No selected nodes to hide."
    new_hidden = sorted(current | sel)
    return new_hidden, f"Hidden {len(sel)} node(s). Total hidden: {len(new_hidden)}."

@app.callback(
    Output("hidden-nodes", "data", allow_duplicate=True),
    Output("node-filter-ids", "data", allow_duplicate=True),
    Output("chunk-filter-ids", "data", allow_duplicate=True),
    Output("isolate-mode", "data", allow_duplicate=True),
    Output("isolate-snapshot", "data", allow_duplicate=True),
    Output("network-graph", "layout", allow_duplicate=True),
    Output("cap-range", "value", allow_duplicate=True),
    Output("edge-types", "value", allow_duplicate=True),
    Output("hidden-status", "children", allow_duplicate=True),
    Output("node-ops-status", "children", allow_duplicate=True),
    Output("chunk-filter-status", "children", allow_duplicate=True),
    Input("clear-view-btn", "n_clicks"),
    Input("clear-all-filters", "n_clicks"),
    # --- CHANGED FROM INPUT TO STATE ---
    State("elements-base", "data"),         
    # -----------------------------------
    State("saved-layout", "data"),
    prevent_initial_call=True
)
def clear_hide_and_filters(_n_view, _n_all, elements_base, saved_layout):
    # Reapply positions: prefer the currently selected/saved layout, else fall back to initial baked positions.
    # Apply the current filter settings and compute the resulting subset for display.
    pos_map = {}
    if saved_layout and saved_layout.get("positions"):
        # Branch based on the current state / selection.
        pos_map = saved_layout["positions"]
    else:
        for el in (elements_base or ELEMS):
            # Iterate over the relevant items and accumulate results.
            d = el.get("data", {})
            p = el.get("position")
            if d.get("id") and p:
                # Branch based on the current state / selection.
                pos_map[d["id"]] = {"x": p["x"], "y": p["y"]}
    layout = {"name": "preset", "positions": pos_map, "fit": False, "animate": False} if pos_map \
             else {"name": "preset", "fit": False, "animate": False}

    # Reset edge filters to defaults (full range + all types)
    full_types = ["etype-host-host", "etype-switch-switch", "etype-host-switch"]
    # We need to calculate the current CAP_MIN/MAX to reset the slider correctly.
    # Since we don't have them as inputs here, we can derive them from elements or just fallback.
    # A safe fallback is [0, 1] or reading from a store, but for "Clear", full range usually implies default globals.
    # If CAP_MIN/MAX are global, we can use them directly or recalculate from elements.
    
    # Recalculate min/max from elements to be safe (since globals might be stale if we relied on them)
    caps = []
    for el in (elements_base or []):
        # Iterate over the relevant items and accumulate results.
        try:
            c = float(el.get("data", {}).get("capacity", 0))
            caps.append(c)
        except: pass
    
    if caps:
        # Branch based on the current state / selection.
        cmin, cmax = min(caps), max(caps)
        if cmax <= cmin: cmax = cmin + 1.0
    else:
        cmin, cmax = 0.0, 1.0

    cap_default = [cmin, cmax]

    return (
        [],                 # hidden-nodes
        [],                 # node-filter-ids
        [],                 # chunk-filter-ids
        False,              # isolate-mode
        None,               # isolate-snapshot
        layout,             # network-graph.layout (re-apply positions)
        cap_default,        # cap-range
        full_types,         # edge-types
        "Cleared hidden nodes.",         # hidden-status
        "Cleared node filter.",          # node-filter-status
        "Cleared chunk filter."          # chunk-filter-status
    )

@app.callback(
    Output("cap-range", "min"),
    Output("cap-range", "max"),
    Output("cap-range", "step"),
    Input("elements-base", "data"),
    prevent_initial_call=True,
)
def update_cap_slider_bounds(_elements_base):
    """
    Keep the capacity RangeSlider in sync with the currently loaded topology.
    CAP_MIN / CAP_MAX are updated by _recompute_topology_from_file().
    """
    # Update cap slider bounds.
    try:
        lo = float(CAP_MIN)
        hi = float(CAP_MAX)
    except Exception:
        # Recover from a failure case and return a safe default.
        lo, hi = 0.0, 1.0

    # Avoid degenerate range
    if hi <= lo:
        # Branch based on the current state / selection.
        hi = lo + 1.0

    step = (hi - lo) / 100.0
    return lo, hi, step



# Color UI → store
@app.callback(
    Output("color-mode", "data", allow_duplicate=True),
    Input("color-mode-radio", "value"),
    prevent_initial_call=True
)
def set_color_mode(val):
    # Set color mode.
    return val or "none"

def _avg_step_value(series, s0, s1):
    """
    Average of a piecewise-constant series on [s0, s1].
    series: sorted list[(time, value)], value holds until next time.
    """
    # Avg step value.
    try:
        s0 = float(s0); s1 = float(s1)
    except Exception:
        # Recover from a failure case and return a safe default.
        return 0.0
    if s1 <= s0:
        # Branch based on the current state / selection.
        return 0.0

    v = 0.0
    idx = 0
    n = len(series)

    # value just before/at s0
    while idx < n and float(series[idx][0]) <= s0:
        # Loop until the stopping condition is reached.
        v = float(series[idx][1])
        idx += 1

    cur_t = s0
    total = 0.0

    # integrate until s1
    while idx < n and float(series[idx][0]) < s1:
        # Loop until the stopping condition is reached.
        t_ev = float(series[idx][0])
        if t_ev > cur_t:
            # Branch based on the current state / selection.
            total += v * (t_ev - cur_t)
            cur_t = t_ev
        v = float(series[idx][1])
        idx += 1

    # tail
    if s1 > cur_t:
        # Branch based on the current state / selection.
        total += v * (s1 - cur_t)

    return total / (s1 - s0)


def _flow_color_scale(val, vmin, vmax):
    """
    Map val in [vmin, vmax] to a color between green (#2a9d8f) and red (#e63946).
    Low flow = green, high flow = red.
    """
    # Flow color scale.
    try:
        val = float(val); vmin = float(vmin); vmax = float(vmax)
    except Exception:
        # Recover from a failure case and return a safe default.
        return "#2a9d8f"
    if vmax <= vmin:
        # Branch based on the current state / selection.
        return "#2a9d8f"

    # green → red
    r0, g0, b0 = (42, 157, 143)   # #2a9d8f
    r1, g1, b1 = (230, 57, 70)    # #e63946

    t = (val - vmin) / (vmax - vmin)
    if t < 0.0: t = 0.0
    if t > 1.0: t = 1.0

    r = int(round(r0 + t * (r1 - r0)))
    g = int(round(g0 + t * (g1 - g0)))
    b = int(round(b0 + t * (b1 - b0)))
    return f"#{r:02x}{g:02x}{b:02x}"


def _flow_color_scale(val, vmin, vmax):
    """
    Map val in [vmin, vmax] to a color between green (#2a9d8f) and red (#e63946).
    Low flow = green, high flow = red.
    """
    # Flow color scale.
    try:
        val = float(val); vmin = float(vmin); vmax = float(vmax)
    except Exception:
        # Recover from a failure case and return a safe default.
        return "#2a9d8f"
    if vmax <= vmin:
        # Branch based on the current state / selection.
        return "#2a9d8f"

    r0, g0, b0 = (42, 157, 143)   # green-ish
    r1, g1, b1 = (230, 57, 70)    # red-ish

    t = (val - vmin) / (vmax - vmin)
    if t < 0.0: t = 0.0
    if t > 1.0: t = 1.0

    r = int(round(r0 + t * (r1 - r0)))
    g = int(round(g0 + t * (g1 - g0)))
    b = int(round(b0 + t * (b1 - b0)))
    return f"#{r:02x}{g:02x}{b:02x}"


def _avg_series_on_segment(series, s0, s1):
    """
    series: sorted list[(time, value)] for one link.
    Semantics: value is 0 before the first event; after each event
    the value stays constant until the next event.

    Returns the time–average on [s0, s1].
    """
    # Avg series on segment.
    try:
        s0 = float(s0)
        s1 = float(s1)
    except Exception:
        # Recover from a failure case and return a safe default.
        return 0.0

    if s1 <= s0:
        # Branch based on the current state / selection.
        return 0.0
    if not series:
        # Validate inputs / state before continuing.
        return 0.0

    # Sort just in case
    series = sorted(series, key=lambda x: float(x[0]))

    total = 0.0
    cur_t = s0
    cur_v = 0.0
    n = len(series)
    i = 0

    # 1) Find value just before s0 (include event exactly at s0)
    while i < n and float(series[i][0]) <= s0:
        # Loop until the stopping condition is reached.
        cur_v = float(series[i][1])
        i += 1

    # 2) Integrate over all events in (s0, s1)
    while i < n and float(series[i][0]) < s1:
        # Loop until the stopping condition is reached.
        t_ev = float(series[i][0])
        if t_ev > cur_t:
            # Branch based on the current state / selection.
            total += cur_v * (t_ev - cur_t)
            cur_t = t_ev
        cur_v = float(series[i][1])
        i += 1

    # 3) Tail from last change (or s0) up to s1
    if s1 > cur_t:
        # Branch based on the current state / selection.
        total += cur_v * (s1 - cur_t)

    return total / (s1 - s0)


# =========================
# Node threshold coloring (by chunks received and by post-conditions left)
# =========================
def _chunks_got_by_time(rank: int, t: float) -> int:
    # Chunks got by time.
    if VIZ is None:
        # Validate inputs / state before continuing.
        return 0
    try:
        r = int(rank)
    except Exception:
        # Recover from a failure case and return a safe default.
        return 0
    lc = getattr(VIZ, "nodeLifeCycle", [])
    if r < 0 or r >= len(lc):
        # Branch based on the current state / selection.
        return 0
    got = 0
    for _cid, arrivals in lc[r].items():
        # Iterate over the relevant items and accumulate results.
        if not arrivals:
            # Validate inputs / state before continuing.
            continue
        try:
            t_first = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
        except Exception:
            # Recover from a failure case and return a safe default.
            continue
        if t_first <= float(t):
            # Branch based on the current state / selection.
            got += 1
    return got


@app.callback(
    Output("highlight-chunk-nodes", "data", allow_duplicate=True),
    Output("highlight-postleft-nodes", "data", allow_duplicate=True),
    Output("node-ops-status", "children", allow_duplicate=True),
    Input("btn-color-chunk-thresh", "n_clicks"),
    Input("btn-color-postleft-thresh", "n_clicks"),
    Input("btn-clear-highlights", "n_clicks"),
    Input("segment-range", "value"),
    State("chunk-count-threshold", "value"),
    State("postleft-threshold", "value"),
    State("highlight-chunk-nodes", "data"),
    State("highlight-postleft-nodes", "data"),
    State("elements-base", "data"),
    State("node-filter-ids", "data"),
    State("isolate-mode", "data"),
    State("isolate-snapshot", "data"),
    State("hidden-nodes", "data"),
    State("multi-logs", "data"),
    State("multi-logs-include", "data"), # CHANGED
    prevent_initial_call=True
)
def apply_node_highlights(n_chunks_btn, n_post_btn, n_clear, seg,
                          chunk_thr, post_thr,
                          prev_hi_chunks, prev_hi_post,
                          elements_base, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes,
                          multi_logs, include_ids):
    # ... rest of function remains identical ...
    ctx = dash.callback_context
    if not ctx.triggered:
        raise PreventUpdate
    which = ctx.triggered[0]["prop_id"].split(".")[0]

    # Determine active VIZ (lowest selected log), fallback to current
    Vsel = _active_viz_from_multi(multi_logs, include_ids)
    with _use_viz(Vsel):
        if which == "btn-clear-highlights":
            return {"ids": [], "active": False}, {"ids": [], "active": False}, "Cleared node highlights."

        allowed_nodes = _visible_node_ids(elements_base or ELEMS, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes)
        hosts = [n for n in allowed_nodes if n not in SWITCH_IDS]
        t1 = float((seg or [TIME_MIN, TIME_MAX])[1])

        # Helper recompute functions
        def recompute_chunks():
            # Recompute chunks.
            thr = int(chunk_thr or 0)
            if thr <= 0:
                # Branch based on the current state / selection.
                return []
            out = []
            for r in hosts:
                # Iterate over the relevant items and accumulate results.
                try:
                    if _chunks_got_by_time(r, t1) >= thr:
                        # Branch based on the current state / selection.
                        out.append(r)
                except Exception:
                    # Recover from a failure case and return a safe default.
                    pass
            return out

        def recompute_postleft():
            # Recompute postleft.
            thr = int(post_thr or 0)
            if thr <= 0:
                # Branch based on the current state / selection.
                return []
            out = []
            for r in hosts:
                # Iterate over the relevant items and accumulate results.
                try:
                    if _post_conditions_left(r, t1) >= thr:
                        # Branch based on the current state / selection.
                        out.append(r)
                except Exception:
                    # Recover from a failure case and return a safe default.
                    pass
            return out

        # Mode selection
        if which == "btn-color-chunk-thresh":
            ids = recompute_chunks()
            msg = f"Colored {len(ids)} node(s) with chunks ≥ {int(chunk_thr or 0)} by t_end."
            return {"ids": ids, "active": True}, dash.no_update, msg

        if which == "btn-color-postleft-thresh":
            ids = recompute_postleft()
            msg = f"Colored {len(ids)} node(s) with post-left ≥ {int(post_thr or 0)} by t_end."
            return dash.no_update, {"ids": ids, "active": True}, msg

        # Slider moved -> refresh whichever mode(s) are active
        if which == "segment-range":
            out_chunks = None
            out_post = None
            if isinstance(prev_hi_chunks, dict) and prev_hi_chunks.get("active"):
                out_chunks = {"ids": recompute_chunks(), "active": True}
            elif isinstance(prev_hi_chunks, list):
                # backwards-compat: treat non-None as active
                out_chunks = {"ids": recompute_chunks(), "active": True}
            if isinstance(prev_hi_post, dict) and prev_hi_post.get("active"):
                out_post = {"ids": recompute_postleft(), "active": True}
            elif isinstance(prev_hi_post, list):
                out_post = {"ids": recompute_postleft(), "active": True}
            if out_chunks is None and out_post is None:
                raise PreventUpdate
            if out_chunks is None:
                out_chunks = dash.no_update
            if out_post is None:
                out_post = dash.no_update
            return out_chunks, out_post, dash.no_update

    raise PreventUpdate


@app.callback(
    Output("node-filter-ids", "data", allow_duplicate=True),
    Output("node-ops-status", "children", allow_duplicate=True),
    Output("network-graph", "layout", allow_duplicate=True),
    Input("apply-node-filter", "n_clicks"),
    Input("add-range-btn", "n_clicks"),
    Input("clear-node-filter", "n_clicks"),
    State("node-filter-text", "value"),
    State("range-start", "value"),
    State("range-end", "value"),
    State("range-step", "value"),
    State("node-post-left-min", "value"),
    State("segment-range", "value"),
    State("node-filter-ids", "data"),
    State("saved-layout", "data"),
    State("elements-base", "data"),
    prevent_initial_call=True
)
def node_filter_actions(n_apply, n_add, n_clear, spec, r_start, r_end, r_step, post_left_min, seg, current_ids, saved_layout, elements_base):
    # Apply the current filter settings and compute the resulting subset for display.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    if not ctx.triggered:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    which = ctx.triggered[0]["prop_id"].split(".")[0]
    cur = set(map(int, current_ids or []))
    reapply_layout = no_update

    if which == "apply-node-filter":
        # Branch based on the current state / selection.
        ids = _parse_num_spec(spec or "")
        candidates = sorted(set(ids)) if ids else list(range(_rank_count()))

    elif which == "add-range-btn":
        # Alternative branch for a different condition.
        try:
            start = int(r_start); end = int(r_end); step = int(r_step if r_step not in (None, 0) else 1)
            rng = list(range(start, end + 1, step)) if start <= end else list(range(start, end - 1, -abs(step)))
            cur |= set(int(i) for i in rng)
            candidates = sorted(cur)
        except Exception:
            # Recover from a failure case and return a safe default.
            return no_update, "Invalid range parameters.", no_update

    elif which == "clear-node-filter":
        # clear filter and reapply current layout (or initial)
        pos_map = None
        if (saved_layout or {}).get("positions"):
            # Branch based on the current state / selection.
            pos_map = saved_layout["positions"]
        else:
            pos_map = {}
            for el in (elements_base or ELEMS):
                # Iterate over the relevant items and accumulate results.
                d = el.get("data", {}); p = el.get("position")
                if "id" in d and p:
                    # Branch based on the current state / selection.
                    pos_map[d["id"]] = {"x": p["x"], "y": p["y"]}
        if pos_map:
            # Branch based on the current state / selection.
            reapply_layout = {"name":"preset","positions":pos_map,"fit": False,"animate":False}
        return [], "Cleared node filter.", reapply_layout

    else:
        candidates = sorted(cur)

    # Apply post-conditions-left threshold if provided (inclusive)
    threshold = 0 if post_left_min in (None, "") else max(0, int(post_left_min))
    t1 = float((seg or [TIME_MIN, TIME_MAX])[1])
    if threshold > 0:
        # Branch based on the current state / selection.
        filt = []
        for r in candidates:
            # Iterate over the relevant items and accumulate results.
            try:
                val = _post_conditions_left(r, t1)
                if val >= threshold:
                    # Branch based on the current state / selection.
                    filt.append(r)
            except Exception:
                # Recover from a failure case and return a safe default.
                pass
        return sorted(filt), f"Applied node filter with post-conditions-left ≥ {threshold}: {len(filt)} node(s).", reapply_layout
    else:
        return sorted(candidates), f"Applied node filter: {len(candidates)} node(s).", reapply_layout

# =========================
# Groups manager (user-defined groups)
# =========================
@server.route("/node_groups", methods=["POST"])
def node_groups_route():
    # Node groups route.
    try:
        # Parse the incoming request body as JSON.
        payload = request.get_json(force=True) or {}
        op = payload.get("op")
        _ensure_groups_file()
        with open(GROUPS_FILE, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) or {"groups": {}}
        groups = data.get("groups", {})

        if op == "list":
            # Branch based on the current state / selection.
            names = sorted(groups.keys())
            return jsonify(ok=True, names=names)

        if op == "save":
            # Branch based on the current state / selection.
            name = (payload.get("name") or "").strip()
            nodes = payload.get("nodes") or []
            if not name:
                # Validate inputs / state before continuing.
                return jsonify(ok=False, message="Missing group name."), 400
            if not nodes:
                # Validate inputs / state before continuing.
                return jsonify(ok=False, message="No nodes provided."), 400
            groups[name] = {"nodes": sorted(list({int(n) for n in nodes})), "saved_at": payload.get("captured_at")}
            data["groups"] = groups
            _atomic_json_write(GROUPS_FILE, data)
            return jsonify(ok=True, message=f"Saved group '{name}' ({len(groups[name]['nodes'])} nodes).")

        if op == "get":
            # Branch based on the current state / selection.
            name = (payload.get("name") or "").strip()
            if name not in groups:
                # Validate inputs / state before continuing.
                return jsonify(ok=False, message=f"Group '{name}' not found."), 404
            return jsonify(ok=True, nodes=groups[name].get("nodes", []))

        if op == "delete":
            # Branch based on the current state / selection.
            name = (payload.get("name") or "").strip()
            if name not in groups:
                # Validate inputs / state before continuing.
                return jsonify(ok=False, message=f"Group '{name}' not found."), 404
            del groups[name]
            data["groups"] = groups
            _atomic_json_write(GROUPS_FILE, data)
            return jsonify(ok=True, message=f"Deleted group '{name}'.")

        return jsonify(ok=False, message="Unknown op."), 400
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return jsonify(ok=False, message=f"Groups op failed: {e}"), 500

@app.callback(
    Output("runjs", "run", allow_duplicate=True),
    Output("groups-status", "children", allow_duplicate=True),
    Input("group-save-btn", "n_clicks"),
    State("group-name-input", "value"),
    State("node-filter-text", "value"),
    State("node-filter-ids", "data"),
    prevent_initial_call=True
)
def save_group(_n, name, spec_text, current_ids):
    # Save group.
    name = (name or "").strip()
    if not name:
        # Validate inputs / state before continuing.
        return no_update, "Enter a group name."
    nodes = _parse_num_spec(spec_text or "")
    if not nodes:
        # Validate inputs / state before continuing.
        nodes = list(map(int, current_ids or []))
    if not nodes:
        # Validate inputs / state before continuing.
        return no_update, "No nodes to save (type nodes/range or apply a filter first)."
    # Encode Python objects into JSON for storage/transport.
    name_js = json.dumps(name)
    # Encode Python objects into JSON for storage/transport.
    nodes_js = json.dumps(nodes)
    js = _js(r"""
    (function(){
      const status=(m)=>{ const el=document.getElementById('groups-status'); if(el) el.textContent=m; };
      status('Saving group…');
      fetch('/node_groups',{method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({"op":"save","name":$NAME_JS,"nodes":$NODES_JS,"captured_at":Date.now()})})
        .then(r=>r.json()).then(js=>status(js && js.message?js.message:'Saved group. Use "Refresh".'))
        .catch(e=>status('Save failed: '+e));
    })();
    """, NAME_JS=name_js, NODES_JS=nodes_js)
    return js, no_update

@app.callback(
    Output("runjs", "run", allow_duplicate=True),
    Output("groups-status", "children", allow_duplicate=True),
    Input("group-save-from-selection-btn", "n_clicks"),
    State("group-name-input", "value"),
    prevent_initial_call=True
)
def save_group_from_selection(_n, name):
    # Save group from selection.
    name = (name or "").strip()
    if not name:
        # Validate inputs / state before continuing.
        return no_update, "Enter a group name."
    # Encode Python objects into JSON for storage/transport.
    name_js = json.dumps(name)
    js = _js(r"""
    (function(){
      const status=(m)=>{ const el=document.getElementById('groups-status'); if(el) el.textContent=m; };
      const host=document.getElementById('network-graph');
      function getCy(){
        if (window.cy && typeof window.cy.nodes==='function') return window.cy;
        const inner=host && host.querySelector? host.querySelector('.dash-cytoscape, .cytoscape-container'):null;
        return (host?(host._cy||host.cy||host.__cy):null) || (inner?(inner._cy||inner.cy||inner.__cy):null);
      }
      const cy=getCy();
      if(!cy){ status('Cannot read selection (Cytoscape not ready).'); return; }
      const sel=cy.nodes(':selected').map(n=>n.id()).map(s=>parseInt(s)).filter(n=>!isNaN(n));
      if(!sel.length){ status('No selected nodes.'); return; }
      status('Saving group from selection…');
      fetch('/node_groups',{method:'POST',headers:{'Content-Type':'application/json'},
        body:JSON.stringify({"op":"save","name":$NAME_JS,"nodes":sel,"captured_at":Date.now()})})
        .then(r=>r.json()).then(js=>status(js && js.message?js.message:'Saved group. Use "Refresh".'))
        .catch(e=>status('Save failed: '+e));
    })();
    """, NAME_JS=name_js)
    return js, no_update

@app.callback(
    Output("group-select", "options"),
    Output("groups-status", "children", allow_duplicate=True),
    Input("groups-refresh", "n_clicks"),
    prevent_initial_call=True
)
def refresh_groups(_n):
    # Refresh groups.
    try:
        with open(GROUPS_FILE, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) or {"groups": {}}
        names = sorted(list((data.get("groups") or {}).keys()))
        opts = [{"label": n, "value": n} for n in names]
        msg = f"Found {len(names)} group(s)." if names else "No groups saved yet."
        return opts, msg
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return no_update, f"Failed to list groups: {e}"

@app.callback(
    Output("node-filter-ids", "data", allow_duplicate=True),
    Output("node-ops-status", "children", allow_duplicate=True),
    Input("group-load-btn", "n_clicks"),
    State("group-select", "value"),
    prevent_initial_call=True
)
def load_group(_n, name):
    # Load group.
    if not name:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    try:
        with open(GROUPS_FILE, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) or {"groups": {}}
        groups = data.get("groups", {})
        if name not in groups:
            # Validate inputs / state before continuing.
            return no_update, f"Group '{name}' not found."
        nodes = groups[name].get("nodes", [])
        return nodes, f"Applied group '{name}' → {len(nodes)} node(s)."
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return no_update, f"Failed to load group: {e}"
# =========================
#  MASTER SWITCH CALLBACK
# =========================
# [Paste this to replace the existing master_topology_switch callback]
import time 

@app.callback(
    # --- Outputs ---
    Output("elements-base", "data", allow_duplicate=True),
    Output("multi-logs", "data", allow_duplicate=True),
    Output("multi-logs-include", "data", allow_duplicate=True),
    Output("saved-layout", "data", allow_duplicate=True),
    Output("file-path", "data", allow_duplicate=True),
    Output("time-min", "data", allow_duplicate=True),
    Output("time-max", "data", allow_duplicate=True),
    Output("segment-range", "value", allow_duplicate=True),
    Output("cap-range", "min", allow_duplicate=True),
    Output("cap-range", "max", allow_duplicate=True),
    Output("cap-range", "value", allow_duplicate=True),
    Output("topology-radio", "value", allow_duplicate=True),
    Output("topology-status", "children", allow_duplicate=True),
    
    # --- Filter Outputs ---
    Output("edge-types", "value", allow_duplicate=True),
    Output("node-filter-ids", "data", allow_duplicate=True),
    Output("chunk-filter-ids", "data", allow_duplicate=True),
    Output("isolate-mode", "data", allow_duplicate=True),
    Output("isolate-snapshot", "data", allow_duplicate=True),
    Output("hidden-nodes", "data", allow_duplicate=True),
    Output("param-filter-store", "data", allow_duplicate=True),
    
    # --- Layout Output ---
    Output("network-graph", "layout", allow_duplicate=True),
    Output("network-graph", "pan", allow_duplicate=True),

    # --- Inputs ---
    Input({'type': 'topo-select-btn', 'index': ALL}, "n_clicks"),
    
    # --- States ---
    State("topology-radio", "value"),      
    State("multi-logs", "data"),           
    State("multi-logs-include", "data"),
    State("saved-layout", "data"),
    State("file-path", "data"),
    State("time-min", "data"),
    State("time-max", "data"),
    State("segment-range", "value"),
    State("multi-topos", "data"),
    
    State("network-graph", "elements"), 
    State("network-graph", "pan"),
    State("network-graph", "zoom"),
    
    State("cap-range", "value"), 
    State("edge-types", "value"),
    State("node-filter-ids", "data"),
    State("chunk-filter-ids", "data"),
    State("isolate-mode", "data"),
    State("isolate-snapshot", "data"),
    State("hidden-nodes", "data"),
    State("param-filter-store", "data"),
    
    prevent_initial_call=True
)
def master_topology_switch(
    n_clicks_list, 
    prev_id, prev_logs, current_global_selection, prev_layout_store, prev_layout_path, 
    prev_tmin, prev_tmax, prev_seg,
    all_topos,
    current_graph_elements,
    cur_pan,
    cur_zoom,
    prev_cap_val, prev_edge_types, prev_node_ids, prev_chunk_ids, 
    prev_iso_mode, prev_iso_snap, prev_hidden, prev_param_filter
):
    ctx = dash.callback_context
    if not ctx.triggered: raise PreventUpdate

    triggered_prop = ctx.triggered[0]['prop_id']
    triggered_value = ctx.triggered[0]['value']
    
    if not triggered_value: raise PreventUpdate

    try:
        import json
        prop_id_json = json.loads(triggered_prop.split(".")[0])
        new_id = int(prop_id_json.get("index"))
    except Exception: raise PreventUpdate

    # 1. SAVE STATE of the PREVIOUS topology
    if prev_id is not None:
        try:
            prev_id_int = int(prev_id)
            # Ensure the previous state object exists
            if prev_id_int in TOPOLOGY_STATE:
                state = TOPOLOGY_STATE[prev_id_int]
                
                # Capture positions only if valid elements exist
                captured_positions = {}
                if current_graph_elements:
                    for el in current_graph_elements:
                        if "position" in el and "data" in el and "id" in el["data"]:
                            # IMPORTANT: Save as string keys for consistency
                            captured_positions[str(el["data"]["id"])] = el["position"]
                
                if captured_positions:
                    state["layout_data"] = {"positions": captured_positions}
                else:
                    state["layout_data"] = prev_layout_store

                state["logs"] = prev_logs or []
                state["layout_path"] = prev_layout_path
                state["time_bounds"] = (prev_tmin, prev_tmax)
                state["segment"] = prev_seg
                state["filters"] = {
                    "cap_val": prev_cap_val, "edge_types": prev_edge_types,
                    "node_ids": prev_node_ids, "chunk_ids": prev_chunk_ids,
                    "iso_mode": prev_iso_mode, "iso_snap": prev_iso_snap,
                    "hidden": prev_hidden, "param_filter": prev_param_filter
                }
        except Exception as e:
            print(f"Error saving previous state: {e}")

    # 2. LOAD STATE of the NEW topology
    topo_entry = next((t for t in (all_topos or []) if int(t["id"]) == new_id), None)
    if not topo_entry: raise PreventUpdate 

    new_state = _get_or_create_topo_state(new_id, topo_entry["path"])

    # Load Layout positions
    layout_data = new_state.get("layout_data")
    saved_pos = layout_data.get("positions", {}) if layout_data else {}

    # --- FIX: Force layout update with timestamp to avoid caching issues ---
    # We add a timestamp so Dash/React perceives this as a new object even if keys are identical.
    ts = int(time.time() * 1000)
    
    if saved_pos:
        new_layout_prop = {
            "name": "preset", 
            "positions": saved_pos, 
            "fit": False, 
            "animate": False,
            "ts": ts
        }
    else:
        # Explicitly NO positions key to revert to element-based positions
        new_layout_prop = {
            "name": "preset", 
            "fit": False, 
            "animate": False, 
            "ts": ts
        }

    # Merge Saved Positions into Elements (Deep Copy)
    raw_elements = new_state["elements"]
    elements = []
    for el in raw_elements:
        new_el = dict(el)
        nid = new_el.get("data", {}).get("id")
        if nid and str(nid) in saved_pos:
            new_el["position"] = saved_pos[str(nid)]
        elements.append(new_el)

    logs_data = new_state["logs"] 
    layout_path = new_state.get("layout_path", PRESET_FILE)
    
    tmin, tmax = new_state["time_bounds"]
    if tmin is None: tmin = 0.0
    if tmax is None: tmax = 100.0
    
    seg = new_state["segment"]
    if not seg or len(seg) != 2: seg = [tmin, tmax]
    
    cmin, cmax = new_state["cap_range"]
    if cmax <= cmin: cmax = cmin + 1.0
    
    # Restore Filters
    filters = new_state.get("filters", {})
    out_cap_val = filters.get("cap_val", [cmin, cmax])
    out_edge_types = filters.get("edge_types", ["etype-host-host", "etype-switch-switch", "etype-host-switch"])
    out_node_ids = filters.get("node_ids", [])
    out_chunk_ids = filters.get("chunk_ids", [])
    out_iso_mode = filters.get("iso_mode", False)
    out_iso_snap = filters.get("iso_snap", None)
    out_hidden = filters.get("hidden", [])
    out_param_filter = filters.get("param_filter", None)

    msg = f"Switched to [{new_id}] {os.path.basename(new_state['path'])}."

    # Update Global VIZ
    global VIZ, TOPO_FILE, G
    VIZ = None
    TOPO_FILE = new_state["path"]
    G = new_state["G"]
    
    valid_ids_in_new_topo = set(int(l["id"]) for l in logs_data)
    global_selected_ids = set(map(int, current_global_selection or []))
    
    active_intersection = list(global_selected_ids.intersection(valid_ids_in_new_topo))
    active_intersection.sort()

    if active_intersection:
        active_lid = active_intersection[0]
        active_log = next((l for l in logs_data if int(l["id"]) == active_lid), None)
        if active_log:
             _active_viz_from_multi([active_log], [active_lid])
             VIZ = MULTI_VIZ_OBJS.get(active_lid)


    # Recenter the viewport on topology switches without auto-fitting.
    # Keep the current zoom, but adjust pan so the new topology's center lands where the previous topology's
    # visible center was rendered. This prevents "off-screen" topologies while keeping zoom buttons usable.
    new_pan = no_update
    try:
        def _center_from_elements(elems):
            xs = []
            ys = []
            for el in (elems or []):
                p = el.get("position")
                d = el.get("data", {}) or {}
                if p and d.get("id") is not None:
                    xs.append(float(p.get("x", 0.0)))
                    ys.append(float(p.get("y", 0.0)))
            if not xs:
                return None
            return (sum(xs) / len(xs), sum(ys) / len(ys))

        old_center = _center_from_elements(current_graph_elements)
        new_center = _center_from_elements(elements)

        z = float(cur_zoom or 1.0)
        pan0 = (cur_pan or {"x": 0, "y": 0})
        px = float(pan0.get("x", 0.0))
        py = float(pan0.get("y", 0.0))

        if new_center:
            if old_center:
                anchor_x = old_center[0] * z + px
                anchor_y = old_center[1] * z + py
            else:
                # First load / no reliable previous center: put the new topology near a reasonable viewport point.
                anchor_x = 500.0
                anchor_y = 350.0
            new_pan = {"x": anchor_x - new_center[0] * z, "y": anchor_y - new_center[1] * z}
    except Exception:
        new_pan = no_update

    return (
        elements, logs_data, no_update, layout_data, layout_path, 
        tmin, tmax, seg, cmin, cmax, out_cap_val, new_id, msg,
        out_edge_types, out_node_ids, out_chunk_ids, out_iso_mode, 
        out_iso_snap, out_hidden, out_param_filter,
        new_layout_prop,
        new_pan
    )


# ---------------------------------------------------------
# NEW: Topology Tree & Log Selection Logic
# ---------------------------------------------------------

@app.callback(
    Output("topology-groups-container", "children"),
    Input("multi-topos", "data"),
    Input("topo-logs", "data"),
    Input("topology-radio", "value"),
    State("active-collectives-map", "data"),
    prevent_initial_call=False
)
def render_topology_tree(multi_topos, topo_collectives, active_topo_id, active_coll_map):
    # Render topology tree.
    multi_topos = multi_topos or []
    topo_collectives = topo_collectives or {}
    active_coll_map = active_coll_map or {}
    
    sorted_topos = sorted(multi_topos, key=lambda x: int(x.get("id", 0)))
    children = []
    
    if not sorted_topos:
        # Validate inputs / state before continuing.
        return html.Div("No topologies loaded.", style=LABEL_MUTED)

    for topo in sorted_topos:
        # Iterate over the relevant items and accumulate results.
        tid = str(topo["id"])
        is_active = (active_topo_id is not None and str(tid) == str(active_topo_id))
        
        collectives = topo_collectives.get(tid, [])
        bg_color = "#e3f2fd" if is_active else "#f8f9fa"
        border_color = "#2196f3" if is_active else "#e1e7ef"
        
        # 1. Topology Header (Updated with Topo Page Button)
        header = html.Div(
            style={
                "padding": "6px 10px", "borderRadius": "6px",
                "backgroundColor": bg_color, "border": f"1px solid {border_color}",
                "display": "flex", "alignItems": "center", "marginBottom": "4px"
            },
            children=[
                # Clickable Label (Selects Topology)
                html.Div(
                    id={'type': 'topo-select-btn', 'index': tid},
                    n_clicks=0,
                    style={"flex": "1", "cursor": "pointer", "fontWeight": "600" if is_active else "normal"},
                    children=[
                        html.Span(f"[{tid}] {topo.get('label', 'Topology')}"),
                        html.Span("● ACTIVE" if is_active else "", style={"fontSize": "9px", "color": "#2196f3", "fontWeight": "bold", "marginLeft": "8px"})
                    ]
                ),
                # Config Button (Goes to Page)
                html.Button(
                    "⚙", 
                    id={'type': 'topo-details-btn', 'index': tid},
                    n_clicks=0,
                    title="Topology Page",
                    style={"marginLeft": "8px", "padding": "2px 6px", "cursor": "pointer", "border": "1px solid #ccc", "borderRadius": "4px", "background": "#fff"}
                )
            ]
        )

        # 2. Action Deck (Coloring/Filters)
        action_deck = None
        if is_active:
            # Branch based on the current state / selection.
            btn_style = {"flex": "1", "fontSize": "11px", "padding": "4px", "border": "1px solid #d0d7de", "background": "white", "borderRadius": "4px", "cursor": "pointer", "textAlign": "center"}
            action_deck = html.Div(
                style={"display": "flex", "gap": "6px", "marginTop": "2px", "padding": "0 4px"},
                children=[
                    html.Div("Coloring", id={'type': 'topo-action-btn', 'index': tid, 'action': 'coloring'}, n_clicks=0, style=btn_style),
                    html.Div("Filters", id={'type': 'topo-action-btn', 'index': tid, 'action': 'filters'}, n_clicks=0, style=btn_style),
                ]
            )

        # 3. Collectives List
        coll_list_items = []
        active_ids_for_topo = active_coll_map.get(tid, [])

        if collectives:
            # Branch based on the current state / selection.
            for coll in collectives:
                # Iterate over the relevant items and accumulate results.
                cid = coll["id"]; cname = coll["name"]; logs = coll.get("logs", [])
                is_checked = cid in active_ids_for_topo
                log_names = [l.get("label", "log") for l in logs]
                logs_txt = ", ".join(log_names) if log_names else "(no logs)"
                
                item = html.Div(
                    style={"marginTop": "6px", "padding": "6px", "border": "1px solid #eee", "borderRadius": "6px", "background": "white"},
                    children=[
                        html.Div(
                            style={"display": "flex", "alignItems": "center", "justifyContent": "space-between"},
                            children=[
                                dcc.Checklist(
                                    id={'type': 'coll-checklist', 'index': cid, 'topo': tid},
                                    options=[{"label": f" {cname}", "value": cid}],
                                    value=[cid] if is_checked else [],
                                    style={"fontWeight": "600", "fontSize": "13px"}
                                ),
                                html.Button("+ Log", id={'type': 'coll-add-log-btn', 'index': cid, 'topo': tid}, n_clicks=0, style={"fontSize": "10px", "padding": "2px 6px", "cursor": "pointer"}),
                                html.Button("Coll Page", id={'type': 'coll-details-btn', 'index': cid, 'topo': tid}, n_clicks=0, style={"fontSize": "10px", "padding": "2px 6px", "cursor": "pointer", "backgroundColor": "#f0f0f0", "border": "1px solid #ccc"})
                            ]
                        ),
                        html.Div(f"Logs: {logs_txt}", style={"fontSize": "11px", "color": "#888", "marginLeft": "24px", "marginTop": "2px"})
                    ]
                )
                coll_list_items.append(item)
        else:
            coll_list_items.append(html.Div("No collectives.", style=LABEL_MUTED | {"margin": "4px 0 0 8px", "fontSize": "11px"}))

        if is_active:
            # Branch based on the current state / selection.
            new_coll_btn = html.Button(
                "+ New Collective",
                id={'type': 'new-collective-btn', 'index': tid},
                n_clicks=0,
                style={"marginTop": "8px", "width": "100%", "fontSize": "12px", "padding": "6px", "background": "#f1f8ff", "border": "1px dashed #0969da", "color": "#0969da", "cursor": "pointer", "borderRadius": "6px"}
            )
            coll_list_items.append(new_coll_btn)

        group_children = [header]
        if action_deck: group_children.append(action_deck)
        group_children.append(html.Div(coll_list_items, style={"padding": "0 4px 8px 4px"}))

        children.append(html.Div(style={"marginBottom": "12px"}, children=group_children))

    return children


# --- A. Navigation to Topology Page ---
# --- A. Navigation to Topology Page ---
@app.callback(
    Output("active-panel", "data", allow_duplicate=True),
    Output("editing-topology-id", "data", allow_duplicate=True),
    Input({'type': 'topo-details-btn', 'index': ALL}, "n_clicks"),
    prevent_initial_call=True
)
def nav_topology_page(n_details):
    # IMPORTANT: Only navigate on a *real click*.
    # Dash can trigger this callback when pattern-matching buttons are created/remounted
    # (n_clicks = 0/None). If we don't ignore that, the UI "snaps" into topology page.

    ctx = dash.callback_context
    if not ctx.triggered:
        raise PreventUpdate

    trig = ctx.triggered[0]
    prop_id = trig.get("prop_id", "")

    try:
        trig_id_str, trig_prop = prop_id.split(".", 1)
    except ValueError:
        raise PreventUpdate

    # Details button: only act on a real click (n_clicks > 0)
    try:
        trig_id = json.loads(trig_id_str)
    except Exception:
        raise PreventUpdate

    clicked_n = None
    for group in (getattr(ctx, "inputs_list", None) or []):
        if isinstance(group, list):
            for item in group:
                if item.get("id") == trig_id and item.get("property") == trig_prop:
                    clicked_n = item.get("value")
                    break
        elif isinstance(group, dict):
            if group.get("id") == trig_id and group.get("property") == trig_prop:
                clicked_n = group.get("value")
        if clicked_n is not None:
            break

    if not isinstance(clicked_n, (int, float)) or clicked_n <= 0:
        raise PreventUpdate

    tid = trig_id.get("index")
    if tid is None:
        raise PreventUpdate

    return "topology_details", tid


# --- B. Populate Topology Page ---
@app.callback(
    Output("topo-rename-input", "value"),
    Output("topo-details-header", "children"),
    Input("editing-topology-id", "data"),
    Input("multi-topos", "data"),
    prevent_initial_call=True
)
def populate_topo_page(tid, multi_topos):
    # Populate topology page.
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not tid or not multi_topos: raise PreventUpdate
    
    target = next((t for t in multi_topos if str(t["id"]) == str(tid)), None)
    if not target: return "", "Topology not found."
    
    header = f"Editing Topology: [{tid}] {target.get('label')}"
    return target.get('label'), header


# --- C. Rename Topology ---
@app.callback(
    Output("multi-topos", "data", allow_duplicate=True),
    Input("topo-rename-btn", "n_clicks"),
    State("topo-rename-input", "value"),
    State("editing-topology-id", "data"),
    State("multi-topos", "data"),
    prevent_initial_call=True
)
def rename_topology(n_save, new_name, tid, multi_topos):
    # Rename topology.
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not n_save or not new_name or not tid: raise PreventUpdate
    
    updated = False
    for t in (multi_topos or []):
        # Iterate over the relevant items and accumulate results.
        if str(t["id"]) == str(tid):
            # Branch based on the current state / selection.
            t["label"] = new_name
            updated = True
            break
    
    if updated: return multi_topos
    # Stop here to avoid updating outputs when the callback should not run yet.
    raise PreventUpdate


# --- D. Load Layout Preset (Updates Global State & Saved Layout) ---
@app.callback(
    Output("topo-layout-path", "value"),
    Input("topo-upload-layout", "contents"),
    State("topo-upload-layout", "filename"),
    prevent_initial_call=True
)
def handle_topo_layout_upload(contents, filename):
    # Load a topology file and rebuild all derived structures used for visualization and filtering.
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not contents or not filename: raise PreventUpdate
    try:
        content_type, content_string = contents.split(",")
        decoded = base64.b64decode(content_string)
        # Resolve and validate filesystem paths before using them.
        safe_name = os.path.basename(filename)
        # Resolve and validate filesystem paths before using them.
        out_path = os.path.join(UPLOAD_DIR, safe_name)
        with open(out_path, "wb") as f:
            # Open the file and ensure it is closed correctly.
            f.write(decoded)
        return out_path
    except:
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

@app.callback(
    Output("saved-layout", "data", allow_duplicate=True),
    Output("topo-layout-status", "children"),
    Input("topo-load-layout-btn", "n_clicks"),
    State("topo-layout-path", "value"),
    State("editing-topology-id", "data"),
    State("topology-radio", "value"), # Active ID
    prevent_initial_call=True
)
def load_topo_layout_preset(n_click, path, edit_id, active_id):
    # Load a topology file and rebuild all derived structures used for visualization and filtering.
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not n_click or not path or not edit_id: raise PreventUpdate
    
    try:
        # Resolve and validate filesystem paths before using them.
        p = os.path.expanduser(path)
        # Resolve and validate filesystem paths before using them.
        if not os.path.isabs(p): p = os.path.join(BASE_DIR, p)
        
        with open(p, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) or {}
            
        pos_map = data.get("positions", {})
        if not pos_map: return no_update, "Error: No positions in file."
        
        # 1. Update Persistent State for this topology
        # We must access the global TOPOLOGY_STATE cache since master_topology_switch reads from it.
        # Ensure the cache entry exists
        _get_or_create_topo_state(edit_id)
        if int(edit_id) in TOPOLOGY_STATE:
            # Branch based on the current state / selection.
            TOPOLOGY_STATE[int(edit_id)]["layout_data"] = {"positions": pos_map}
            TOPOLOGY_STATE[int(edit_id)]["layout_path"] = p

        # 2. If we are editing the ACTIVE topology, apply immediately to graph
        if str(edit_id) == str(active_id):
            # Branch based on the current state / selection.
            return {"positions": pos_map}, f"Loaded & Applied to Active Topology [{edit_id}]."
        
        return no_update, f"Loaded for Topology [{edit_id}]. Switch to it to see."
        
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return no_update, f"Failed: {e}"
  
    

@app.callback(
    Output("active-panel", "data", allow_duplicate=True),
    Output("editing-collective-id", "data", allow_duplicate=True),
    Input({'type': 'coll-details-btn', 'index': ALL, 'topo': ALL}, "n_clicks"),
    prevent_initial_call=True
)
def nav_collective_page(n_details):
    # Only navigate on explicit clicks; ignore remount/render triggers.

    ctx = dash.callback_context
    if not ctx.triggered:
        raise PreventUpdate

    trig = ctx.triggered[0]
    prop_id = trig.get("prop_id", "")

    try:
        trig_id_str, trig_prop = prop_id.split(".", 1)
    except ValueError:
        raise PreventUpdate
    # Coll Page button: only act on a real click (n_clicks > 0)
    try:
        trig_id = json.loads(trig_id_str)
    except Exception:
        raise PreventUpdate

    clicked_n = None
    for group in (getattr(ctx, "inputs_list", None) or []):
        if isinstance(group, list):
            for item in group:
                if item.get("id") == trig_id and item.get("property") == trig_prop:
                    clicked_n = item.get("value")
                    break
        elif isinstance(group, dict):
            if group.get("id") == trig_id and group.get("property") == trig_prop:
                clicked_n = group.get("value")
        if clicked_n is not None:
            break

    if not isinstance(clicked_n, (int, float)) or clicked_n <= 0:
        raise PreventUpdate

    cid = trig_id.get("index")
    if cid is None:
        raise PreventUpdate

    return "collective_details", cid



@app.callback(
    Output("topo-logs", "data", allow_duplicate=True),
    Input("coll-active-flow-param", "value"),
    Input("coll-active-data-param", "value"),
    State("editing-collective-id", "data"),
    State("topo-logs", "data"),
    prevent_initial_call= 'initial_duplicate'
)
def update_collective_active_params(flow_param, data_param, cid, topo_collectives):
    """
    Enforce single active parameter per category (flow/link vars and chunk/data vars) for a collective.
    We implement this by:
      - Storing explicit preferences: active_link_param / active_data_param on the collective
      - Updating hidden_params so all non-selected parameters are hidden from global menus/filters
    """
    if cid is None or topo_collectives is None:
        raise PreventUpdate

    # Normalize "none" while preserving whether the user explicitly chose it.
    raw_flow = flow_param
    raw_data = data_param
    explicit_none_flow = (raw_flow == "__none__")
    explicit_none_data = (raw_data == "__none__")

    if explicit_none_flow:
        flow_param = None
    if explicit_none_data:
        data_param = None

    # 1) Find the collective to update
    target_coll = None
    target_tid = None
    target_idx = -1

    for tid, col_list in topo_collectives.items():
        for i, coll in enumerate(col_list or []):
            if str(coll.get("id")) == str(cid):
                target_coll = coll
                target_tid = tid
                target_idx = i
                break
        if target_coll:
            break

    if not target_coll:
        raise PreventUpdate

    # 2) Re-scan logs for all parameters in this collective (and lazily load V if needed)
    all_flow = set()
    all_data = set()
    all_params = set()

    for log in (target_coll.get("logs", []) or []):
        lid = int(log.get("id"))
        V = MULTI_VIZ_OBJS.get(lid)

        if V is None:
            path = log.get("path")
            try:
                if str(path).lower().endswith(".json"):
                    V = JsonVisualizer(path, TOPO_FILE)
                else:
                    V = interactiveinfo.Visualizer(path, TOPO_FILE)
                MULTI_VIZ_OBJS[lid] = V
            except Exception:
                continue

        if not V:
            continue

        for lv in (getattr(V, "link_vars", []) or []):
            all_flow.add(lv.name)
            all_params.add(lv.name)
        for dv in (getattr(V, "data_vars", []) or []):
            all_data.add(dv.name)
            all_params.add(dv.name)

    # 3) Choose "effective" selections (guard against stale values)
    if (not explicit_none_flow) and (flow_param not in all_flow):
        flow_param = target_coll.get("active_link_param") if target_coll.get("active_link_param") in all_flow else None
    if (not explicit_none_data) and (data_param not in all_data):
        data_param = target_coll.get("active_data_param") if target_coll.get("active_data_param") in all_data else None

    # If nothing selected, fall back to the first visible candidate (if any) to keep UX stable.
    hidden_now = set(target_coll.get("hidden_params", []))
    if flow_param is None and all_flow and (not explicit_none_flow):
        candidates = [p for p in sorted(all_flow) if p not in hidden_now]
        if candidates:
            flow_param = candidates[0]
    if data_param is None and all_data and (not explicit_none_data):
        candidates = [p for p in sorted(all_data) if p not in hidden_now]
        if candidates:
            data_param = candidates[0]

    active_set = {p for p in (flow_param, data_param) if p}

    new_hidden = sorted(list(all_params - active_set))

    # 4) No-op guard
    if (
        set(target_coll.get("hidden_params", [])) == set(new_hidden)
        and target_coll.get("active_link_param") == flow_param
        and target_coll.get("active_data_param") == data_param
    ):
        raise PreventUpdate

    # 5) Persist
    target_coll["hidden_params"] = new_hidden
    target_coll["active_link_param"] = flow_param
    target_coll["active_data_param"] = data_param
    topo_collectives[target_tid][target_idx] = target_coll

    return topo_collectives



@app.callback(
    Output("avail-params", "data"),
    Output("param-select-dropdown", "options"),
    # If you have a separate filter dropdown "filter-param-dropdown", add it to Outputs here:
    # Output("filter-param-dropdown", "options"),
    Input("active-collectives-map", "data"),
    Input("topology-radio", "value"),     
    State("topo-logs", "data"), 
    prevent_initial_call=False
)
def update_available_params(active_coll_map, active_topo_id, topo_logs):
    # Update available params.
    if not active_topo_id: return [], []
    
    tid = str(active_topo_id)
    all_colls = (topo_logs or {}).get(tid, [])
    active_cids = set(int(x) for x in (active_coll_map or {}).get(tid, []))
    
    unique_params = {}

    for coll in all_colls:
        # Iterate over the relevant items and accumulate results.
        if int(coll["id"]) in active_cids:
            # Get hidden params for THIS collective
            hidden = set(coll.get("hidden_params", []))
            
            for log in coll.get("logs", []):
                # Iterate over the relevant items and accumulate results.
                lid = int(log["id"])
                V = MULTI_VIZ_OBJS.get(lid)
                if V is None: continue 
                
                # Scan viz params
                p_list = _get_viz_parameters(V)
                for p in p_list:
                    # ONLY add if not hidden
                    if p['value'] not in hidden:
                        # Validate inputs / state before continuing.
                        unique_params[p['value']] = p

    full_params = list(unique_params.values())
    dropdown_options = [{"label": p["label"], "value": p["value"]} for p in full_params]
    
    # If you added filter-param-dropdown to output, return dropdown_options twice
    return full_params, dropdown_options


@app.callback(
    Output("xy-x-select", "options"),
    Output("xy-x-select", "value"),
    Output("xy-y-select", "options"),
    Output("xy-y-select", "value"),
    Input("xy-mode-toggle", "value"),
    Input("avail-params", "data"),
    State("xy-x-select", "value"),
    State("xy-y-select", "value"),
    prevent_initial_call=False
)
def update_xy_dropdowns(mode, avail_params, cur_x, cur_y):
    # 1. DATA MODE (Legacy behavior)
    if mode == "data":
        # Keep current values if they exist in XY_OPTIONS, else reset
        valid_vals = set(o["value"] for o in XY_OPTIONS)
        new_x = cur_x if cur_x in valid_vals else "time"
        new_y = cur_y if cur_y in valid_vals else "postleft_avg"
        return XY_OPTIONS, new_x, XY_OPTIONS, new_y

    # 2. LINK MODE
    # X axis is almost always Time
    x_opts = [{"label": "Time (series)", "value": "time"}]
    
    # Y axis: Filter 'avail-params' for items where type='link'
    y_opts = []
    if avail_params:
        for p in avail_params:
            if p.get("type") == "link":
                label = p.get("label", p.get("value"))
                # Clean up label if needed (remove duplicates)
                if "(Link)" not in label: label += " (Total)"
                else: label = label.replace("(Link)", "(Total)")
                
                y_opts.append({"label": label, "value": p["value"]})
    
    if not y_opts:
        y_opts.append({"label": "No link vars found", "value": "none", "disabled": True})
    
    new_x = "time"
    # Try to preserve Y if it exists in new options, else pick first
    valid_y = set(o["value"] for o in y_opts)
    new_y = cur_y if cur_y in valid_y else (y_opts[0]["value"] if y_opts else None)

    return x_opts, new_x, y_opts, new_y



@app.callback(
    Output("xy-collectives-param-box-rows", "children"),
    Input("topology-radio", "value"),
    Input("active-collectives-map", "data"),
    Input("topo-logs", "data"),
    Input("xy-mode-toggle", "value"),
    prevent_initial_call=False
)
def render_xy_collective_param_box(active_topo_id, active_coll_map, topo_logs, xy_mode):
    """
    In the XY panel, show (per active collective):
      - a button that navigates to that collective's page
      - the *currently active* parameter for the selected metric type (data/link)

    Here, "active" is interpreted as: present in the collective's logs AND not hidden via hidden_params.
    If multiple are active, we show one plus a "+N more" indicator.
    """
    if not active_topo_id:
        return html.Div("No active topology.", style=LABEL_MUTED)

    tid = str(active_topo_id)

    # Which collectives are active in this topology?
    active_ids = set()
    for x in (active_coll_map or {}).get(tid, []):
        try:
            active_ids.add(int(x))
        except Exception:
            continue

    if not active_ids:
        return html.Div("No active collectives selected.", style=LABEL_MUTED)

    collectives = (topo_logs or {}).get(tid, []) or []

    def _active_param_for_coll(coll_obj, mode):
        hidden = set(coll_obj.get("hidden_params", []) or [])
        candidates = set()

        for lb in (coll_obj.get("logs", []) or []):
            try:
                lid = int(lb.get("id"))
            except Exception:
                continue

            V = MULTI_VIZ_OBJS.get(lid)
            if V is None:
                # Keep this lightweight; do not lazy-load here.
                continue

            if mode == "link":
                for lv in getattr(V, "link_vars", []) or []:
                    name = getattr(lv, "name", None)
                    if name and name not in hidden:
                        candidates.add(str(name))
            else:
                for dv in getattr(V, "data_vars", []) or []:
                    name = getattr(dv, "name", None)
                    if name and name not in hidden:
                        candidates.add(str(name))

        names = sorted(candidates)
        if not names:
            return "(no active link var)" if mode == "link" else "(no active data var)"

        # If the collective has an explicit remembered active param, prefer it.
        pref_key = "active_link_param" if mode == "link" else "active_data_param"
        pref = coll_obj.get(pref_key)
        if pref is not None and str(pref) in candidates:
            base = str(pref)
        else:
            base = names[0]

        if len(names) > 1:
            return f"{base} (+{len(names) - 1} more)"
        return base

    rows = []
    for coll in collectives:
        try:
            cid = int(coll.get("id"))
        except Exception:
            continue

        if cid not in active_ids:
            continue

        cname = coll.get("name") or f"Collective {cid}"
        param_txt = _active_param_for_coll(coll, xy_mode or "data")

        btn = html.Button(
            cname,
            id={"type": "coll-details-btn", "index": cid, "topo": f"xy-summary-{tid}"},
            n_clicks=0,
            title="Open Collective Page",
            style={
                "border": "1px solid #cfd8e3",
                "background": "#f8fafc",
                "padding": "4px 8px",
                "borderRadius": "6px",
                "cursor": "pointer",
                "fontWeight": 600,
                "marginRight": "10px"
            }
        )

        rows.append(
            html.Div(
                [
                    btn,
                    html.Span(
                        param_txt,
                        style={
                            "fontFamily": "monospace",
                            "fontSize": "12px",
                            "padding": "2px 6px",
                            "borderRadius": "999px",
                            "background": "#f1f5f9",
                            "border": "1px solid #e2e8f0",
                            "color": "#334155"
                        }
                    ),
                ],
                style={"display": "flex", "alignItems": "center", "gap": "6px", "marginBottom": "6px"}
            )
        )

    if not rows:
        return html.Div("No active collectives.", style=LABEL_MUTED)

    return rows

@app.callback(
    Output("coll-rename-input", "value"),
    Output("coll-details-header", "children"),
    Output("coll-flow-params-container", "children"),
    Output("coll-data-params-container", "children"),
    Input("editing-collective-id", "data"),
    Input("topo-logs", "data"),
    prevent_initial_call=True
)
def populate_collective_page(cid, topo_collectives):
    """Populate the Collective Page (rename + active parameter selection)."""
    if not cid or not topo_collectives:
        raise PreventUpdate

    # Find the collective object
    target_coll = None
    for _tid, col_list in topo_collectives.items():
        for coll in (col_list or []):
            if str(coll.get("id")) == str(cid):
                target_coll = coll
                break
        if target_coll:
            break

    if not target_coll:
        return (
            "",
            "Collective not found.",
            html.Div("No flow parameters.", style=LABEL_MUTED),
            html.Div("No chunk parameters.", style=LABEL_MUTED),
        )

    header = f"Editing: {target_coll.get('name', '')} (ID: {cid})"
    current_name = target_coll.get("name", "")

    logs = target_coll.get("logs", [])
    hidden_params = set(target_coll.get("hidden_params", []))

    flow_params = set()
    data_params = set()

    for log in (logs or []):
        lid = int(log.get("id"))
        V = MULTI_VIZ_OBJS.get(lid)

        # Lazy load if needed
        if V is None:
            path = log.get("path")
            try:
                if str(path).lower().endswith(".json"):
                    V = JsonVisualizer(path, TOPO_FILE)
                else:
                    V = interactiveinfo.Visualizer(path, TOPO_FILE)
                MULTI_VIZ_OBJS[lid] = V
            except Exception:
                continue

        if not V:
            continue

        for lv in (getattr(V, "link_vars", []) or []):
            flow_params.add(lv.name)
        for dv in (getattr(V, "data_vars", []) or []):
            data_params.add(dv.name)

    flow_list = sorted(flow_params)
    data_list = sorted(data_params)

    def _build_radio(component_id, options_list, preferred_value, preferred_key_present, hidden_set, empty_msg):
        # Always render a component with a stable id so callbacks remain valid, even when empty.
        base_style = {"display": "flex", "flexDirection": "column", "gap": "6px"}
    
        if not options_list:
            return html.Div([
                html.Div(empty_msg, style={"fontStyle": "italic", "color": "#999", "marginBottom": "6px"}),
                dcc.RadioItems(
                    id=component_id,
                    options=[{"label": " (none)", "value": "__none__", "disabled": True}],
                    value="__none__",
                    style=base_style,
                ),
            ])
    
        # If the key exists on the collective and is explicitly None, the user intentionally chose "(none)".
        explicit_none = preferred_key_present and preferred_value is None
    
        candidates = [p for p in options_list if p not in hidden_set]
        if explicit_none:
            chosen = None
        else:
            chosen = preferred_value if preferred_value in options_list else (candidates[0] if candidates else None)
    
        options = [{"label": " (none)", "value": "__none__"}] + [{"label": f" {p}", "value": p} for p in options_list]
        return dcc.RadioItems(
            id=component_id,
            options=options,
            value=chosen if chosen is not None else "__none__",
            style=base_style,
        )

    flow_ui = _build_radio(
        "coll-active-flow-param",
        flow_list,
        target_coll.get("active_link_param"),
        ("active_link_param" in target_coll),
        hidden_params,
        "No flow parameters found in this collective's logs.",
    )
    data_ui = _build_radio(
        "coll-active-data-param",
        data_list,
        target_coll.get("active_data_param"),
        ("active_data_param" in target_coll),
        hidden_params,
        "No chunk (data) parameters found in this collective's logs.",
    )

    return current_name, header, flow_ui, data_ui



@app.callback(
    Output("topo-logs", "data", allow_duplicate=True),
    Output("coll-rename-input", "value", allow_duplicate=True), # Just to confirm/sanitize
    Input("coll-rename-btn", "n_clicks"),
    State("coll-rename-input", "value"),
    State("editing-collective-id", "data"),
    State("topo-logs", "data"),
    State("target-collective-id", "data"),
    prevent_initial_call=True
)
def rename_collective(n_save, new_name, cid, topo_collectives):
    # Rename collective.
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not n_save or not new_name or not cid: raise PreventUpdate
    
    new_name = new_name.strip()
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not new_name: raise PreventUpdate

    updated = False
    
    # Deep copy or modify in place (State data is mutable dict usually)
    # We iterate to find and update
    for tid, col_list in topo_collectives.items():
        # Iterate over the relevant items and accumulate results.
        for coll in col_list:
            # Iterate over the relevant items and accumulate results.
            if str(coll["id"]) == str(cid):
                # Branch based on the current state / selection.
                coll["name"] = new_name
                updated = True
                break
        if updated: break
    
    if updated:
        # Branch based on the current state / selection.
        return topo_collectives, new_name
    
    # Stop here to avoid updating outputs when the callback should not run yet.
    raise PreventUpdate


@app.callback(
    Output("param-data-input-container", "style"),
    Input("param-select-dropdown", "value"),
    State("avail-params", "data"),
    prevent_initial_call=False
)
def toggle_data_id_input(param_name, all_params):
    # Toggle a UI feature/state and propagate the change to dependent components.
    if not param_name or not all_params:
        # Validate inputs / state before continuing.
        return {"display": "none", "marginTop": "12px"}
    
    # Find the type of the selected param
    p_type = "link"
    for p in all_params:
        # Iterate over the relevant items and accumulate results.
        if p["value"] == param_name:
            # Branch based on the current state / selection.
            p_type = p.get("type", "link")
            break
    
    if p_type == "data":
        # Branch based on the current state / selection.
        return {"display": "block", "marginTop": "12px"}
    
    return {"display": "none", "marginTop": "12px"}

@app.callback(
    Output("topo-logs", "data", allow_duplicate=True),
    Output("active-panel", "data", allow_duplicate=True),
    Output("target-collective-id", "data"),
    Input({'type': 'new-collective-btn', 'index': ALL}, "n_clicks"),
    Input({'type': 'coll-add-log-btn', 'index': ALL, 'topo': ALL}, "n_clicks"),
    State("topo-logs", "data"),
    State("target-collective-id", "data"),
    prevent_initial_call=True
)
def manage_collectives(n_new, n_add_log, topo_collectives, current_target_cid):
    ctx = dash.callback_context
    if not ctx.triggered:
        raise PreventUpdate

    # Identify exactly which component triggered (pattern-matching IDs are JSON)
    trig = ctx.triggered[0]                      # {"prop_id": "...", "value": ...}
    prop_id_str = trig.get("prop_id", "")
    trig_id_str, trig_prop = prop_id_str.split(".", 1)

    try:
        trig_id = json.loads(trig_id_str)
    except Exception:
        raise PreventUpdate

    if not isinstance(trig_id, dict):
        raise PreventUpdate

    # Find the triggered component’s *actual* n_clicks (not the full ALL list)
    clicked_n = None
    for group in (ctx.inputs_list or []):
        if isinstance(group, list):
            for entry in group:
                if entry.get("id") == trig_id and entry.get("property") == trig_prop:
                    clicked_n = entry.get("value")
                    break
        elif isinstance(group, dict):
            if group.get("id") == trig_id and group.get("property") == trig_prop:
                clicked_n = group.get("value")

        if clicked_n is not None:
            break

    # Critical: ignore re-render / creation triggers (n_clicks is 0/None)
    if not isinstance(clicked_n, (int, float)) or clicked_n <= 0:
        raise PreventUpdate

    topo_collectives = topo_collectives or {}
    btn_type = trig_id.get("type")

    # Only two ways to go to "+log":
    if btn_type == "new-collective-btn":
        tid = str(trig_id.get("index"))
        current_list = topo_collectives.get(tid, [])

        import time
        cid = int(time.time() * 1000)
        name = f"Collective {len(current_list) + 1}"

        current_list.append({"id": cid, "name": name, "active": True, "logs": [], "chunk_filter_ids": []})
        topo_collectives[tid] = current_list

        # IMPORTANT: creating a new collective should not reset the current collective UI state.
        # Keep the current target/panel unless we do not have a target yet.
        if current_target_cid is None:
            return topo_collectives, "logs", cid
        return topo_collectives, no_update, no_update

    if btn_type == "coll-add-log-btn":
        cid = trig_id.get("index")
        return no_update, "logs", cid

    raise PreventUpdate


@app.callback(
    Output("active-collectives-map", "data", allow_duplicate=True),
    Input({'type': 'coll-checklist', 'index': ALL, 'topo': ALL}, "value"),
    State("active-collectives-map", "data"),
    prevent_initial_call=True
)
def update_active_collectives(values, current_map):
    # Update active collectives.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not ctx.triggered: raise PreventUpdate
    
    # values is a list of lists because of ALL.
    # We need to find WHICH checklist triggered this.
    trigger = ctx.triggered[0]
    # Decode a JSON payload back into Python objects.
    prop = json.loads(trigger['prop_id'].split('.')[0])
    tid = str(prop['topo'])
    cid = prop['index']
    val_list = trigger['value'] # [cid] or []
    
    current_map = current_map or {}
    actives = set(current_map.get(tid, []))
    
    if val_list:
        # Branch based on the current state / selection.
        actives.add(cid)
    else:
        if cid in actives: actives.remove(cid)
        
    current_map[tid] = list(actives)
    return current_map

@app.callback(
    Output("active-panel", "data", allow_duplicate=True),
    Output("filters-submode", "data", allow_duplicate=True),
    Input({'type': 'topo-action-btn', 'index': ALL, 'action': ALL}, "n_clicks"),
    prevent_initial_call=True
)
def handle_topology_actions(n_clicks_list):
    # Handle topology actions.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    if not ctx.triggered:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    # 1. Get the trigger info
    triggered_str = ctx.triggered[0]['prop_id']
    triggered_value = ctx.triggered[0]['value']

    # 2. CRITICAL FIX: Ignore if n_clicks is 0 or None
    # When the topology list is re-rendered (e.g., loading a log), buttons are re-created 
    # with n_clicks=0. We must ignore these "creation" triggers.
    if not triggered_value:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    try:
        import json
        # Decode a JSON payload back into Python objects.
        prop_id_json = json.loads(triggered_str.split(".")[0])
        action = prop_id_json.get("action")
    except Exception:
        # Recover from a failure case and return a safe default.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    # 3. Routing Logic (Only runs on real clicks)
    if action == "coloring":
        # Branch based on the current state / selection.
        return "param_coloring", "links"
    elif action == "filters":
        # Alternative branch for a different condition.
        return "param_filters", "links"

    return no_update, no_update
    
@app.callback(
    Output("groups-status", "children", allow_duplicate=True),
    Input("group-delete-btn", "n_clicks"),
    State("group-select", "value"),
    prevent_initial_call=True
)
def delete_group(_n, name):
    # Delete group.
    if not name:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    try:
        with open(GROUPS_FILE, "r") as f:
            # Open the file and ensure it is closed correctly.
            data = json.load(f) or {"groups": {}}
        groups = data.get("groups", {})
        if name not in groups:
            # Validate inputs / state before continuing.
            return f"Group '{name}' not found."
        del groups[name]
        data["groups"] = groups
        _atomic_json_write(GROUPS_FILE, data)
        return f"Deleted group '{name}'. Click Refresh to update the list."
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return f"Failed to delete group: {e}"

@app.callback(
    Output("group-selected-name", "children"),
    Input("group-select", "value"),
    prevent_initial_call=False
)
def show_selected_group(name):
    # Show selected group.
    if not name:
        # Validate inputs / state before continuing.
        return ""
    return f"Selected group: {name}"

# --- 1. Populate Filter Dropdown (Reuse existing logic) ---
@app.callback(
    Output("filter-param-dropdown", "options"),
    Input("avail-params", "data"),
    prevent_initial_call=False
)
def update_filter_dropdown_options(params):
    # params is list of {label, value, type}
    # Apply the current filter settings and compute the resulting subset for display.
    if not params: return []
    return [{"label": p["label"], "value": p["value"]} for p in params]

# --- 2. Update Slider Range when Parameter Selected ---

# --- 1b. Show chunk filter controls inside Parameter Filters when the selected parameter is a DataVar ---
@app.callback(
    Output("paramfilter-chunk-filter-container", "style"),
    Input("filter-param-dropdown", "value"),
    State("avail-params", "data"),
    prevent_initial_call=False
)
def toggle_paramfilter_chunk_filter_container(param_name, all_params):
    # Show the chunk filter UI only when filtering by a DataVar.
    if not param_name or not all_params:
        return {"display": "none", "marginTop": "14px", "paddingTop": "12px", "borderTop": "1px solid #e1e7ef"}

    p_type = "link"
    for p in (all_params or []):
        try:
            if p.get("value") == param_name:
                p_type = p.get("type", "link")
                break
        except Exception:
            continue

    if p_type == "data":
        return {"display": "block", "marginTop": "14px", "paddingTop": "12px", "borderTop": "1px solid #e1e7ef"}

    return {"display": "none", "marginTop": "14px", "paddingTop": "12px", "borderTop": "1px solid #e1e7ef"}

@app.callback(
    Output("filter-param-slider", "min"),
    Output("filter-param-slider", "max"),
    Output("filter-param-slider", "value"),
    Output("filter-param-slider", "step"),
    Input("filter-param-dropdown", "value"),
    Input("segment-range", "value"),
    Input("active-collectives-map", "data"),
    Input("topology-radio", "value"),
    State("topo-logs", "data"),
    prevent_initial_call=True
)
def update_filter_slider(param_name, seg, active_coll_map, active_topo_id, topo_logs):
    # Update the slider bounds based on the selected parameter and current segment.
    if not param_name:
        return 0, 100, [0, 100], 1

    t0, t1 = (seg or [TIME_MIN, TIME_MAX])

    # Prefer active collectives; fall back to the global single-log VIZ if needed.
    viz_list = _get_active_viz_list(active_coll_map, active_topo_id, topo_logs)
    if not viz_list and VIZ is not None:
        viz_list = [VIZ]

    result = _aggregate_param_values(param_name, float(t0), float(t1), None, viz_list)
    if not result:
        return 0, 100, [0, 100], 1

    vals = []
    if result.get("type") == "link":
        vals = list((result.get("data") or {}).values())
    elif result.get("type") == "data" and result.get("mode") == "counts":
        vals = list((result.get("node_counts") or {}).values()) + list((result.get("link_counts") or {}).values())

    if not vals:
        return 0, 100, [0, 100], 1

    is_counts = (result.get("type") == "data" and result.get("mode") == "counts")

    try:
        if is_counts:
            vmin = 0
            vmax = int(max(vals))
        else:
            vmin = float(min(vals))
            vmax = float(max(vals))
    except Exception:
        return 0, 100, [0, 100], 1

    if vmax <= vmin:
        vmax = vmin + (1 if is_counts else 1.0)

    if is_counts:
        step = 1
        return float(vmin), float(vmax), [float(vmin), float(vmax)], step

    step = (vmax - vmin) / 100.0
    return vmin, vmax, [vmin, vmax], step

# --- 3. Store the Active Filter ---
@app.callback(
    Output("param-filter-store", "data"),
    Output("filter-status-msg", "children"),
    Input("apply-param-filter", "n_clicks"),
    Input("clear-param-filter", "n_clicks"),
    State("filter-param-dropdown", "value"),
    State("filter-param-slider", "value"),
    prevent_initial_call=True
)
def set_active_filter(n_apply, n_clear, param, rng):
    # Apply the current filter settings and compute the resulting subset for display.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not ctx.triggered: raise PreventUpdate
    which = ctx.triggered[0]["prop_id"].split(".")[0]
    
    if which == "clear-param-filter":
        # Branch based on the current state / selection.
        return None, "Filter cleared."
    
    if not param or not rng:
        # Validate inputs / state before continuing.
        return no_update, "Select a parameter and range first."
        
    return {"name": param, "min": rng[0], "max": rng[1]}, f"Filter active: {param} [{rng[0]:.2f} - {rng[1]:.2f}]"

# --- 4. Apply Filter to Graph (Update style_edges) ---
# Update your EXISTING style_edges callback to accept param-filter-store
@app.callback(
    Output("network-graph", "stylesheet"),
    Input("cap-range", "value"),
    Input("color-mode", "data"),
    Input("segment-range", "value"),
    Input("edge-types", "value"),
    Input("elements-base", "data"),
    Input("highlight-chunk-links", "data"),
    Input("param-values", "data"),       
    Input("param-filter-store", "data"),
    Input("active-collectives-map", "data"), # CHANGED
    Input("topology-radio", "value"),    
    State("topo-logs", "data"),
    prevent_initial_call=True,
)
def style_edges(cap_range, color_mode, seg_range, selected_types, elements, chunk_link_hi, param_data, param_filter, active_coll_map, active_topo_id, topo_logs):
    
    
    # Style edges.
    styles = list(BASE_STYLESHEET)

    # Build a set of directed edges present in the current Cytoscape elements.
    # Needed because logs may report a traversal as (src,dst) while the loaded topology
    # stores the same physical link in the opposite orientation.
    edge_pairs = set()
    for _el in (elements or []):
        try:
            _d = _el.get("data", {})
            if "source" in _d and "target" in _d:
                edge_pairs.add((str(_d.get("source")), str(_d.get("target"))))
        except Exception:
            pass

    # ... (Filter types logic is same) ...
    all_types = {"etype-host-host", "etype-switch-switch", "etype-host-switch"}
    selected = set(selected_types or all_types)
    for t in (all_types - selected):
        # Iterate over the relevant items and accumulate results.
        styles.append({"selector": f"edge.{t}", "style": {"display": "none"}})

    # Parameter Filter
    if param_filter and param_filter.get("name"):
        # Branch based on the current state / selection.
        fname = param_filter["name"]
        fmin = param_filter["min"]
        fmax = param_filter["max"]
        t0, t1 = (seg_range or [TIME_MIN, TIME_MAX])
        
        # Use new helper
        viz_list = _get_active_viz_list(active_coll_map, active_topo_id, topo_logs)
        if not viz_list and VIZ is not None:
            viz_list = [VIZ]
        filter_vals = _aggregate_param_values(fname, float(t0), float(t1), None, viz_list)
        
        if filter_vals:
            ftype = filter_vals.get("type")

            # LinkVar filter: hide edges whose average value is outside [fmin, fmax].
            if ftype == "link":
                data_map = filter_vals.get("data") or {}
                for el in (elements or []):
                    d = el.get("data", {})
                    src, dst = str(d.get("source")), str(d.get("target"))
                    if not src or not dst:
                        continue
                    key = f"{src}-{dst}"
                    val = data_map.get(key)
                    if val is None:
                        val = data_map.get(f"{dst}-{src}", None)
                    if val is None:
                        continue
                    try:
                        vv = float(val)
                    except Exception:
                        continue
                    if vv < float(fmin) or vv > float(fmax):
                        styles.append({
                            "selector": f'edge[source="{src}"][target="{dst}"]',
                            "style": {"display": "none"}
                        })

            # DataVar filter (mode='counts'): hide BOTH nodes and edges whose DISTINCT chunk count
            # in the current segment is outside [fmin, fmax].
            elif ftype == "data" and filter_vals.get("mode") == "counts":
                node_map = filter_vals.get("node_counts") or {}
                link_map = filter_vals.get("link_counts") or {}

                # Nodes
                for el in (elements or []):
                    d = el.get("data", {})
                    nid = d.get("id")
                    if nid is None:
                        continue
                    if "source" in d or "target" in d:
                        continue
                    k = str(nid)
                    try:
                        cnt = float(node_map.get(k, 0))
                    except Exception:
                        cnt = 0.0
                    if cnt < float(fmin) or cnt > float(fmax):
                        styles.append({
                            "selector": f'node[id="{k}"]',
                            "style": {"display": "none"}
                        })

                # Edges
                for el in (elements or []):
                    d = el.get("data", {})
                    src, dst = d.get("source"), d.get("target")
                    if src is None or dst is None:
                        continue
                    src_s, dst_s = str(src), str(dst)
                    key = f"{src_s}-{dst_s}"
                    val = link_map.get(key)
                    if val is None:
                        val = link_map.get(f"{dst_s}-{src_s}", 0)
                    try:
                        cnt = float(val)
                    except Exception:
                        cnt = 0.0
                    if cnt < float(fmin) or cnt > float(fmax):
                        styles.append({
                            "selector": f'edge[source="{src_s}"][target="{dst_s}"]',
                            "style": {"display": "none"}
                        })
# ... (Coloring/Highlight logic is same) ...
    if color_mode == "parameter" and param_data:
        # Branch based on the current state / selection.
        p_type = param_data.get("type")
        if p_type == "link":
            # Branch based on the current state / selection.
            data_map = param_data.get("data", {})
            vmin = param_data.get("min", 0)
            vmax = param_data.get("max", 1)
            for key, val in data_map.items():
                # Iterate over the relevant items and accumulate results.
                try:
                    src, dst = key.split("-")
                    if (src, dst) not in edge_pairs and (dst, src) in edge_pairs:
                        src, dst = dst, src
                    color = _flow_color_scale(val, vmin, vmax)
                    styles.append({
                        "selector": f'edge[source = "{src}"][target = "{dst}"]',
                        "style": {"line-color": color}
                    })
                except: pass
        elif p_type == "data":
            # Alternative branch for a different condition.
            nodes = set(map(str, param_data.get("nodes", [])))
            for nid in nodes:
                # Iterate over the relevant items and accumulate results.
                styles.append({
                    "selector": f'node[id = "{nid}"]',
                    "style": {"border-width": 6, "border-color": "#ff00bf", "background-color": "#ff00bf"}
                })
            links = param_data.get("links", [])
            t_min = float(param_data.get("t_min", 0))
            t_max = float(param_data.get("t_max", 1))
            span = max(t_max - t_min, 1e-9)
            for l in links:
                # Iterate over the relevant items and accumulate results.
                src, dst = str(l["src"]), str(l["dst"])

                if (src, dst) not in edge_pairs and (dst, src) in edge_pairs:

                    src, dst = dst, src
                t_end = float(l["t_end"])
                x = max(0.0, min(1.0, (t_end - t_min) / span))
                r = int(round(255 * x))
                g = int(round(255 * (1.0 - x)))
                styles.append({
                    "selector": f'edge[source = "{src}"][target = "{dst}"]',
                    "style": {"line-color": f"rgb({r},{g},0)", "width": 4}
                })

    elif color_mode in ("flow", "flow_frac"):
        # Alternative branch for a different condition.
        seg0, seg1 = 0.0, 100.0
        if seg_range and len(seg_range) == 2:
            # Branch based on the current state / selection.
            seg0, seg1 = float(seg_range[0]), float(seg_range[1])
        if seg1 <= seg0: seg1 = seg0 + 1e-9

        # Use new helper
        viz_list = _get_active_viz_list(active_coll_map, active_topo_id, topo_logs)
        
        vals = {}
        counts = {}
        use_ratio = (color_mode == "flow_frac")

        if viz_list:
            # Branch based on the current state / selection.
            for v in viz_list:
                # Iterate over the relevant items and accumulate results.
                lv_list = getattr(v, "link_vars", [])
                if not lv_list: continue
                link_var = lv_list[0]
                per_link = getattr(link_var, "per_link", {})
                
                for el in (elements or []):
                    # Iterate over the relevant items and accumulate results.
                    d = el.get("data", {})
                    if "source" not in d: continue
                    try:
                        src, dst = int(d["source"]), int(d["target"])
                        series = per_link.get((src, dst)) or per_link.get((dst, src))
                        if not series: continue
                        avg = _avg_series_on_segment(series, seg0, seg1)
                        if avg <= 0.0: continue
                        
                        key = (src, dst)
                        vals[key] = vals.get(key, 0.0) + avg
                        counts[key] = counts.get(key, 0) + 1
                    except: pass

            final_vals = {}
            for k, total in vals.items():
                # Iterate over the relevant items and accumulate results.
                avg = total / counts[k]
                final_vals[k] = avg

            if final_vals:
                # Branch based on the current state / selection.
                vm, vx = min(final_vals.values()), max(final_vals.values())
                for (s, d), v in final_vals.items():
                    # Iterate over the relevant items and accumulate results.
                    color = _flow_color_scale(v, vm, vx)
                    styles.append({
                        "selector": f'edge[source = "{s}"][target = "{d}"]',
                        "style": {"line-color": color}
                    })

    elif color_mode in ("capacity", "latency"):
        # ... (same) ...
        attr = color_mode
        vals = [float(el["data"].get(attr)) for el in (elements or []) 
                if "data" in el and attr in el["data"] and str(el["data"].get(attr)) != "nan"]
        vmin, vmax = (min(vals), max(vals)) if vals else (0.0, 1.0)
        styles.append({
            "selector": "edge",
            "style": {"line-color": f"mapData({attr}, {vmin}, {vmax}, #e63946, #2a9d8f)"}
        })

    # ... (highlights same) ...
    if chunk_link_hi:
        # Branch based on the current state / selection.
        for it in chunk_link_hi:
            # Iterate over the relevant items and accumulate results.
            try:
                src = str(it.get("src"))
                dst = str(it.get("dst"))
            except Exception:
                continue
            if (src, dst) not in edge_pairs and (dst, src) in edge_pairs:
                src, dst = dst, src
            styles.append({
                "selector": f'edge[source = "{src}"][target = "{dst}"]',
                "style": {"line-color": it["color"], "width": 5, "opacity": 1.0}
            })

    styles.append({"selector": ".has-chunk", "style": {"border-width": 5, "border-color": "#ff00bf"}})
    styles.append({"selector": ".thresh-chunks", "style": {"border-width": 6, "border-color": "#00c853"}})
    styles.append({"selector": ".thresh-postleft", "style": {"border-width": 6, "border-color": "#ff1744"}})

    return styles

# =========================
# Chunk filter + presence + events (segment-aware)
# =========================
@app.callback(
    Output("chunk-filter-ids", "data", allow_duplicate=True),
    Output("chunk-filter-status", "children", allow_duplicate=True),
    Output("pf-chunk-filter-status", "children", allow_duplicate=True),
    Output("topo-logs", "data", allow_duplicate=True),
    Input("apply-chunk-filter", "n_clicks"),
    Input("chunk-add-range-btn", "n_clicks"),
    Input("clear-chunk-filter", "n_clicks"),
    Input("pf-apply-chunk-filter", "n_clicks"),
    Input("pf-chunk-add-range-btn", "n_clicks"),
    Input("pf-clear-chunk-filter", "n_clicks"),
    State("chunk-filter-text", "value"),
    State("chunk-range-start", "value"),
    State("chunk-range-end", "value"),
    State("chunk-range-step", "value"),
    State("chunk-min-nodes", "value"),
    State("pf-chunk-filter-text", "value"),
    State("pf-chunk-range-start", "value"),
    State("pf-chunk-range-end", "value"),
    State("pf-chunk-range-step", "value"),
    State("pf-chunk-min-nodes", "value"),
    State("segment-range", "value"),
    State("chunk-filter-ids", "data"),
    State("target-collective-id", "data"),
    State("topology-radio", "value"),
    State("topo-logs", "data"),
    prevent_initial_call=True
)
def chunk_filter_actions(
    n_apply, n_add, n_clear,
    n_pf_apply, n_pf_add, n_pf_clear,
    spec, r_start, r_end, r_step, min_nodes,
    pf_spec, pf_r_start, pf_r_end, pf_r_step, pf_min_nodes,
    seg, current_ids,
    target_cid, active_tid, topo_collectives
):
    # Apply the current filter settings and compute the resulting subset for display.
    ctx = dash.callback_context
    if not ctx.triggered:
        raise PreventUpdate

    which = ctx.triggered[0]["prop_id"].split(".")[0]

    # Choose which input-set to use (main Chunk Filters panel vs Parameter Filters panel)
    use_pf = which.startswith("pf-")
    spec_in = (pf_spec if use_pf else spec) or ""
    r_start_in = pf_r_start if use_pf else r_start
    r_end_in = pf_r_end if use_pf else r_end
    r_step_in = pf_r_step if use_pf else r_step
    min_nodes_in = pf_min_nodes if use_pf else min_nodes

    cur = set(map(int, current_ids or []))

    # Helper: persist per-collective chunk filter selection (best-effort)
    def _persist(ids_list):
        if not topo_collectives or not active_tid or not target_cid:
            return no_update
        tid = str(active_tid)
        cols = list((topo_collectives or {}).get(tid, []) or [])
        changed = False
        for c in cols:
            if str(c.get("id")) == str(target_cid):
                c["chunk_filter_ids"] = [int(x) for x in (ids_list or [])]
                changed = True
                break
        if not changed:
            return no_update
        out = dict(topo_collectives or {})
        out[tid] = cols
        return out

    # Decide candidate chunks
    if which in ("apply-chunk-filter", "pf-apply-chunk-filter"):
        ids = _parse_num_spec(spec_in)
        try:
            total = int(getattr(VIZ, "chunkCount", 0) or 0)
        except Exception:
            total = 0
        candidates = sorted(set(ids)) if ids else list(range(total))

    elif which in ("chunk-add-range-btn", "pf-chunk-add-range-btn"):
        try:
            start = int(r_start_in)
            end = int(r_end_in)
            step = int(r_step_in if r_step_in not in (None, 0, "") else 1)
            if step == 0:
                step = 1
            if start <= end:
                rng = list(range(start, end + 1, abs(step)))
            else:
                rng = list(range(start, end - 1, -abs(step)))
            cur |= set(int(i) for i in rng)
            candidates = sorted(cur)
        except Exception:
            msg = "Invalid range parameters."
            return no_update, msg, msg, no_update

    elif which in ("clear-chunk-filter", "pf-clear-chunk-filter"):
        msg = "Cleared chunk filter."
        return [], msg, msg, _persist([])

    else:
        candidates = sorted(cur)

    # Optional: enforce a minimum number of nodes that have the chunk at t_end
    t1 = float((seg or [TIME_MIN, TIME_MAX])[1])
    threshold = 0 if min_nodes_in in (None, "") else max(0, int(min_nodes_in))

    if threshold > 0 and VIZ is not None:
        keep = []
        for cid in candidates:
            try:
                have, _ = _nodes_with_chunk_by_time(cid, t1)
                if len(have) >= threshold:
                    keep.append(cid)
            except Exception:
                pass
        out_ids = sorted(keep)
        msg = f"Applied chunk filter with min nodes ≥ {threshold}: {len(out_ids)} chunk(s)."
    else:
        out_ids = sorted(candidates)
        msg = f"Applied chunk filter: {len(out_ids)} chunk(s)."

    return out_ids, msg, msg, _persist(out_ids)


# --- Per-collective persistence: load the targeted collective's chunk filter into the global store ---
@app.callback(
    Output("chunk-filter-ids", "data", allow_duplicate=True),
    Output("chunk-filter-status", "children", allow_duplicate=True),
    Output("pf-chunk-filter-status", "children", allow_duplicate=True),
    Input("target-collective-id", "data"),
    Input("topology-radio", "value"),
    State("topo-logs", "data"),
    prevent_initial_call="initial_duplicate"
)
def sync_chunk_filter_for_target(target_cid, active_tid, topo_collectives):
    if not active_tid or not target_cid:
        return no_update, "", ""
    tid = str(active_tid)
    cols = (topo_collectives or {}).get(tid, []) or []
    for c in cols:
        if str(c.get("id")) == str(target_cid):
            ids = c.get("chunk_filter_ids") or []
            msg = f"Loaded chunk filter: {len(ids)} chunk(s)." if ids else "No chunk filter."
            return [int(x) for x in ids], msg, msg
    # If the target is not part of this topology, clear the filter
    return [], "No chunk filter.", "No chunk filter."


@app.callback(
    Output("topo-states", "data", allow_duplicate=True),
    State("multi-logs", "data"),
    State("multi-logs-include", "data"), # CHANGED
    Input("saved-layout", "data"),
    Input("file-path", "data"),
    State("topology-radio", "value"),
    State("topo-states", "data"),
    prevent_initial_call=True
)
def save_topo_state(current_logs, include_ids, current_layout, current_path, active_topo_id, states):
    # Save topology state.
    if active_topo_id is None:
        # Validate inputs / state before continuing.
        return no_update
    states = states or {}
    tid = str(active_topo_id)
    states[tid] = {
        "logs": current_logs or [],
        "include": include_ids or [],
        "layout": current_layout,
        "path": current_path
    }
    return states

@app.callback(
    Output("highlight-chunk-links", "data", allow_duplicate=True),
    Input("chunk-id", "value"),
    Input("segment-range", "value"),
    State("chunk-filter-ids", "data"),
    State("multi-logs", "data"),
    State("multi-logs-include", "data"), # CHANGED
    prevent_initial_call=True,
)
def set_chunk_link_highlights(chunk_id, seg, allowed_chunks, multi_logs, include_ids):
    # ... rest of function remains identical ...
    # No chunk selected → clear highlights
    # Set chunk link highlights.
    if chunk_id is None:
        # Validate inputs / state before continuing.
        return []

    try:
        cid = int(chunk_id)
    except (TypeError, ValueError):
        # Recover from a failure case and return a safe default.
        return []

    # Respect chunk filter
    if allowed_chunks and cid not in set(map(int, allowed_chunks)):
        # Validate inputs / state before continuing.
        return []

    # Time segment
    try:
        t0, t1 = (seg or [TIME_MIN, TIME_MAX])
        t0 = float(t0)
        t1 = float(t1)
    except Exception:
        # Recover from a failure case and return a safe default.
        t0, t1 = float(TIME_MIN), float(TIME_MAX)

    if t1 < t0:
        # Branch based on the current state / selection.
        t0, t1 = t1, t0

    # Pick the active log (multi-log or main)
    Vsel = _active_viz_from_multi(multi_logs, include_ids)

    with _use_viz(Vsel):
        # Use a context manager to manage resources safely.
        V = VIZ
        DV = getattr(V, "primary_data", None) if V is not None else None
        if DV is None:
            # Validate inputs / state before continuing.
            return []

        # DataVar must have links_for_chunk_in_segment
        try:
            links = DV.links_for_chunk_in_segment(cid, t0, t1)
        except Exception:
            # Recover from a failure case and return a safe default.
            return []

    if not links:
        # Validate inputs / state before continuing.
        return []

    # Map t_end → color (earlier = green, later = red)
    t_ends = [float(it["t_end"]) for it in links]
    t_min = min(t_ends)
    t_max = max(t_ends)
    span = max(t_max - t_min, 1e-9)

    def _color_for(t_end):
        # Color for.
        x = (float(t_end) - t_min) / span  # 0..1
        if x < 0.0:
            # Branch based on the current state / selection.
            x = 0.0
        if x > 1.0:
            # Branch based on the current state / selection.
            x = 1.0
        r = int(round(255 * x))
        g = int(round(255 * (1.0 - x)))
        return f"rgb({r},{g},0)"  # early = green, late = red

    out = []
    for it in links:
        # Iterate over the relevant items and accumulate results.
        try:
            src = int(it["src"])
            dst = int(it["dst"])
        except Exception:
            # Recover from a failure case and return a safe default.
            continue
        col = _color_for(it["t_end"])
        out.append({"src": src, "dst": dst, "color": col})

    # Format: list of {src, dst, color} used by the stylesheet callback
    return out

@app.callback(
    Output("chunk-presence", "data", allow_duplicate=True),
    Output("chunk-status", "children"),
    Input("chunk-id", "value"),
    Input("segment-range", "value"),
    State("chunk-filter-ids", "data"),
    State("multi-logs", "data"),
    State("multi-logs-include", "data"), # CHANGED
    prevent_initial_call=True
)
def set_chunk_presence(chunk_id, seg, allowed_chunks, multi_logs, include_ids):
    # Set chunk presence.
    if chunk_id is None:
        # Validate inputs / state before continuing.
        return None, ""
    if allowed_chunks and int(chunk_id) not in set(map(int, allowed_chunks)):
        # Validate inputs / state before continuing.
        return None, f"Chunk {int(chunk_id)} is filtered out."
    Vsel = _active_viz_from_multi(multi_logs, include_ids)
    with _use_viz(Vsel):
        # Use a context manager to manage resources safely.
        t0, t1 = (seg or [TIME_MIN, TIME_MAX])
        have_nodes, msg = _nodes_with_chunk_in_segment(chunk_id, t0, t1)
        if not have_nodes and VIZ is None:
            # Validate inputs / state before continuing.
            return None, msg
        return {"chunk": int(chunk_id), "time0": float(t0), "time1": float(t1), "nodes": sorted(list(have_nodes))}, msg

@app.callback(
    Output("chunk-events", "data", allow_duplicate=True),
    Output("chunk-event-info", "children"),
    Input("chunk-id", "value"),
    Input("segment-range", "value"),
    Input("network-graph", "selectedNodeData"),
    State("chunk-filter-ids", "data"),
    State("multi-logs", "data"),
    State("multi-logs-include", "data"), # CHANGED
    prevent_initial_call=True
)
def compute_chunk_events(chunk_id, seg, selectedNodeData, allowed_chunks, multi_logs, include_ids):
    # Compute chunk events.
    if chunk_id is None:
        # Validate inputs / state before continuing.
        return {"events": []}, ""
    if allowed_chunks and int(chunk_id) not in set(map(int, allowed_chunks)):
        # Validate inputs / state before continuing.
        return {"events": []}, "Chunk is filtered out."
    sel_set = set()
    for d in (selectedNodeData or []):
        # Iterate over the relevant items and accumulate results.
        try:
            sel_set.add(int(d.get("id")))
        except Exception:
            # Recover from a failure case and return a safe default.
            pass
    Vsel = _active_viz_from_multi(multi_logs, include_ids)
    with _use_viz(Vsel):
        # Use a context manager to manage resources safely.
        t0, t1 = (seg or [TIME_MIN, TIME_MAX])
        events = [ev for ev in _chunk_events_list(chunk_id) if float(t0) <= float(ev["time"]) <= float(t1)]
        if sel_set:
            # Branch based on the current state / selection.
            ev2 = []
            for ev in events:
                # Iterate over the relevant items and accumulate results.
                nodes = ev.get("nodes") or ev.get("ranks") or []
                filt = [n for n in nodes if n in sel_set]
                if filt:
                    # Branch based on the current state / selection.
                    ev2.append({"time": ev["time"], "nodes": filt})
            events = ev2 or events
        if not events:
            # Validate inputs / state before continuing.
            return {"events": []}, "(no events in segment)"
        pretty = "\n".join(f"t={e['time']:.3f}: {e.get('nodes') or e.get('chunks')}" for e in events[:200])
        return {"events": events}, html.Pre(pretty, style={"whiteSpace":"pre-wrap", "margin": 0})

@app.callback(
    Output("node-contents", "data", allow_duplicate=True),
    Output("node-status", "children"),
    Output("node-chunk-list", "children"),
    Input("node-id", "value"),
    Input("segment-range", "value"),
    Input("chunk-filter-ids", "data"), 
    State("chunk-filter-ids", "data"),
    State("multi-logs", "data"),
    State("multi-logs-include", "data"), # CHANGED
    prevent_initial_call=True
)
def set_node_contents(node_id, seg, _trigger_chunks_change, allowed_chunks, multi_logs, include_ids):
    # Set node contents.
    if node_id is None:
        # Validate inputs / state before continuing.
        return None, "", ""
    Vsel = _active_viz_from_multi(multi_logs, include_ids)
    with _use_viz(Vsel):
        # Use a context manager to manage resources safely.
        t0, t1 = (seg or [TIME_MIN, TIME_MAX])
        chunks, msg = _chunks_on_node_in_segment(node_id, t0, t1)
        if allowed_chunks:
            # Branch based on the current state / selection.
            allowed = set(map(int, allowed_chunks))
            chunks = [c for c in chunks if c in allowed]
        data = {"node": int(node_id), "time0": float(t0), "time1": float(t1), "chunks": chunks, "count": len(chunks)}
        if chunks:
            # Branch based on the current state / selection.
            shown = chunks[:200]; more = len(chunks) - len(shown)
            pretty = ", ".join(map(str, shown)) + (f" … (+{more} more)" if more > 0 else "")
            list_view = html.Pre(pretty, style={"whiteSpace": "pre-wrap", "margin": 0})
        else:
            list_view = html.Div("(none)")
        return data, msg, list_view

# Toggle LEFT panel open/closed
@app.callback(
    Output("left-panel-open", "data"),
    Input("toggle-left-panel", "n_clicks"),
    State("left-panel-open", "data"),
    prevent_initial_call=True,
)
def toggle_left_panel_state(n_clicks, is_open):
    # Update the viewport pan/translation for the network graph.
    if n_clicks is None:
        # Guard: only run after the user triggers the action.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    return not bool(is_open)


# Toggle RIGHT panel open/closed
@app.callback(
    Output("right-panel-open", "data"),
    Input("toggle-right-panel", "n_clicks"),
    State("right-panel-open", "data"),
    prevent_initial_call=True,
)
def toggle_right_panel_state(n_clicks, is_open):
    # Update the viewport pan/translation for the network graph.
    if n_clicks is None:
        # Guard: only run after the user triggers the action.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    return not bool(is_open)


# Update main grid columns when left/right panel visibility changes
@app.callback(
    Output("main-grid", "style"),
    Input("left-panel-open", "data"),
    Input("right-panel-open", "data"),
)
def update_main_grid_style(left_open, right_open):
    # base style
    # Update main grid style.
    style = dict(MAIN_GRID)

    cols = []
    cols.append("300px" if left_open else "0px")
    cols.append("1fr")
    cols.append("300px" if right_open else "0px")

    style["gridTemplateColumns"] = " ".join(cols)
    return style


@app.callback(
    Output("node-events", "data", allow_duplicate=True),
    Output("node-timeline", "children"),
    Input("node-id", "value"),
    Input("segment-range", "value"),
    Input("chunk-filter-ids", "data"),
    State("chunk-filter-ids", "data"),
    State("multi-logs", "data"),
    State("multi-logs-include", "data"), # CHANGED
    prevent_initial_call=True
)
def update_node_timeline(node_id, seg, _trigger_chunks_change, allowed_chunks, multi_logs, include_ids):
    # Update node timeline.
    if node_id is None:
        # Validate inputs / state before continuing.
        return {"events": []}, ""
    Vsel = _active_viz_from_multi(multi_logs, include_ids)
    with _use_viz(Vsel):
        # Use a context manager to manage resources safely.
        t0, t1 = (seg or [TIME_MIN, TIME_MAX])
        events = [ev for ev in _node_events_list(node_id) if float(t0) <= float(ev["time"]) <= float(t1)]
        if allowed_chunks:
            # Branch based on the current state / selection.
            allowed = set(map(int, allowed_chunks))
            for ev in events:
                # Iterate over the relevant items and accumulate results.
                ev["chunks"] = [cid for cid in ev["chunks"] if cid in allowed]
            events = [ev for ev in events if ev["chunks"]]
        if not events:
            # Validate inputs / state before continuing.
            return {"events": []}, html.Div("(no arrivals in segment)")
        active_idx = len(events) - 1
        rows = []
        for i, ev in enumerate(events):
            # Iterate over the relevant items and accumulate results.
            is_active = (i == active_idx)
            time_badge = html.Span(
                f"t={ev['time']:.3f}",
                style={"display":"inline-block","padding":"2px 6px","marginRight":"8px",
                       "borderRadius":"10px","background":"#eef2ff" if is_active else "#f6f7fb",
                       "fontWeight":600}
            )
            chips = [html.Span(str(cid), style={"display":"inline-block","padding":"1px 6px","marginRight":"6px","marginBottom":"4px",
                                                "border":"1px solid #ddd","borderRadius":"10px",
                                                "background":"#fafafa" if not is_active else "#eefaf3"}) for cid in ev["chunks"]]
            rows.append(html.Div(
                [time_badge, html.Span(f"{len(ev['chunks'])} chunk(s): "), html.Span(chips)],
                style={"padding":"4px 6px","borderLeft":"3px solid "+("#2a9d8f" if is_active else "transparent"),
                       "background":"#fff" if not is_active else "#f3fcf8","marginBottom":"2px"}))
        return {"events": events}, rows

@app.callback(
    Output("toggle-left-panel", "children"),
    Output("toggle-right-panel", "children"),
    Input("left-panel-open", "data"),
    Input("right-panel-open", "data"),
)
def update_panel_toggle_icons(left_open, right_open):
    """
    Use chevrons instead of 'x':
    - ▼ when panel is open
    - ▶ when panel is closed
    Like the loaded logs section style.
    """
    # Update the viewport pan/translation for the network graph.
    left_label = "✕" if left_open else "▶"
    right_label = "✕" if right_open else "◀"
    return left_label, right_label
# =========================
# Right-panel Back navigation
# =========================
@app.callback(
    Output("right-panel-history", "data", allow_duplicate=True),
    Input("active-panel", "data"),
    Input("target-collective-id", "data"),
    State("editing-collective-id", "data"),
    State("right-panel-history", "data"),
    prevent_initial_call=True
)
def update_right_panel_history(active_panel, target_cid, editing_cid, history):
    """Maintain a stack of previously visited right-panel screens, including the collective context.

    We record entries as dicts:
        {"panel": <panel_id>, "target": <target_collective_id>, "editing": <editing_collective_id>}
    This avoids the UX bug where the Back button returns to a previous panel but leaves the app
    on a different target collective (which makes chunk filters look like they were reset).
    """
    if active_panel is None:
        raise PreventUpdate

    history = history or {"stack": [], "current": None}
    stack = list(history.get("stack") or [])

    def _norm_entry(e):
        if e is None:
            return None
        if isinstance(e, dict):
            return {
                "panel": e.get("panel"),
                "target": e.get("target"),
                "editing": e.get("editing"),
            }
        # Backward-compat: previous saves stored plain panel ids.
        return {"panel": e, "target": None, "editing": None}

    cur = _norm_entry(history.get("current"))
    stack = [_norm_entry(x) for x in stack if x is not None]

    new_entry = {"panel": active_panel, "target": target_cid, "editing": editing_cid}

    # First initialization
    if cur is None:
        history["current"] = new_entry
        history["stack"] = stack[-50:]
        return history

    # If nothing changed, do nothing
    if (
        str(cur.get("panel")) == str(new_entry.get("panel"))
        and str(cur.get("target")) == str(new_entry.get("target"))
        and str(cur.get("editing")) == str(new_entry.get("editing"))
    ):
        raise PreventUpdate

    # Push the previous "current" entry if it differs from the last stack entry
    if not stack or stack[-1] != cur:
        stack.append(cur)

    history["stack"] = stack[-50:]
    history["current"] = new_entry
    return history


@app.callback(
    Output("active-panel", "data", allow_duplicate=True),
    Output("right-panel-history", "data", allow_duplicate=True),
    Output("target-collective-id", "data", allow_duplicate=True),
    Output("editing-collective-id", "data", allow_duplicate=True),
    Input("right-panel-back", "n_clicks"),
    State("right-panel-history", "data"),
    prevent_initial_call=True
)
def right_panel_go_back(n_clicks, history):
    """Go back to the previously visited right-panel screen, restoring the collective context too."""
    if not isinstance(n_clicks, (int, float)) or n_clicks <= 0:
        raise PreventUpdate

    history = history or {"stack": [], "current": None}
    stack = list(history.get("stack") or [])
    if not stack:
        raise PreventUpdate

    prev = stack.pop()
    if not isinstance(prev, dict):
        prev = {"panel": prev, "target": None, "editing": None}

    history["current"] = prev
    history["stack"] = stack[-50:]

    return prev.get("panel"), history, prev.get("target"), prev.get("editing")

@app.callback(
    Output("plot-visible", "data"),
    Output("postleft-visible", "data"),
    Output("wip-visible", "data"),
    Output("cum-visible", "data"),
    Output("avg-visible", "data"),
    Output("xy-visible", "data"),
    Output("postleft-matrix-visible", "data"),
    Input("plot-visible-toggle", "value"),
    prevent_initial_call=False
)
def set_plot_visibility(mode):
    # Enforce exclusive center-mode selection for plots.
    # Historically this was a checklist; accept list input for backwards compatibility.
    if isinstance(mode, (list, tuple, set)):
        # Priority order: graph (xy) > presence grid > topology
        if "xy" in mode:
            mode = "xy"
        elif "grid" in mode:
            mode = "grid"
        elif "topology" in mode:
            mode = "topology"
        else:
            mode = "topology"

    mode = (mode or "topology")
    grid_on = (mode == "grid")
    xy_on = (mode == "xy")

    # We keep the other panes wired, but they are not user-selectable in the UI.
    return (
        grid_on,   # plot-visible (presence grid)
        False,     # postleft-visible
        False,     # wip-visible
        False,     # cum-visible
        False,     # avg-visible
        xy_on,     # xy-visible
        False,     # postleft-matrix-visible
    )



OVERLAP_PINK = "#A37B1C"

@app.callback(
    Output("presence-grid", "figure"),
    Input("segment-range", "value"),
    Input("chunk-filter-ids", "data"),
    Input("node-filter-ids", "data"),
    Input("isolate-mode", "data"),
    Input("isolate-snapshot", "data"),
    Input("hidden-nodes", "data"),
    Input("active-collectives-map", "data"), # Active collectives
    State("elements-base", "data"),
    Input("topology-radio", "value"),        # Active topology ID
    State("topo-logs", "data"),              # Topology-Log structure
    prevent_initial_call=False
)
def build_grid(seg, allowed_chunks, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes,
               active_coll_map, elements_base, active_topo_id, topo_logs):
    import numpy as np
    import plotly.graph_objects as go
    import os

    # 1. Setup & Time Window
    t1 = float((seg or [TIME_MIN, TIME_MAX])[1])

    # 2. Identify Active Collectives (and their logs)
    selected_collectives = []

    if active_topo_id:
        tid = str(active_topo_id)
        collectives = (topo_logs or {}).get(tid, [])
        raw_actives = (active_coll_map or {}).get(tid, [])
        active_cids = set()
        for x in (raw_actives or []):
            try:
                active_cids.add(int(x))
            except Exception:
                continue

        for ci, coll in enumerate(collectives or []):
            try:
                cid = int(coll.get("id"))
            except Exception:
                continue

            if cid not in active_cids:
                continue

            # If the user explicitly chose "(none)" for this collective's data/chunk variable, it must not
            # contribute to chunk-based views (presence grid / data-series).
            if "active_data_param" in coll:
                _raw = coll.get("active_data_param")
                if _raw is None or str(_raw).strip().lower() in ("", "__none__", "none", "(none)"):
                    continue

            coll_name = coll.get("name") or f"Collective {cid}"

            # Prefer a collective-level color if present; otherwise reuse the first log's color; otherwise palette.
            coll_color = coll.get("color")
            if not coll_color:
                logs0 = coll.get("logs") or []
                if logs0 and isinstance(logs0[0], dict):
                    coll_color = logs0[0].get("color")
            if not coll_color:
                coll_color = _next_color(ci)

            # Load all logs' visualizers and resolve the active data-var object for this collective.
            # Store as (log_id, viz, data_var_obj) so downstream code can operate on the chosen data var.
            viz_list = []
            for log_bundle in (coll.get("logs") or []):
                if not isinstance(log_bundle, dict):
                    continue
                try:
                    lid = int(log_bundle.get("id"))
                except Exception:
                    continue

                V = MULTI_VIZ_OBJS.get(lid)
                if V is None:
                    path = log_bundle.get("path", "")
                    try:
                        if str(path).lower().endswith(".json"):
                            V = JsonVisualizer(path, TOPO_FILE)
                        else:
                            V = interactiveinfo.Visualizer(path, TOPO_FILE)
                        MULTI_VIZ_OBJS[lid] = V
                    except Exception:
                        V = None

                if V is None:
                    continue

                dv = _select_data_var_for_collective(V, coll)
                if dv is None:
                    continue

                viz_list.append((lid, V, dv))

            if not viz_list:
                continue

            # Include the active data-var name in the label (improves hover interpretability).
            try:
                dv_name = getattr(viz_list[0][2], "name", None)
                if dv_name is not None:
                    coll_label = f"{coll_name} [{dv_name}]"
                else:
                    coll_label = coll_name
            except Exception:
                coll_label = coll_name

            selected_collectives.append((cid, coll_label, coll_color, viz_list))

    # 3. Determine Visible Nodes (exclude switches)
    current_elems = elements_base or ELEMS

    local_switch_ids = set()
    for el in current_elems:
        if "switch" in el.get("classes", ""):
            try:
                local_switch_ids.add(int(el.get("data", {}).get("id")))
            except Exception:
                pass

    allowed_nodes_all = _visible_node_ids(current_elems, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes)
    nodes = [n for n in allowed_nodes_all if n not in local_switch_ids]

    # 4. Determine Visible Chunks
    if allowed_chunks:
        chunks_full = sorted(set(int(c) for c in allowed_chunks))
    else:
        max_chunk = 0
        for (_cid, _name, _col, viz_list) in selected_collectives:
            for (_lid, _V, _DV) in (viz_list or []):
                try:
                    max_chunk = max(max_chunk, int(getattr(_DV, "chunkCount", 0)) - 1)
                except Exception:
                    continue
        chunks_full = list(range(max_chunk + 1)) if max_chunk > 0 else []

    # Cap total cells for performance: shrink columns first (chunks), keep all rows when possible.
    capped_note = None
    MAX_CELLS = 120_000
    if len(nodes) * max(1, len(chunks_full)) > MAX_CELLS:
        max_cols = max(1, MAX_CELLS // max(1, len(nodes)))
        if len(chunks_full) > max_cols:
            chunks = chunks_full[:max_cols]
            capped_note = f"Grid capped to {len(nodes)}×{len(chunks)} cells for speed (showing first {len(chunks)} chunks)."
        else:
            chunks = chunks_full
    else:
        chunks = chunks_full

    # If nothing to show, return an empty annotated figure.
    fig = go.Figure()
    if not nodes or not chunks or not selected_collectives:
        fig.add_annotation(
            text="No active collectives / data to display in the current window.",
            xref="paper", yref="paper", x=0.02, y=0.98, showarrow=False, align="left"
        )
        fig.update_layout(margin=dict(l=10, r=10, t=10, b=10), plot_bgcolor="white", paper_bgcolor="white")
        return fig

    # 5. Build occupancy matrix: rows=nodes, cols=chunks
    H = len(nodes)
    W = len(chunks)

    node_index = {r: i for i, r in enumerate(nodes)}
    chunk_to_col = {int(c): j for j, c in enumerate(chunks)}

    M = len(selected_collectives)
    MULTI_CODE = M + 1

    z = [[0] * W for _ in range(H)]
    hover = [["" for _ in range(W)] for __ in range(H)]

    # Each collective gets a single code (k). Any overlap between *different* collectives becomes MULTI_CODE.
    for k, (_cid, label, _color, viz_list) in enumerate(selected_collectives, start=1):
        if not viz_list:
            continue

        for (_lid, _V, _DV) in viz_list:
            node_lc = getattr(_DV, "nodeLifeCycle", [])
            for r in nodes:
                if r < 0 or r >= len(node_lc):
                    continue

                arrivals_dict = node_lc[r]
                if not isinstance(arrivals_dict, dict):
                    continue

                ri = node_index[r]

                for cid, arrivals in (arrivals_dict or {}).items():
                    try:
                        icid = int(cid)
                    except Exception:
                        continue

                    cj = chunk_to_col.get(icid)
                    if cj is None or not arrivals:
                        continue

                    # Keep seeds (t=0) as valid arrivals; do not filter messages.
                    try:
                        times = [float(ts) for (ts, _msg) in arrivals]
                        if not times:
                            continue
                        earliest = min(times)
                    except Exception:
                        continue

                    if earliest <= t1:
                        if z[ri][cj] == 0:
                            z[ri][cj] = k
                            hover[ri][cj] = f"node {r} • chunk {icid}<br>collectives: {label}"
                        elif z[ri][cj] == k:
                            # Same collective already marked (e.g., multiple logs within the same collective).
                            if label not in hover[ri][cj]:
                                hover[ri][cj] += f", {label}"
                        elif z[ri][cj] != MULTI_CODE:
                            z[ri][cj] = MULTI_CODE
                            if label not in hover[ri][cj]:
                                hover[ri][cj] += f", {label}"
                        else:
                            if label not in hover[ri][cj]:
                                hover[ri][cj] += f", {label}"

    # 6. Colorscale
    OVERLAP_PINK = "#A37B1C"
    colors = ["#ffffff"] + [col for (_cid, _name, col, _viz) in selected_collectives] + [OVERLAP_PINK]
    K = len(colors)
    zmin = -0.5
    zmax = (K - 1) + 0.5

    colorscale = []
    for i, c in enumerate(colors):
        v0 = (i - 0.5 - zmin) / (zmax - zmin)
        v1 = (i + 0.5 - zmin) / (zmax - zmin)
        v0 = max(0.0, min(1.0, v0))
        v1 = max(0.0, min(1.0, v1))
        colorscale.append([v0, c])
        colorscale.append([v1, c])

    # 7. Plot heatmap
    fig.add_trace(go.Heatmap(
        z=z, zmin=zmin, zmax=zmax,
        colorscale=colorscale,
        hoverinfo="text",
        text=hover,
        showscale=False,
        # --- NEW LINES BELOW ---
        xgap=1,  # Creates a vertical gap between chunks (columns)
        ygap=1   # Creates a horizontal gap between nodes (rows)
        # -----------------------
    ))

    fig.update_layout(
        margin=dict(l=10, r=10, t=30 if capped_note else 10, b=10),
        xaxis_title="Chunks", yaxis_title="Nodes",
        xaxis=dict(
            showgrid=False, zeroline=False,
            tickmode="array",
            tickvals=list(range(W)),
            ticktext=[str(c) for c in chunks],
            fixedrange=True
        ),
        yaxis=dict(
            showgrid=False, zeroline=False,
            tickmode="array",
            tickvals=list(range(H)),
            ticktext=[str(r) for r in nodes],
            autorange="reversed",
            fixedrange=True
        ),
        plot_bgcolor="white", paper_bgcolor="white",
        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="left", x=0),
    )

    # Legend entries: one per collective (not per log)
    for (_cid, label, col, _viz) in selected_collectives:
        fig.add_trace(go.Scatter(
            x=[None], y=[None],
            mode="markers",
            marker=dict(size=10, color=col),
            name=label,
            showlegend=True
        ))

    if M >= 2:
        fig.add_trace(go.Scatter(
            x=[None], y=[None],
            mode="markers",
            marker=dict(size=10, color=OVERLAP_PINK),
            name="Overlap",
            showlegend=True
        ))

    top_text = []
    if capped_note:
        top_text.append(capped_note)
    if selected_collectives:
        labels = ", ".join(lbl for (_cid, lbl, _c, _viz) in selected_collectives)
        top_text.append(f"Selected collectives: {labels}")

    if top_text:
        fig.add_annotation(
            text=" • ".join(top_text),
            xref="paper", yref="paper", x=0, y=1.08,
            showarrow=False, align="left"
        )

    # If the whole grid is empty, show a quick hint.
    if not any(any(row) for row in z):
        fig.add_annotation(
            text="No arrivals up to current time window for selected collectives.",
            xref="paper", yref="paper", x=0.02, y=0.98,
            showarrow=False, align="left"
        )

    return fig

@app.callback(
    Output("postleft-chart", "figure"),
    Input("segment-range", "value"),
    Input("selected-nodes", "data"),
    Input("node-id", "value"),
    Input("node-filter-ids", "data"),
    Input("isolate-mode", "data"),
    Input("isolate-snapshot", "data"),
    Input("hidden-nodes", "data"),
    Input("chunk-filter-ids", "data"),
    State("elements-base", "data"),
    prevent_initial_call=False
)
def build_postleft_chart(
    seg,
    selected_nodes,
    typed_node,
    node_filter_ids,
    isolate_mode,
    isolate_snapshot,
    hidden_nodes,
    allowed_chunks,      
    elements_base
):
    t0, t1 = (seg or [TIME_MIN, TIME_MAX])
    t0 = float(t0); t1 = float(t1)
    fig = go.Figure()

    if VIZ is None:
        fig.update_layout(
            xaxis=dict(visible=False), yaxis=dict(visible=False),
            annotations=[dict(text="No simulation loaded (.vis). Use Logs.", showarrow=False)],
            margin=dict(l=10, r=10, t=10, b=10)
        )
        return fig

    # Visible non-switch hosts
    allowed_all = _visible_node_ids(elements_base or ELEMS, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes)
    hosts_all = [n for n in allowed_all if n not in SWITCH_IDS]

    # Nodes to plot
    chosen = set(int(n) for n in (selected_nodes or []) if str(n).isdigit())
    if typed_node is not None:
        try: chosen.add(int(typed_node))
        except Exception: pass
    chosen = [n for n in chosen if n in hosts_all]

    # Time samples
    MAX_POINTS = 160
    N = max(50, min(MAX_POINTS, 1 + int((t1 - t0) / max(1e-9, (t1 - t0) / 120.0))))
    times = [t0 + (t1 - t0) * i / (N - 1) if N > 1 else t0 for i in range(N)]

    # Chunk filter set
    allowed_set = set(int(c) for c in (allowed_chunks or []))
    cmax = int(getattr(VIZ, "chunkCount", 0))

    def series_for_node(node: int):
        """Fast series via precomputed first-arrival lists + bisect."""
        # Ensure cache exists for this node (in case user loaded a session before a log, etc.)
        # Series for node.
        firsts_all = _NODE_FIRSTS_ALL.get(node)
        perchunk = _NODE_FIRSTS_BY_CHUNK.get(node)
        if firsts_all is None or perchunk is None:
            # Build lazily for this node (rare)
            _warm_node_arrival_cache(hosts_only=False)
            firsts_all = _NODE_FIRSTS_ALL.get(node, [])
            perchunk = _NODE_FIRSTS_BY_CHUNK.get(node, {})

        if allowed_set:
            # Branch based on the current state / selection.
            firsts = sorted(perchunk[c] for c in allowed_set if c in perchunk)
            total = len(allowed_set)
        else:
            firsts = firsts_all
            total = cmax if cmax > 0 else len(firsts_all)

        ys = []
        for tt in times:
            # Iterate over the relevant items and accumulate results.
            got = bisect_right(firsts, float(tt))
            ys.append(max(0, total - got))
        return ys

    # Plot lines or average
    if chosen:
        lines = chosen[:8]
        for n in lines:
            fig.add_trace(go.Scatter(x=times, y=series_for_node(n), mode="lines", name=f"node {n}"))
        if len(chosen) > 8:
            fig.add_annotation(text=f"+{len(chosen)-8} more selected nodes (not shown)",
                               xref="paper", yref="paper", x=1.0, y=1.05, showarrow=False)
    else:
        if not hosts_all:
            fig.update_layout(
                xaxis=dict(visible=False), yaxis=dict(visible=False),
                annotations=[dict(text="No host nodes on screen (filter/isolate/hidden).", showarrow=False)],
                margin=dict(l=10, r=10, t=10, b=10)
            )
            return fig

        MAX_AVG_HOSTS = 200
        hosts = hosts_all[:MAX_AVG_HOSTS]
        sampled_note = None
        if len(hosts_all) > MAX_AVG_HOSTS:
            sampled_note = f"Average computed on first {MAX_AVG_HOSTS} of {len(hosts_all)} visible hosts (cap for speed)."

        # Precompute per-node series once, then average by column
        node_series = [series_for_node(n) for n in hosts]
        avg = [sum(col) / float(len(hosts)) for col in zip(*node_series)]
        fig.add_trace(go.Scatter(x=times, y=avg, mode="lines", name="Average (visible hosts)"))
        if sampled_note:
            fig.add_annotation(text=sampled_note, xref="paper", yref="paper", x=0, y=1.08, showarrow=False, align="left")

    if allowed_set:
        fig.add_annotation(
            text=f"Filtered by {len(allowed_set)} selected chunk(s)",
            xref="paper", yref="paper", x=0, y=1.14, showarrow=False, align="left"
        )

    fig.update_layout(
        margin=dict(l=10, r=20, t=36 if allowed_set else 28, b=40),
        xaxis_title="Time", yaxis_title="Post-conditions left",
        paper_bgcolor="white", plot_bgcolor="white",
        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="left", x=0),
    )
    return fig


@app.callback(
    Output("wip-over-time", "figure"),
    Output("cum-finished-over-time", "figure"),
    Output("avg-send-duration-over-time", "figure"),
    Input("store-sends", "data"),
    Input("store-chunk-finish-times", "data"),
    Input("store-chunk-start-times", "data"),
    Input("chunk-filter-ids", "data"),
)
def render_throughput(sends_rec, fin_map, start_map, chunk_filter_ids):
    # Render throughput.
    # Create a DataFrame to make filtering/aggregation/plotting simpler.
    sends = pd.DataFrame(sends_rec or [])
    allowed = set(int(c) for c in (chunk_filter_ids or []))
    # If we can, restrict to filtered chunks
    if not sends.empty and allowed and "chunk" in sends.columns:
        # keep rows with known chunk in allowed; if chunk is NaN/None we drop them under a filter
        sends = sends[sends["chunk"].apply(lambda x: (x in allowed) if pd.notna(x) else False)]

    # 1) WIP (sends). If none → fallback to chunk-level WIP
    if not sends.empty:
        # Validate inputs / state before continuing.
        x_wip, y_wip = _series_wip_from_intervals(sends)
        note = None
    else:
        starts = {int(k): float(v) for k, v in (start_map or {}).items()
                  if (not allowed) or (int(k) in allowed)}
        fins   = {int(k): float(v) for k, v in (fin_map   or {}).items()
                  if (not allowed) or (int(k) in allowed)}
        if starts and fins:
            # Branch based on the current state / selection.
            x_wip, y_wip = _chunk_wip_from_start_finish(starts, fins)
            note = "No send intervals found; showing chunk-level WIP (chunks started − finished)."
        else:
            x_wip, y_wip, note = [], [], "No data to compute WIP."
    fig_wip = _line_fig(x_wip, y_wip, "In-flight sends (WIP)", "sends")
    fig_wip.update_traces(line=dict(shape="hv"))  # step plot: horizontal then vertical

    if note:
        # Branch based on the current state / selection.
        fig_wip.add_annotation(text=note, xref="paper", yref="paper", x=0, y=1.10, showarrow=False, align="left")

    # 2) Cumulative finished chunks
    fins_map = {int(k): float(v) for k, v in (fin_map or {}).items()
                if (not allowed) or (int(k) in allowed)}
    x_cum, y_cum = _series_cum_finished(fins_map)
    fig_cum = _line_fig(x_cum, y_cum, "Cumulative finished chunks", "chunks")

    # 3) Average time per send (ms), anchored at end
    if not sends.empty:
        # Validate inputs / state before continuing.
        x_avg, y_avg = _series_avg_send_duration(sends, anchor="t_end")
    else:
        x_avg, y_avg = [], []
    fig_avg = _line_fig(x_avg, y_avg, "Average send duration", "ms")

    # make narrow spikes obvious
    fig_avg.update_traces(connectgaps=True, mode="lines+markers")
    fig_avg.update_traces(marker=dict(size=3))

    return fig_wip, fig_cum, fig_avg


# =========================
# Global Next/Prev navigation
# =========================
def _global_event_times(seg, chunk_id, selectedNodeData, node_id, allowed_nodes):
    # Global event times.
    t0, _t1 = (seg or [TIME_MIN, TIME_MAX])
    t0 = float(t0)
    allowed = set(int(n) for n in (allowed_nodes or []))

    # 1) Chunk events
    if chunk_id is not None:
        # Validate inputs / state before continuing.
        raw = _chunk_events_list(chunk_id) or []
        sel_set = set()
        for d in (selectedNodeData or []):
            # Iterate over the relevant items and accumulate results.
            try: sel_set.add(int(d.get("id")))
            except Exception: pass
        times = []
        for ev in raw:
            # Iterate over the relevant items and accumulate results.
            tt = float(ev["time"])
            if tt < t0: continue
            if sel_set:
                # Branch based on the current state / selection.
                inter = [n for n in ev["nodes"] if n in sel_set]
                if not inter: continue
            else:
                if allowed:
                    # Branch based on the current state / selection.
                    inter = [n for n in ev["nodes"] if n in allowed]
                    if not inter: continue
            times.append(tt)
        if times:
            # Branch based on the current state / selection.
            return sorted(set(times))

    # 2) Selected nodes
    sel_nodes = []
    for d in (selectedNodeData or []):
        # Iterate over the relevant items and accumulate results.
        try:
            nid = int(d.get("id"))
            if not allowed or nid in allowed:
                # Validate inputs / state before continuing.
                sel_nodes.append(nid)
        except Exception:
            # Recover from a failure case and return a safe default.
            pass
    if sel_nodes:
        # Branch based on the current state / selection.
        s = set()
        for r in sel_nodes:
            # Iterate over the relevant items and accumulate results.
            for ev in _node_events_list(r):
                # Iterate over the relevant items and accumulate results.
                tt = float(ev["time"])
                if tt >= t0: s.add(tt)
        return sorted(s)

    # 3) Typed node
    if node_id is not None and ((not allowed) or (int(node_id) in allowed)):
        # Validate inputs / state before continuing.
        s = set()
        for ev in _node_events_list(node_id):
            # Iterate over the relevant items and accumulate results.
            tt = float(ev["time"])
            if tt >= t0: s.add(tt)
        return sorted(s)

    return []

@app.callback(
    Output("empty-state-msg", "style"),
    Input("elements-base", "data"),
    prevent_initial_call=False
)
def manage_empty_state_msg(elems):
    # Default visible style
    visible_style = {
        "position": "absolute", 
        "top": "50%", 
        "left": "50%",
        "transform": "translate(-50%, -50%)",
        "fontSize": "22px", 
        "color": "#94a3b8", 
        "fontWeight": "600",
        "textAlign": "center", 
        "pointerEvents": "none", 
        "zIndex": 0,
        "width": "100%",
        "display": "block"
    }

    # If we have topology elements, hide the message
    if elems and len(elems) > 0:
        return {"display": "none"}
    
    # Otherwise, show it
    return visible_style


@app.callback(
    Output("segment-range", "value", allow_duplicate=True),
    Output("global-nav-info", "children", allow_duplicate=True),
    Output("suppress-snap", "data", allow_duplicate=True),
    Input("global-next", "n_clicks"),
    Input("global-prev", "n_clicks"),
    Input("chunk-next", "n_clicks"),
    Input("chunk-prev", "n_clicks"),
    State("segment-range", "value"),
    State("chunk-events", "data"),
    State("network-graph", "selectedNodeData"),
    State("node-id", "value"),
    State("chunk-id", "value"),
    State("node-filter-ids", "data"),
    State("isolate-mode", "data"),
    State("isolate-snapshot", "data"),
    State("hidden-nodes", "data"),
    State("elements-base", "data"),
    State("time-max", "data"),
    State("time-min", "data"),
    prevent_initial_call=True
)
def global_nav(n1, n2, n3, n4, seg, _chunk_events_store, selectedNodeData, node_id, chunk_id,
               node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes, elements_base, tmax_store, tmin_store):
    ctx = dash.callback_context
    if not ctx.triggered:
        raise PreventUpdate
    which = ctx.triggered[0]["prop_id"].split(".")[0]
    go_next = which in ("global-next", "chunk-next")
    go_prev = which in ("global-prev", "chunk-prev")
    t0, t1 = (seg or [TIME_MIN, TIME_MAX])

    allowed_nodes = _visible_node_ids(elements_base or ELEMS, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes)
    allowed_nodes = [n for n in allowed_nodes if n not in SWITCH_IDS]
    times = _global_event_times([t0, t1], chunk_id, selectedNodeData, node_id, allowed_nodes)
    curr = float(t1)
    EPS = 1e-9

    if not times:
        if go_next and tmax_store is not None:
            return [float(t0), float(tmax_store)], f"End → t={float(tmax_store):.3f}.", True
        if go_prev and tmin_store is not None:
            return [float(tmin_store), float(tmin_store)], f"Start → t={float(tmin_store):.3f}.", True
        return no_update, "No events found (set chunk id / select nodes / fill node id).", True

    if go_next:
        cand = [t for t in times if t > curr + EPS]
        new_t1 = cand[0] if cand else float(tmax_store if tmax_store is not None else times[-1])
    elif go_prev:
        cand = [t for t in times if t < curr - EPS]
        new_t1 = cand[-1] if cand else float(tmin_store if tmin_store is not None else times[0])
    else:
        new_t1 = times[0]
    return [float(t0), float(new_t1)], f"End → t={new_t1:.3f}.", True

# =========================
# Time segment helpers & snapping
# =========================

# --- Top bar banner: show when some chunks are filtered ---
@app.callback(
    Output("chunk-filter-banner", "children"),
    Output("chunk-filter-banner", "style"),
    Input("chunk-filter-ids", "data"),
    prevent_initial_call=False
)
def update_chunk_filter_banner(chunk_ids):
    if chunk_ids and len(chunk_ids) > 0:
        return "some chunks are filtered", {
            "display": "inline-block",
            "marginLeft": "10px",
            "padding": "2px 8px",
            "borderRadius": "999px",
            "border": "1px solid #ffe08a",
            "background": "#fff6d6",
            "color": "#7a5a00",
            "fontSize": "12px",
            "fontWeight": 700,
            "cursor": "pointer",
        }
    return "", {"display": "none"}


# --- Clickable banner: jump to the chunk-filter controls for the current collective ---
@app.callback(
    Output("active-panel", "data", allow_duplicate=True),
    Output("right-panel-open", "data", allow_duplicate=True),
    Output("filter-param-dropdown", "value", allow_duplicate=True),
    Input("chunk-filter-banner", "n_clicks"),
    State("target-collective-id", "data"),
    State("topology-radio", "value"),
    State("topo-logs", "data"),
    State("avail-params", "data"),
    State("filter-param-dropdown", "value"),
    prevent_initial_call=True
)
def jump_to_chunk_filter_controls(n_clicks, target_cid, active_tid, topo_collectives, avail_params, current_param):
    if not isinstance(n_clicks, (int, float)) or n_clicks <= 0:
        raise PreventUpdate

    data_params = [p.get("value") for p in (avail_params or []) if p.get("type") == "data" and p.get("value")]

    chosen = None
    try:
        if active_tid is not None and target_cid is not None:
            cols = (topo_collectives or {}).get(str(active_tid), []) or []
            for c in cols:
                if str(c.get("id")) == str(target_cid):
                    ap = c.get("active_data_param")
                    if ap and str(ap).lower() not in ("none", ""):
                        chosen = ap
                    break
    except Exception:
        chosen = None

    if chosen not in data_params:
        chosen = data_params[0] if data_params else None

    # If there is no DataVar to select, fall back to the dedicated Chunk Filters panel.
    target_panel = "param_filters" if data_params else "data"

    return target_panel, True, (chosen if chosen is not None else no_update)


# --- Show a "topo view" shortcut when the center is not currently showing topology ---
@app.callback(
    Output("btn-topo-view", "style"),
    Input("plot-visible-toggle", "value"),
    prevent_initial_call=False
)
def toggle_topo_view_shortcut(mode):
    if isinstance(mode, (list, tuple, set)):
        if "xy" in mode:
            mode = "xy"
        elif "grid" in mode:
            mode = "grid"
        elif "topology" in mode:
            mode = "topology"
        else:
            mode = "topology"
    mode = (mode or "topology")

    if mode != "topology":
        return {
            "display": "inline-block",
            "marginLeft": "10px",
            "padding": "2px 8px",
            "borderRadius": "999px",
            "border": "1px solid #cbd5e1",
            "background": "#ffffff",
            "color": "#334155",
            "fontSize": "12px",
            "fontWeight": 700,
            "cursor": "pointer",
        }
    return {"display": "none"}


@app.callback(
    Output("plot-visible-toggle", "value", allow_duplicate=True),
    Input("btn-topo-view", "n_clicks"),
    prevent_initial_call=True
)
def force_topology_view(n_clicks):
    if not isinstance(n_clicks, (int, float)) or n_clicks <= 0:
        raise PreventUpdate
    return "topology"

@app.callback(
    Output("segment-start", "data"),
    Output("segment-end", "data"),
    Output("segment-label", "children"),
    Input("segment-range", "value"),
    prevent_initial_call=False
)
def keep_segment(seg):
    # Keep segment.
    t0, t1 = (seg or [TIME_MIN, TIME_MAX])
    return float(t0), float(t1), f"[{float(t0):.3f} → {float(t1):.3f}]"

# Snap end gently: allow free drag, snap only when close to a multiple or to tmax.
@app.callback(
    Output("segment-range", "value", allow_duplicate=True),
    Output("global-nav-info", "children", allow_duplicate=True),
    Output("suppress-snap", "data", allow_duplicate=True),
    Input("segment-range", "value"),
    State("segment-start", "data"),
    State("segment-end", "data"),
    State("time-min", "data"),
    State("time-max", "data"),
    State("lock-window", "data"),
    State("suppress-snap", "data"),
    prevent_initial_call=True
)
def snap_gently(seg_val, prev_t0, prev_t1, tmin, tmax, lock_window, suppress):
    # Snap gently.
    if suppress or not seg_val or tmin is None or tmax is None:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    t0, t1 = float(seg_val[0]), float(seg_val[1])
    
    # Calculate current window size to use as a ruler for "closeness"
    window = (float(prev_t1) - float(prev_t0)) if (prev_t0 is not None and prev_t1 is not None) else (t1 - t0)
    # Stop here to avoid updating outputs when the callback should not run yet.
    if window <= 0: raise PreventUpdate

    # --- SIMPLIFIED LOGIC ---
    
    # 1. Snap to Real End (Priority)
    # If we are within 1% of the end, just snap to the real end (tmax).
    if t1 >= float(tmax) - (0.01 * window):
        # Branch based on the current state / selection.
        target = float(tmax)
        label = "Snapped → end=tmax"

    # 2. Snap to Segment Multiple (Secondary)
    else:
        # Find nearest multiple of window
        k = math.ceil((t1 - float(tmin)) / window)
        cand = float(tmin) + k * window
        cand = min(max(cand, float(tmin)), float(tmax))
        
        # Only snap if we are close (1%)
        if abs(cand - t1) <= (0.01 * window):
            # Branch based on the current state / selection.
            target = cand
            label = "Snapped → end≈multiple"
        else:
            # Stop here to avoid updating outputs when the callback should not run yet.
            raise PreventUpdate # Free drag, don't snap

    # Avoid infinite loops if we are already at the target
    if abs(target - t1) < 1e-9:
        # Branch based on the current state / selection.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate

    new_t1 = target
    # If locked, pull the start time along; otherwise leave start time alone
    new_t0 = max(float(tmin), new_t1 - window) if bool(lock_window) else float(t0)

    return [float(new_t0), float(new_t1)], label, False

@app.callback(
    Output("lock-window", "data"),
    Input("lock-window-toggle", "value"),
    prevent_initial_call=False
)
def set_lock_window(vals):
    # Set lock window.
    return ("lock" in (vals or []))

# Move (programmatic) — use guard to bypass snapper
@app.callback(
    Output("segment-range", "value", allow_duplicate=True),
    Output("global-nav-info", "children", allow_duplicate=True),
    Output("suppress-snap", "data", allow_duplicate=True),
    Input("move-step", "n_clicks"),
    State("play-speed", "value"),
    State("segment-range", "value"),
    State("lock-window", "data"),
    State("time-min", "data"),
    State("time-max", "data"),
    prevent_initial_call=True
)
def move_once(_n, speed, seg, lock_window, tmin, tmax):
    # Move once.
    try:
        spd = float(speed or 0.0)
    except Exception:
        # Recover from a failure case and return a safe default.
        spd = 0.0
    if spd == 0.0:
        # Branch based on the current state / selection.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    t0, t1 = (seg or [tmin, tmax])
    dt = spd * 1.0
    new_t1 = min(float(t1) + dt, float(tmax))
    if bool(lock_window):
        # Branch based on the current state / selection.
        window = float(t1) - float(t0)
        new_t0 = max(float(tmin), new_t1 - max(0.0, window))
    else:
        new_t0 = float(t0)
    return [float(new_t0), float(new_t1)], f"Moved → t_end={new_t1:.3f}", True

# Apply saved layout (positions-only loader)
# [Find and Replace this callback]
@app.callback(
    Output("network-graph", "layout", allow_duplicate=True),
    Input("saved-layout", "data"),
    prevent_initial_call=True
)
def apply_layout(saved):
    # Fix: If saved is None or empty, return a clean layout dict (no positions).
    # This ensures we clear any previous topology's layout artifact.
    # Apply layout.
    pos_map = (saved or {}).get("positions")
    
    if not pos_map:
        # Validate inputs / state before continuing.
        return {"name": "preset", "fit": False, "animate": False}
        
    return {"name": "preset", "positions": pos_map, "fit": False, "animate": False}

# Clear layout positions after applying
@app.callback(
    Output("network-graph", "layout", allow_duplicate=True),
    Output("layout-has-positions", "data", allow_duplicate=True),
    Input("network-graph", "elements"),
    State("layout-has-positions", "data"),
    prevent_initial_call=True
)
def clear_layout_after_apply(_elements, has_positions):
    # Clear layout after apply.
    if has_positions:
        # Branch based on the current state / selection.
        return {"name": "preset", "fit": False, "animate": False}, False
    # Stop here to avoid updating outputs when the callback should not run yet.
    raise PreventUpdate

# =========================
# FULL SESSION SAVE/LOAD
# =========================
@server.route("/save_session", methods=["POST"])
def save_session_route():
    # Serialize the current session state so it can be saved and later restored.
    try:
        # Parse the incoming request body as JSON.
        payload = request.get_json(force=True) or {}
        path = payload.get("path") or SESSION_FILE
        sess = payload.get("session") or {}
        if not isinstance(sess, dict) or not sess:
            # Validate inputs / state before continuing.
            return jsonify(ok=False, message="No session payload."), 400
        # Resolve and validate filesystem paths before using them.
        path = os.path.expanduser(path)
        if not os.path.isabs(path):
            # Validate inputs / state before continuing.
            # Resolve and validate filesystem paths before using them.
            path = os.path.join(BASE_DIR, path)
        _atomic_json_write(path, sess)
        return jsonify(ok=True, message=f"Session saved → {path}")
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return jsonify(ok=False, message=f"Save session failed: {e}"), 500

@app.callback(
    Output("runjs", "run", allow_duplicate=True),
    Input("save-session", "n_clicks"),
    State("session-file-path", "data"),
    # UI States
    State("active-panel", "data"),
    State("segment-range", "value"),
    State("cap-range", "value"),
    State("edge-types", "value"),
    State("color-mode", "data"),
    State("isolate-mode", "data"),
    State("isolate-snapshot", "data"),
    State("hidden-nodes", "data"),
    State("chunk-id", "value"),
    State("node-id", "value"),
    State("plot-visible", "data"),
    State("xy-visible", "data"),
    State("postleft-visible", "data"),
    State("node-filter-ids", "data"),
    State("chunk-filter-ids", "data"),
    # NEW: Topology & Log States
    State("multi-topos", "data"),           # List of loaded topology files
    State("topology-radio", "value"),       # Active topology ID
    State("topo-logs", "data"),             # Logs associated with each topo
    State("multi-logs", "data"),            # Global multi-log list (for exact session restore)
    State("multi-logs-include", "data"),    # Global log selection
    State("topo-states", "data"),           # Layouts/metadata per topo
    # NEW: Collective context for full restore
    State("target-collective-id", "data"),
    State("editing-collective-id", "data"),
    State("active-collectives-map", "data"),
    State("param-filter-store", "data"),
    State("right-panel-history", "data"),
    State("plot-visible-toggle", "value"),

    prevent_initial_call=True
)
def save_full_session_js(_n, path, active_panel, seg, cap_range, edge_types, color_mode,
                         isolate_on, iso_snap, hidden_nodes, chunk_id, node_id, grid_on, xy_on,
                         postleft_on, node_filt, chunk_filt,
                         multi_topos, active_topo_id, topo_logs, multi_logs, global_log_selection, topo_states,
                         target_cid, editing_cid, active_coll_map, param_filter_store, right_panel_history, plot_mode):
    
    
    # Normalize a few stores to keep the session JSON stable across versions.
    norm_active_coll_map = {}
    for _tid, _ids in (active_coll_map or {}).items():
        if _ids is None:
            norm_active_coll_map[str(_tid)] = []
            continue
        if isinstance(_ids, set):
            _ids = list(_ids)
        if not isinstance(_ids, (list, tuple)):
            _ids = [_ids]
        out_ids = []
        for _x in _ids:
            try:
                out_ids.append(int(_x))
            except Exception:
                pass
        norm_active_coll_map[str(_tid)] = out_ids
# 1. Build the UI state object
    ui = {
        "active_panel": active_panel or "view",
        "segment": {"t0": float(seg[0]) if seg else float(TIME_MIN),
                    "t1": float(seg[1]) if seg else float(TIME_MAX)},
        "color_mode": (color_mode or "none"),
        "filters": {
            "cap_range": cap_range or [CAP_MIN, CAP_MAX],
            "edge_types": edge_types or ["etype-host-host", "etype-switch-switch", "etype-host-switch"],
            "node_ids": node_filt or [],
            "chunk_ids": chunk_filt or []
        },
        "isolation": {"on": bool(isolate_on), "snapshot_ids": iso_snap or []},
        "hidden_nodes": hidden_nodes or [],
        "chunk": {"id": (int(chunk_id) if chunk_id is not None else None)},
        "node": {"id": (int(node_id) if node_id is not None else None)},
        "center": {"mode": (plot_mode if plot_mode in ("topology", "grid", "xy") else ("xy" if bool(xy_on) else ("grid" if bool(grid_on) else "topology"))),
                  "grid": bool(grid_on), "xy": bool(xy_on), "postleft": bool(postleft_on)},
        
        # NEW: Save Topology & Log Context
        "topology_context": {
            "multi_topos": multi_topos or [],
            "active_topo_id": active_topo_id,
            "topo_logs": topo_logs or {},
            "multi_logs": (multi_logs or []),
            "global_log_selection": global_log_selection or [],
            "topo_states": topo_states or {}
        },

        # NEW: Save per-collective UI context for exact restore
        "collective_context": {
            "target_cid": (int(target_cid) if target_cid is not None else None),
            "editing_cid": (int(editing_cid) if editing_cid is not None else None),
            "active_collectives_map": norm_active_coll_map,
            "param_filter_store": (param_filter_store if param_filter_store is not None else None),
            "right_panel_history": (right_panel_history or [])
        }

    }

    ui_js = json.dumps(ui)
    path_js = json.dumps(os.path.expanduser(path or SESSION_FILE))
    
    # We execute JS to grab the current graph positions (zoom/pan) and then POST everything to Python
    return _js(r"""
    (function(){
      const status=(m)=>{ const el=document.getElementById('session-status'); if(el) el.textContent=m; };
      const host=document.getElementById('network-graph');
      if(!host){ status('Save failed: #network-graph not found'); return; }
      function getCy(){
        if (window.cy && typeof window.cy.nodes==='function') return window.cy;
        const inner=host.querySelector('.dash-cytoscape, .cytoscape-container');
        const cy=host._cy||host.cy||host.__cy||(inner?(inner._cy||inner.cy||inner.__cy):null);
        if (cy && typeof cy.nodes==='function') return cy;
        const first=host.firstElementChild;
        if(first && (first._cy||first.cy||first.__cy)){
          const c2=first._cy||first.cy||first.__cy;
          if(c2 && typeof c2.nodes==='function') return c2;
        }
        return null;
      }
      let tries=0;
      (function capture(){
        const cy=getCy();
        if(!cy){
          if(tries++<100){return setTimeout(capture,50);}
          status('Save failed: Cytoscape not ready'); return;
        }
        const positions={};
        cy.nodes().forEach(n=>{ const p=n.position(); positions[n.id()]={x:p.x,y:p.y}; });
        const zoom=cy.zoom(); const pan=cy.pan();
        const selected_nodes=cy.nodes(':selected').map(n=>n.id());
        
        // Version 7 includes multi-topology support
        const payload={ version: 7, captured_at: Date.now(),
          graph: { positions, zoom, pan, selected_nodes, layout: { name: "preset" } },
          ui: $UI_JS 
        };
        
        fetch('/save_session',{method:'POST',headers:{'Content-Type':'application/json'},
          body:JSON.stringify({path:$PATH_JS, session:payload})})
          .then(r=>r.json()).then(js=>status(js && js.message?js.message:'Session saved.'))
          .catch(e=>status('Save failed: '+e));
      })();
    })();
    """, UI_JS=ui_js, PATH_JS=path_js)

@app.callback(
    Output("session-status", "children", allow_duplicate=True),
    Output("active-panel", "data", allow_duplicate=True),
    Output("cap-range", "value"),
    Output("edge-types", "value"),
    Output("color-mode", "data", allow_duplicate=True),
    Output("isolate-mode", "data", allow_duplicate=True),
    Output("isolate-snapshot", "data", allow_duplicate=True),
    Output("hidden-nodes", "data", allow_duplicate=True),
    Output("segment-range", "value", allow_duplicate=True),
    Output("chunk-id", "value"),
    Output("node-id", "value"),
    Output("selected-nodes", "data", allow_duplicate=True),
    Output("network-graph", "layout", allow_duplicate=True),
    Output("network-graph", "zoom", allow_duplicate=True),
    Output("network-graph", "pan", allow_duplicate=True),
    Output("zoom-label", "children", allow_duplicate=True),
    Output("layout-has-positions", "data", allow_duplicate=True),
    Output("plot-visible-toggle", "value"),
    Output("node-filter-ids", "data", allow_duplicate=True),
    Output("chunk-filter-ids", "data", allow_duplicate=True),
    # NEW: Full collective restore
    Output("target-collective-id", "data", allow_duplicate=True),
    Output("editing-collective-id", "data", allow_duplicate=True),
    Output("active-collectives-map", "data", allow_duplicate=True),
    Output("param-filter-store", "data", allow_duplicate=True),
    Output("right-panel-history", "data", allow_duplicate=True),
    
    # Topology State Restoration
    Output("multi-topos", "data", allow_duplicate=True),
    Output("topology-radio", "value", allow_duplicate=True),
    Output("topo-logs", "data", allow_duplicate=True),
    Output("multi-logs", "data", allow_duplicate=True),
    Output("multi-logs-include", "data", allow_duplicate=True),
    Output("topo-states", "data", allow_duplicate=True),
    
    # NEW: Push the graph elements immediately!
    Output("elements-base", "data", allow_duplicate=True),

    Input("load-session", "n_clicks"),
    State("session-file-path", "data"),
    prevent_initial_call=True
)
def load_full_session(_n, path):
    # Load a saved session and repopulate the app state (topology, filters, view settings, and logs).
    try:
        # Resolve and validate filesystem paths before using them.
        p = os.path.expanduser(path or SESSION_FILE)
        if not os.path.isabs(p):
            # Validate inputs / state before continuing.
            # Resolve and validate filesystem paths before using them.
            p = os.path.join(BASE_DIR, p)
            
        with open(p, "r") as f:
            # Open the file and ensure it is closed correctly.
            sess = json.load(f) or {}

        # 1. Restore Graph Visuals
        graph = sess.get("graph", {})
        positions = graph.get("positions") or {}
        layout = {"name":"preset", "positions": positions, "fit": False, "animate": False}
        zoom = float(graph.get("zoom") if graph.get("zoom") is not None else 1.0)
        pan = graph.get("pan") or {"x": 0, "y": 0}
        selected_nodes = graph.get("selected_nodes") or []
        
        # 2. Restore UI Controls
        ui = sess.get("ui", {})
        active_panel = ui.get("active_panel") or "view"
        seg_ui = ui.get("segment") or {}
        seg = [float(seg_ui.get("t0", TIME_MIN)), float(seg_ui.get("t1", TIME_MAX))]
        color_mode = ui.get("color_mode") or "none"
        
        filters = ui.get("filters") or {}
        cap_range = filters.get("cap_range") or [CAP_MIN, CAP_MAX]
        edge_types = filters.get("edge_types") or ["etype-host-host", "etype-switch-switch", "etype-host-switch"]
        node_ids = filters.get("node_ids") or []
        chunk_ids = filters.get("chunk_ids") or []
        
        iso = ui.get("isolation") or {}
        iso_on = bool(iso.get("on"))
        iso_snap = iso.get("snapshot_ids") or []
        hidden_nodes = ui.get("hidden_nodes") or []
        
        ch = ui.get("chunk") or {}
        nd = ui.get("node") or {}
        center = ui.get("center") or {}

        # Center view mode is exclusive: topology | grid | xy
        plot_mode = center.get("mode")
        if not plot_mode:
            # Backwards compatibility with older sessions that stored booleans only
            if center.get("xy"):
                plot_mode = "xy"
            elif center.get("grid"):
                plot_mode = "grid"
            else:
                plot_mode = "topology"
        # Older sessions may have stored other center panes; fall back safely.
        if plot_mode not in ("topology", "grid", "xy"):
            plot_mode = "topology"
        
        # 3. Restore Topology Context
        topo_ctx = ui.get("topology_context", {})
        multi_topos = topo_ctx.get("multi_topos", [])
        active_topo_id = topo_ctx.get("active_topo_id")
        topo_logs = topo_ctx.get("topo_logs", {})
        global_log_selection = topo_ctx.get("global_log_selection", [])
        topo_states = topo_ctx.get("topo_states", {})
        # Multi-logs store is used by many callbacks (active VIZ selection, chunk presence, etc.).
        # New sessions may store it explicitly; otherwise rebuild it from topo_states/topo_logs.
        multi_logs_for_restore = topo_ctx.get("multi_logs")
        if not isinstance(multi_logs_for_restore, list):
            # Prefer the per-topology saved state (it mirrors what the app uses when switching topologies)
            try:
                _tid_key = str(active_topo_id) if active_topo_id is not None else None
                if _tid_key and isinstance(topo_states, dict) and isinstance(topo_states.get(_tid_key), dict):
                    maybe = topo_states[_tid_key].get("logs")
                    if isinstance(maybe, list):
                        multi_logs_for_restore = maybe
            except Exception:
                pass
        if not isinstance(multi_logs_for_restore, list):
            # Fallback: flatten from topo_logs of the active topology
            multi_logs_for_restore = []
            try:
                _tid_key = str(active_topo_id) if active_topo_id is not None else None
                cols = (topo_logs or {}).get(_tid_key, []) if _tid_key else []
                seen = set()
                for c in (cols or []):
                    if not isinstance(c, dict):
                        continue
                    for b in (c.get("logs") or []):
                        if not isinstance(b, dict):
                            continue
                        try:
                            lid = int(b.get("id"))
                        except Exception:
                            continue
                        if lid in seen:
                            continue
                        seen.add(lid)
                        multi_logs_for_restore.append(b)
            except Exception:
                multi_logs_for_restore = []

        # If global_log_selection was not saved (older sessions), derive it from per-topology state.
        if not isinstance(global_log_selection, list):
            global_log_selection = []
        if (not global_log_selection) and active_topo_id is not None and isinstance(topo_states, dict):
            try:
                _tid_key = str(active_topo_id)
                inc = (topo_states.get(_tid_key) or {}).get("include")
                if isinstance(inc, list):
                    global_log_selection = inc
            except Exception:
                pass

        # If we still have no selected logs but we do have logs restored, default-select the first log.
        if (not global_log_selection) and isinstance(multi_logs_for_restore, list) and multi_logs_for_restore:
            try:
                global_log_selection = [int(multi_logs_for_restore[0].get('id'))]
            except Exception:
                global_log_selection = global_log_selection

        # 3b. Restore Collective Context (for exact behavior on load)
        collective_ctx = ui.get("collective_context", {}) or {}
        target_cid = collective_ctx.get("target_cid")
        editing_cid = collective_ctx.get("editing_cid")
        active_coll_map = collective_ctx.get("active_collectives_map")
        param_filter_store = collective_ctx.get("param_filter_store")
        right_panel_history = collective_ctx.get("right_panel_history") or []

        # Normalize topo_logs entries for backwards compatibility
        topo_logs = topo_logs or {}
        for _tid, _cols in list(topo_logs.items()):
            if not isinstance(_cols, list):
                continue
            for _c in _cols:
                if not isinstance(_c, dict):
                    continue
                _c.setdefault("logs", [])
                _c.setdefault("active", True)
                _c.setdefault("chunk_filter_ids", [])
                _c.setdefault("hidden_params", [])
                _c.setdefault("active_link_param", None)
                _c.setdefault("active_data_param", None)

        # If active_collectives_map was not saved (older sessions), derive it from topo_logs.
        if not isinstance(active_coll_map, dict):
            active_coll_map = {}
            for _tid, _cols in topo_logs.items():
                if not isinstance(_cols, list):
                    continue
                active_coll_map[str(_tid)] = [c.get("id") for c in _cols if isinstance(c, dict) and c.get("active")]

        
        else:
            # Ensure a consistent {topo_id -> [collective_ids]} structure
            norm_map = {}
            for _tid, _ids in (active_coll_map or {}).items():
                if _ids is None:
                    norm_map[str(_tid)] = []
                    continue
                if isinstance(_ids, set):
                    _ids = list(_ids)
                if not isinstance(_ids, (list, tuple)):
                    _ids = [_ids]
                out_ids = []
                for _x in _ids:
                    try:
                        out_ids.append(int(_x))
                    except Exception:
                        pass
                norm_map[str(_tid)] = out_ids
            active_coll_map = norm_map
# If we do not have a target collective yet, pick the first active collective on the active topology (if any).
        if target_cid is None and active_topo_id is not None:
            _tid_key = str(active_topo_id)
            _cols = topo_logs.get(_tid_key) or topo_logs.get(int(active_topo_id)) or []
            if isinstance(_cols, list) and _cols:
                # Prefer active collectives.
                _actives = [c.get("id") for c in _cols if isinstance(c, dict) and c.get("active")]
                target_cid = (_actives[0] if _actives else (_cols[0].get("id") if isinstance(_cols[0], dict) else None))

        # Align chunk filter store with the selected target collective (per-collective persistence)
        chunk_ids_for_target = chunk_ids
        if active_topo_id is not None and target_cid is not None:
            _tid_key = str(active_topo_id)
            _cols = topo_logs.get(_tid_key) or topo_logs.get(int(active_topo_id)) or []
            for _c in (_cols or []):
                if isinstance(_c, dict) and str(_c.get("id")) == str(target_cid):
                    chunk_ids_for_target = _c.get("chunk_filter_ids") or []
                    break


        # 4. PREPARE ELEMENTS
        elements = []
        if active_topo_id and multi_topos:
            # Find the path for the active ID
            active_path = next((t["path"] for t in multi_topos if int(t["id"]) == int(active_topo_id)), None)
            if active_path:
                # Pre-warm the cache so the graph displays immediately
                _get_or_create_topo_state(active_topo_id, active_path)
                
                # Retrieve the elements we just loaded
                if int(active_topo_id) in TOPOLOGY_STATE:
                    # Branch based on the current state / selection.
                    elements = TOPOLOGY_STATE[int(active_topo_id)]["elements"]
                
                # Also ensure global TOPO_FILE is synced
                global TOPO_FILE
                TOPO_FILE = active_path

        zoom_label = f"{int(round(zoom * 100))}%"
        
        return (
            f"Loaded session from {os.path.basename(p)}", active_panel, cap_range, edge_types, color_mode, iso_on, iso_snap,
            hidden_nodes, seg, ch.get("id"), nd.get("id"), selected_nodes, layout, zoom, pan, zoom_label, True,
            plot_mode, node_ids, chunk_ids_for_target,
            target_cid, editing_cid, active_coll_map, param_filter_store, right_panel_history,
            multi_topos, active_topo_id, topo_logs, multi_logs_for_restore, global_log_selection, topo_states,
            elements  # <--- Returning elements here forces the graph to appear
        )
        
    except FileNotFoundError:
        # Recover from a failure case and return a safe default.
        return (f"Session file not found: {path}",) + (no_update,) * 31
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return (f"Failed to load session: {e}",) + (no_update,) * 31

@app.callback(
    Output("session-file-path", "data"),
    Input("session-path-input", "value"),
    prevent_initial_call=True
)
def set_session_path_store(val):
    # Set session path store.
    if not val:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    # Resolve and validate filesystem paths before using them.
    p = os.path.expanduser(val)
    if not os.path.isabs(p):
        # Validate inputs / state before continuing.
        # Resolve and validate filesystem paths before using them.
        p = os.path.join(BASE_DIR, p)
    return p

# =========================
# Logs (upload + load)
# =========================
@app.callback(
    Output("log-path-input", "value"),
    Output("data-status", "children", allow_duplicate=True),
    Input("upload-log", "contents"),
    State("upload-log", "filename"),
    prevent_initial_call=True
)
def handle_upload(contents, filename):
    # Read and parse one or more log files from disk into the structures used by the visualizer.
    if not contents or not filename:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    try:
        content_type, content_string = contents.split(',')
        decoded = base64.b64decode(content_string)
        # Resolve and validate filesystem paths before using them.
        safe_name = os.path.basename(filename)
        # Resolve and validate filesystem paths before using them.
        out_path = os.path.join(UPLOAD_DIR, safe_name)
        with open(out_path, "wb") as f:
            # Open the file and ensure it is closed correctly.
            f.write(decoded)
        return out_path, f"Uploaded to {out_path}. Click 'Load Log' to read it."
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return no_update, f"Upload failed: {e}"


@app.callback(
    Output("xy-plot", "figure"),
    Input("xy-x-select", "value"),
    Input("xy-y-select", "value"),
    Input("segment-range", "value"),
    Input("active-collectives-map", "data"),
    Input("chunk-filter-ids", "data"),
    Input("node-filter-ids", "data"),
    Input("isolate-mode", "data"),
    Input("isolate-snapshot", "data"),
    Input("hidden-nodes", "data"),
    State("elements-base", "data"),
    Input("topology-radio", "value"),
    State("topo-logs", "data"),
    Input("xy-mode-toggle", "value"),  # <--- NEW INPUT
    prevent_initial_call=False
)
def build_xy_plot(x_sel, y_sel, seg, active_coll_map,
                  chunk_filter_ids, node_filter_ids, isolate_mode, isolate_snapshot,
                  hidden_nodes, elements_base, active_topo_id, topo_logs, 
                  xy_mode):  # <--- NEW ARGUMENT

    import numpy as np
    import pandas as pd
    import plotly.graph_objects as go

    title = f"{y_sel or ''} vs {x_sel or ''}"
    fig = go.Figure()

    if not x_sel or not y_sel:
        fig.update_layout(title="Custom X/Y", xaxis_title="", yaxis_title="")
        return fig

    t0, t1 = (seg or [TIME_MIN, TIME_MAX])
    t0 = float(t0); t1 = float(t1)
    if t1 < t0: t0, t1 = t1, t0
    N = 200 if t1 > t0 else 1
    t = np.linspace(t0, t1, N, dtype=float)

    # Resolve active logs
    logs = _get_active_log_bundles(active_coll_map, active_topo_id, topo_logs)
    
    if not logs:
        fig.add_annotation(text="No active logs selected.",
                           xref="paper", yref="paper", x=0.02, y=0.98, showarrow=False, align="left")
        fig.update_layout(margin=dict(l=40, r=10, t=48, b=40), title=title)
        return fig

    # Map collective id -> collective object (used to resolve active data-var selection per log).
    coll_by_id = {}
    if active_topo_id:
        tid = str(active_topo_id)
        for _coll in (topo_logs or {}).get(tid, []):
            try:
                coll_by_id[int(_coll.get("id"))] = _coll
            except Exception:
                continue

    # =========================================================
    #  MODE A: LINK VARIABLES (New Logic)
    # =========================================================
    if xy_mode == "link":
        # We assume X=Time and Y=LinkVarName
        # We calculate Total Y (Sum over all edges) at each time step t
        any_data = False
        seen_colls = set()

        for i, log_bundle in enumerate(logs):
            # 1. Collective/Log Metadata
            cid = log_bundle.get('_coll_id')
            # Check hidden params
            hidden_params = set()
            if cid is not None and active_topo_id:
                tid = str(active_topo_id)
                for c_obj in (topo_logs or {}).get(tid, []):
                    if str(c_obj.get("id")) == str(cid):
                        hidden_params = set(c_obj.get("hidden_params", []))
                        break
            
            if y_sel in hidden_params: continue

            # 2. Get Visualizer
            lid = int(log_bundle.get("id"))
            V = MULTI_VIZ_OBJS.get(lid)
            if not V: continue

            # 3. Find the Link Variable object
            target_var = None
            for lv in getattr(V, "link_vars", []):
                if lv.name == y_sel:
                    target_var = lv
                    break
            
            if not target_var: continue

            # 4. Compute Total Flow (Sum of all links)
            # target_var.per_link = { (src,dst): [(t, val), ...], ... }
            total_series = np.zeros_like(t)
            
            # Iterate ALL links in this variable
            # (Note: we could optimize by filtering links visible in the graph, 
            #  but usually "Total Flow" implies the whole network state)
            for (_src, _dst), series in target_var.per_link.items():
                if not series: continue
                # series is list of (time, val). Values are step functions.
                # We need to sample this series at times `t`.
                
                # Unzip
                times = np.array([pt[0] for pt in series])
                vals  = np.array([pt[1] for pt in series])
                
                # `searchsorted` gives the index where `t` would be inserted.
                # Since these are step functions (value holds until next change),
                # we want the value at index `idx - 1`.
                idx = np.searchsorted(times, t, side='right') - 1
                
                # Fix indices < 0 (before first event -> value is 0)
                valid_mask = idx >= 0
                
                # Accumulate
                # Create a temp array for this link's contribution
                link_contrib = np.zeros_like(t)
                link_contrib[valid_mask] = vals[idx[valid_mask]]
                
                total_series += link_contrib

            # 5. Plot
            coll_name = log_bundle.get('_coll_name') or log_bundle.get('label')
            coll_color = log_bundle.get('_coll_color') or log_bundle.get('color') or _next_color(i)
            lg = str(cid) if cid is not None else str(coll_name)
            showlegend = lg not in seen_colls
            seen_colls.add(lg)

            fig.add_trace(go.Scatter(
                x=t, y=total_series, 
                mode="lines", 
                name=f"{coll_name} (Total)", 
                line=dict(color=coll_color), 
                legendgroup=lg, 
                showlegend=showlegend
            ))
            any_data = True

        if not any_data:
             fig.add_annotation(text="No link data found for selection.", xref="paper", yref="paper", x=0.5, y=0.5, showarrow=False)

        fig.update_layout(
            title=f"Total {y_sel} over Time", 
            xaxis_title="Time", 
            yaxis_title=f"Sum({y_sel})",
            margin=dict(l=40, r=10, t=48, b=40), 
            hovermode="closest"
        )
        return fig


    # =========================================================
    #  MODE B: DATA/CHUNK VARIABLES (Legacy Logic)
    # =========================================================

    allowed_nodes = _visible_node_ids(elements_base or ELEMS, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes)
    allowed_nodes = set(n for n in allowed_nodes if n not in SWITCH_IDS)

    # --- KEY CHANGE: Get logs from Collectives ---
    logs = _get_active_log_bundles(active_coll_map, active_topo_id, topo_logs)
    
    if not logs:
        fig.add_annotation(text="No active logs selected.",
                           xref="paper", yref="paper", x=0.02, y=0.98, showarrow=False, align="left")
        fig.update_layout(margin=dict(l=40, r=10, t=48, b=40), title=title)
        return fig

    # ... (Rest of build_xy_plot remains identical, just uses 'logs') ...
    # Ensure build_series_funcs_for_log uses MULTI_VIZ_OBJS properly
    
    
    def build_series_funcs_for_log(log_bundle):
        # Resolve collective selection for this log (explicit "(none)" must suppress chunk/data visuals).
        _cid = log_bundle.get("_coll_id")
        try:
            _cid_int = int(_cid) if _cid is not None else None
        except Exception:
            _cid_int = None

        coll_obj = coll_by_id.get(_cid_int) if _cid_int is not None else None
        coll_obj = coll_obj or {}

        explicit_none = False
        explicit_key = ("active_data_param" in coll_obj)
        if explicit_key:
            _raw = coll_obj.get("active_data_param")
            if _raw is None or str(_raw).strip().lower() in ("", "__none__", "none", "(none)"):
                explicit_none = True

        # Per-log visualizer.
        lid = None
        V = None
        try:
            lid = int(log_bundle.get("id"))
        except Exception:
            lid = None

        if lid is not None:
            V = MULTI_VIZ_OBJS.get(lid)
            if V is None:
                path = log_bundle.get("path", "")
                try:
                    if str(path).lower().endswith(".json"):
                        V = JsonVisualizer(path, TOPO_FILE)
                    else:
                        V = interactiveinfo.Visualizer(path, TOPO_FILE)
                    MULTI_VIZ_OBJS[lid] = V
                except Exception:
                    V = None

        # Resolve active data var object for this collective/log.
        dv = None if explicit_none else _select_data_var_for_collective(V, coll_obj)

        # Build sends DF:
        # - explicit "(none)" => empty
        # - explicit selection but not found => empty
        # - auto selection fallback => use resolved dv when available, otherwise the bundle's precomputed sends
        sends_list = []
        if explicit_none:
            sends_list = []
        elif dv is not None:
            sends_list = getattr(dv, "sends", []) or []
        else:
            if explicit_key:
                sends_list = []  # do not silently fall back on explicit selection mismatch
            else:
                sends_list = log_bundle.get("sends") or []

        df = pd.DataFrame(sends_list)

        # Identify time columns.
        s_col = e_col = None
        for cand_s, cand_e in [("t_start", "t_end"), ("t0", "t1"), ("start", "end"), ("begin", "finish")]:
            if cand_s in df.columns and cand_e in df.columns:
                s_col, e_col = cand_s, cand_e
                break

        if s_col:
            df[s_col] = pd.to_numeric(df[s_col], errors="coerce")
            df[e_col] = pd.to_numeric(df[e_col], errors="coerce")
            df = df.dropna(subset=[s_col, e_col])

            if chunk_filter_ids and any(c in df.columns for c in ("chunk", "chunk_id", "cid")):
                col = next(c for c in ("chunk", "chunk_id", "cid") if c in df.columns)
                allowed_chunks = set(map(int, chunk_filter_ids))
                df = df[pd.to_numeric(df[col], errors="coerce").isin(list(allowed_chunks))]

            if "src" in df.columns and "dst" in df.columns and allowed_nodes:
                df["src"] = pd.to_numeric(df["src"], errors="coerce")
                df["dst"] = pd.to_numeric(df["dst"], errors="coerce")
                if df["src"].notna().any() or df["dst"].notna().any():
                    df = df[df["src"].isin(allowed_nodes) | df["dst"].isin(allowed_nodes)]

            df = df.sort_values([s_col, e_col])
            df["duration"] = (df[e_col] - df[s_col]).clip(lower=0.0)
            ev_mask = (df[e_col] >= t0) & (df[e_col] <= t1)
        else:
            ev_mask = None

        # Chunk start/finish maps: prefer dv's lifecycle when available.
        if dv is not None:
            clc = getattr(dv, "chunkLifeCycle", [])
            fin_map = _compute_chunk_finish_times_from_lifecycle(clc)
            start_map = _compute_chunk_start_times_from_lifecycle(clc)
        else:
            fin_map = {}
            start_map = {}

        def series_time():
            return t.copy()

        def series_wip():
            if s_col is not None and not df.empty:
                s_arr = np.sort(df[s_col].to_numpy(dtype=float))
                e_arr = np.sort(df[e_col].to_numpy(dtype=float))
                return (np.searchsorted(s_arr, t, side="right") -
                        np.searchsorted(e_arr, t, side="right")).astype(float)
            starts_arr = np.sort(np.array([float(v) for v in (start_map or {}).values()], dtype=float))
            fins_arr = np.sort(np.array([float(v) for v in (fin_map or {}).values()], dtype=float))
            if starts_arr.size == 0 or fins_arr.size == 0:
                return np.full_like(t, np.nan, dtype=float)
            return (np.searchsorted(starts_arr, t, side="right") -
                    np.searchsorted(fins_arr, t, side="right")).astype(float)

        def series_cum_finished():
            fins_arr = np.sort(np.array([float(v) for v in (fin_map or {}).values()], dtype=float))
            if fins_arr.size == 0 and s_col is not None and not df.empty:
                fins_arr = np.sort(df[e_col].to_numpy(dtype=float))
            if fins_arr.size == 0:
                return np.full_like(t, np.nan, dtype=float)
            return np.searchsorted(fins_arr, t, side="right").astype(float)

        def series_avg_send_duration():
            if s_col is None or df.empty:
                return np.full_like(t, np.nan, dtype=float)
            dt = (t[1] - t[0]) if len(t) > 1 else 1.0
            edges = np.concatenate([t - 0.5 * dt, [t[-1] + 0.5 * dt]])
            idx = np.clip(np.digitize(df[e_col].to_numpy(dtype=float), edges) - 1, 0, len(t) - 1)
            num = np.bincount(idx, weights=df["duration"].to_numpy(dtype=float), minlength=len(t)).astype(float)
            den = np.bincount(idx, minlength=len(t)).astype(float)
            with np.errstate(divide="ignore", invalid="ignore"):
                y = np.where(den > 0, num / den, np.nan)
            return y

        def series_postleft_avg():
            # Average "chunks left to receive" across allowed nodes, for the selected data var.
            if dv is None or (not allowed_nodes):
                return np.full_like(t, np.nan, dtype=float)

            node_lc = getattr(dv, "nodeLifeCycle", [])
            allowed_chunks = set(int(c) for c in (chunk_filter_ids or [])) if chunk_filter_ids else None

            per_host = []
            for r in allowed_nodes:
                if r >= len(node_lc):
                    continue
                arrivals_dict = node_lc[r]
                firsts = []
                for cid, arrivals in (arrivals_dict or {}).items():
                    try:
                        icid = int(cid)
                    except Exception:
                        continue
                    if allowed_chunks is not None and icid not in allowed_chunks:
                        continue
                    if not arrivals:
                        continue
                    try:
                        earliest = _safe_min(
                            [float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != "seed")],
                            default=0.0
                        )
                    except Exception:
                        continue
                    firsts.append(earliest)

                firsts = np.sort(np.array(firsts, dtype=float))
                tot = float(firsts.size)
                if tot == 0:
                    per_host.append(np.zeros_like(t, dtype=float))
                else:
                    per_host.append(tot - np.searchsorted(firsts, t, side="right").astype(float))

            if not per_host:
                return np.full_like(t, np.nan, dtype=float)
            Y = np.vstack(per_host).astype(float)
            return np.nanmean(Y, axis=0)

        SERIES_FUNCS = {
            "time": series_time,
            "wip": series_wip,
            "cum_finished": series_cum_finished,
            "avg_send_duration": series_avg_send_duration,
            "postleft_avg": series_postleft_avg,
        }

        def is_series(sel):
            return sel in SERIES_FUNCS

        def is_event(sel):
            return sel in ("send_start_time", "send_end_time", "send_duration")

        def event_vals(sel):
            if ev_mask is None or df.empty:
                return np.array([]), np.array([])
            times = df.loc[ev_mask, e_col].to_numpy(dtype=float)
            if sel == "send_start_time":
                vals = df.loc[ev_mask, s_col].to_numpy(dtype=float)
            elif sel == "send_end_time":
                vals = df.loc[ev_mask, e_col].to_numpy(dtype=float)
            elif sel == "send_duration":
                vals = df.loc[ev_mask, "duration"].to_numpy(dtype=float)
            else:
                vals = np.array([])
            return times, vals

        return SERIES_FUNCS, is_series, is_event, event_vals, df

    # ... (Rendering loop remains identical) ...
    def kind(sel, is_series, is_event):
        # Kind.
        if is_series(sel): return "series"
        if is_event(sel):  return "event"
        return "unknown"

    any_data = False
    for i, log in enumerate(logs):
        SERIES_FUNCS, is_series, is_event, event_vals, df = build_series_funcs_for_log(log)
        kx = kind(x_sel, is_series, is_event)
        ky = kind(y_sel, is_series, is_event)
        name = f"[{log['id']}] {log['label']}"
        color = log.get("color") or _next_color(i)

        if kx == "series" and ky == "series":
            X = SERIES_FUNCS[x_sel](); Y = SERIES_FUNCS[y_sel]()
            mask = np.isfinite(X) & np.isfinite(Y)
            if mask.sum() > 0:
                fig.add_trace(go.Scatter(x=X[mask], y=Y[mask], mode="lines", name=name, line=dict(color=color)))
                any_data = True
            continue

        if kx == "event" and ky == "event":
            _tx, X = event_vals(x_sel); _ty, Y = event_vals(y_sel)
            K = min(len(X), len(Y))
            if K > 0:
                fig.add_trace(go.Scatter(x=X[:K], y=Y[:K], mode="markers", name=name, marker=dict(size=5, opacity=0.6, color=color)))
                any_data = True
            continue

        if kx == "series" and ky == "event":
            ty, Vy = event_vals(y_sel)
            if len(Vy) > 0:
                X_series = SERIES_FUNCS[x_sel]()
                X = np.interp(ty, t, X_series)
                fig.add_trace(go.Scatter(x=X, y=Vy, mode="markers", name=name, marker=dict(size=5, opacity=0.6, color=color)))
                any_data = True
            continue

        if kx == "event" and ky == "series":
            tx, Vx = event_vals(x_sel)
            if len(Vx) > 0:
                Y_series = SERIES_FUNCS[y_sel]()
                Y = np.interp(tx, t, Y_series)
                fig.add_trace(go.Scatter(x=Vx, y=Y, mode="markers", name=name, marker=dict(size=5, opacity=0.6, color=color)))
                any_data = True
            continue

    if not any_data:
        fig.add_annotation(text="XY has no data in current selection/segment.", xref="paper", yref="paper", x=0.5, y=0.5, showarrow=False)

    fig.update_layout(
        title=title, xaxis_title=x_sel, yaxis_title=y_sel,
        margin=dict(l=40, r=10, t=48, b=40), uirevision="xy",
        hovermode="closest",
        legend=dict(orientation="h", yanchor="bottom", y=1.02, xanchor="left", x=0),
    )
    return fig

@app.callback(
    Output("download-xy-data", "data"),
    Output("xy-export-status", "children"),
    Input("btn-xy-export-csv", "n_clicks"),
    State("xy-x-select", "value"),
    State("xy-y-select", "value"),
    State("segment-range", "value"),
    State("store-sends", "data"),
    State("store-chunk-finish-times", "data"),
    State("store-chunk-start-times", "data"),
    State("chunk-filter-ids", "data"),
    State("node-filter-ids", "data"),
    State("isolate-mode", "data"),
    State("isolate-snapshot", "data"),
    State("hidden-nodes", "data"),
    State("elements-base", "data"),
    prevent_initial_call=True
)
def export_current_xy(n_csv, x_sel, y_sel, seg,
                      sends_rec, fin_map, start_map, chunk_filter_ids,
                      node_filter_ids, isolate_mode, isolate_snapshot,
                      hidden_nodes, elements_base):
    import numpy as np
    import pandas as pd
    from dash import no_update, dcc
    import dash

    ctx = dash.callback_context
    if not ctx.triggered:
        return no_update, no_update

    if not x_sel or not y_sel:
        return no_update, "Choose X and Y first."

    t0, t1 = (seg or [TIME_MIN, TIME_MAX])
    t0 = float(t0); t1 = float(t1)
    if t1 < t0: t0, t1 = t1, t0
    N_SERIES_EXPORT = 1000 if t1 > t0 else 1
    t = np.linspace(t0, t1, N_SERIES_EXPORT, dtype=float)

    allowed_nodes = _visible_node_ids(elements_base or ELEMS, node_filter_ids, isolate_mode, isolate_snapshot, hidden_nodes)
    allowed_nodes = set(n for n in allowed_nodes if n not in SWITCH_IDS)

    df = pd.DataFrame(sends_rec or [])
    s_col = e_col = None
    for cand_s, cand_e in [("t_start","t_end"), ("t0","t1"), ("start","end"), ("begin","finish")]:
        if cand_s in df.columns and cand_e in df.columns:
            s_col, e_col = cand_s, cand_e
            break
    if s_col:
        df[s_col] = pd.to_numeric(df[s_col], errors="coerce")
        df[e_col] = pd.to_numeric(df[e_col], errors="coerce")
        df = df.dropna(subset=[s_col, e_col])
        if chunk_filter_ids and any(c in df.columns for c in ("chunk", "chunk_id", "cid")):
            col = next(c for c in ("chunk","chunk_id","cid") if c in df.columns)
            allowed_chunks = set(map(int, chunk_filter_ids))
            df = df[pd.to_numeric(df[col], errors="coerce").isin(list(allowed_chunks))]
        if "src" in df.columns and "dst" in df.columns and allowed_nodes:
            df["src"] = pd.to_numeric(df["src"], errors="coerce")
            df["dst"] = pd.to_numeric(df["dst"], errors="coerce")
            if df["src"].notna().any() or df["dst"].notna().any():
                df = df[df["src"].isin(allowed_nodes) | df["dst"].isin(allowed_nodes)]
        df = df.sort_values([s_col, e_col])
        df["duration"] = (df[e_col] - df[s_col]).clip(lower=0.0)
        ev_mask = (df[e_col] >= t0) & (df[e_col] <= t1)
    else:
        ev_mask = None

    def series_time():
        # Series time.
        return t.copy()

    def series_wip():
        # Series wip.
        if s_col is not None and not df.empty:
            # Validate inputs / state before continuing.
            s_arr = np.sort(df[s_col].to_numpy(dtype=float))
            e_arr = np.sort(df[e_col].to_numpy(dtype=float))
            return (np.searchsorted(s_arr, t, side="right") -
                    np.searchsorted(e_arr, t, side="right")).astype(float)
        starts_arr = np.sort(np.array([float(v) for v in (start_map or {}).values()], dtype=float))
        fins_arr   = np.sort(np.array([float(v) for v in (fin_map   or {}).values()], dtype=float))
        if starts_arr.size == 0 or fins_arr.size == 0:
            # Branch based on the current state / selection.
            return np.full_like(t, np.nan, dtype=float)
        return (np.searchsorted(starts_arr, t, side="right") -
                np.searchsorted(fins_arr,   t, side="right")).astype(float)

    def series_cum_finished():
        # Series cum finished.
        fins_arr = np.sort(np.array([float(v) for v in (fin_map or {}).values()], dtype=float))
        if fins_arr.size == 0 and s_col is not None and not df.empty:
            # Validate inputs / state before continuing.
            fins_arr = np.sort(df[e_col].to_numpy(dtype=float))
        if fins_arr.size == 0:
            # Branch based on the current state / selection.
            return np.full_like(t, np.nan, dtype=float)
        return np.searchsorted(fins_arr, t, side="right").astype(float)

    def series_avg_send_duration():
        # Series avg send duration.
        if s_col is None or df.empty:
            # Validate inputs / state before continuing.
            return np.full_like(t, np.nan, dtype=float)
        dt = (t[1] - t[0]) if len(t) > 1 else 1.0
        edges = np.concatenate([t - 0.5 * dt, [t[-1] + 0.5 * dt]])
        idx   = np.clip(np.digitize(df[e_col].to_numpy(dtype=float), edges) - 1, 0, len(t) - 1)
        num   = np.bincount(idx, weights=df["duration"].to_numpy(dtype=float), minlength=len(t)).astype(float)
        den   = np.bincount(idx, minlength=len(t)).astype(float)
        with np.errstate(divide="ignore", invalid="ignore"):
            # Use a context manager to manage resources safely.
            y = np.where(den > 0, num / den, np.nan)
        return y

    def series_postleft_avg():
        # Series postleft avg.
        if VIZ is None or not allowed_nodes:
            # Validate inputs / state before continuing.
            return np.full_like(t, np.nan, dtype=float)
        node_lc = getattr(VIZ, "nodeLifeCycle", [])
        allowed_chunks = set(int(c) for c in (chunk_filter_ids or [])) if chunk_filter_ids else None
        per_host = []
        for r in allowed_nodes:
            # Iterate over the relevant items and accumulate results.
            if r >= len(node_lc): 
                # Branch based on the current state / selection.
                continue
            arrivals_dict = node_lc[r]
            firsts = []
            for cid, arrivals in (arrivals_dict or {}).items():
                # Iterate over the relevant items and accumulate results.
                try:
                    icid = int(cid)
                except Exception:
                    # Recover from a failure case and return a safe default.
                    continue
                if allowed_chunks is not None and icid not in allowed_chunks:
                    # Validate inputs / state before continuing.
                    continue
                if not arrivals:
                    # Validate inputs / state before continuing.
                    continue
                try:
                    earliest = (_safe_min([float(ts) for (ts, _msg) in arrivals if (_msg is None or str(_msg).lower() != 'seed')], default=0.0))
                except Exception:
                    # Recover from a failure case and return a safe default.
                    continue
                firsts.append(earliest)
            firsts = np.sort(np.array(firsts, dtype=float))
            tot = float(firsts.size)
            if tot == 0:
                # Branch based on the current state / selection.
                per_host.append(np.zeros_like(t, dtype=float))
            else:
                per_host.append(tot - np.searchsorted(firsts, t, side="right").astype(float))
        if not per_host:
            # Validate inputs / state before continuing.
            return np.full_like(t, np.nan, dtype=float)
        Y = np.vstack(per_host).astype(float)
        return np.nanmean(Y, axis=0)

    SERIES_FUNCS = {
        "time": series_time,
        "wip": series_wip,
        "cum_finished": series_cum_finished,
        "avg_send_duration": series_avg_send_duration,
        "postleft_avg": series_postleft_avg,
    }

    def event_vals(sel):
        # Event vals.
        if ev_mask is None or df.empty:
            # Validate inputs / state before continuing.
            return np.array([]), np.array([])
        times = df.loc[ev_mask, e_col].to_numpy(dtype=float)
        if sel == "send_start_time":
            # Branch based on the current state / selection.
            vals = df.loc[ev_mask, s_col].to_numpy(dtype=float)
        elif sel == "send_end_time":
            # Alternative branch for a different condition.
            vals = df.loc[ev_mask, e_col].to_numpy(dtype=float)
        elif sel == "send_duration":
            # Alternative branch for a different condition.
            vals = df.loc[ev_mask, "duration"].to_numpy(dtype=float)
        else:
            vals = np.array([])
        return times, vals

    def is_series(sel): return sel in SERIES_FUNCS
    def is_event(sel):  return sel in ("send_start_time", "send_end_time", "send_duration")

    X, Y = None, None
    if is_series(x_sel) and is_series(y_sel):
        # Is series.
        X = SERIES_FUNCS[x_sel](); Y = SERIES_FUNCS[y_sel]()
        mask = np.isfinite(X) & np.isfinite(Y)
        X, Y = X[mask], Y[mask]

    elif is_event(x_sel) and is_event(y_sel):
        _tx, X = event_vals(x_sel)
        _ty, Y = event_vals(y_sel)
        K = min(len(X), len(Y))
        X, Y = X[:K], Y[:K]

    elif is_series(x_sel) and is_event(y_sel):
        ty, Vy = event_vals(y_sel)
        if len(Vy) == 0:
            X = np.array([]); Y = np.array([])
        else:
            X_series = SERIES_FUNCS[x_sel]()
            X = np.interp(ty, t, X_series)
            Y = Vy

    elif is_event(x_sel) and is_series(y_sel):
        tx, Vx = event_vals(x_sel)
        if len(Vx) == 0:
            X = np.array([]); Y = np.array([])
        else:
            Y_series = SERIES_FUNCS[y_sel]()
            X = Vx
            Y = np.interp(tx, t, Y_series)
    else:
        X = np.array([]); Y = np.array([])

    if X is None or Y is None or len(X) == 0 or len(Y) == 0:
        return no_update, "XY has no data to export."

    k = min(len(X), len(Y))
    df_out = pd.DataFrame({"x": np.asarray(X[:k]).ravel(), "y": np.asarray(Y[:k]).ravel()})
    base = f"xy_{str(x_sel).strip().replace(' ', '_')}_vs_{str(y_sel).strip().replace(' ', '_')}"
    return dcc.send_data_frame(df_out.to_csv, f"{base}.csv", index=False), f"Exported {len(df_out)} rows (CSV)."


@app.callback(
    Output("segment-range", "min"),
    Output("segment-range", "max"),
    Output("segment-range", "step"),
    Output("segment-range", "value", allow_duplicate=True),
    Input("time-min", "data"),
    Input("time-max", "data"),
    Input("slider-step", "data"),
    prevent_initial_call=True
)
def update_segment_slider(minv, maxv, _step_unused):
    # Update segment slider.
    if minv is None or maxv is None:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    return float(minv), float(maxv), None, [float(minv), float(maxv)]

# =========================
# Run
# =========================
# Multi-log management (XY overlay only)
# =========================


@app.callback(
    Output("time-max", "data", allow_duplicate=True),
    Input("active-collectives-map", "data"),
    Input("topology-radio", "value"),
    Input("topo-logs", "data"),
    State("time-max", "data"),
    prevent_initial_call=True
)
def sync_tmax_with_selected_collectives(active_coll_map, active_topo_id, topo_collectives, prev):
    # Recompute tmax based ONLY on the currently selected (active) collectives in the active topology.
    # This keeps the global time window aligned with what the user is actually viewing.
    if not active_topo_id:
        raise PreventUpdate

    tid = str(active_topo_id)
    collectives = (topo_collectives or {}).get(tid, [])
    raw_actives = (active_coll_map or {}).get(tid, [])

    active_cids = set()
    for x in (raw_actives or []):
        try:
            active_cids.add(int(x))
        except Exception:
            continue

    tmax_vals = []
    for coll in (collectives or []):
        try:
            cid = int(coll.get("id"))
        except Exception:
            continue
        if cid not in active_cids:
            continue

        for lb in (coll.get("logs") or []):
            if not isinstance(lb, dict):
                continue

            # Prefer stored tmax from the log bundle; fall back to the in-memory VIZ object if needed.
            tm = lb.get("tmax", None)
            if tm is None:
                try:
                    lid = int(lb.get("id", -1))
                except Exception:
                    lid = -1
                V = MULTI_VIZ_OBJS.get(lid)
                tm = getattr(V, "tmax", None) if V is not None else None

            if tm is None:
                continue

            try:
                tmax_vals.append(float(tm))
            except Exception:
                continue

    if not tmax_vals:
        # If nothing is currently selected (or nothing loaded yet), keep the existing tmax stable.
        if prev is None:
            raise PreventUpdate
        return prev

    return float(max(tmax_vals))


@app.callback(
    Output("active-panel", "data", allow_duplicate=True),
    Output("filters-submode", "data", allow_duplicate=True),
    Input("btn-node-filters-shortcut", "n_clicks"),
    Input("btn-links-filters-shortcut", "n_clicks"),
    Input("btn-chunks-filters-shortcut", "n_clicks"),
    prevent_initial_call=True
)
def shortcut_to_filters(n_node, n_links, n_chunks):
    # Apply the current filter settings and compute the resulting subset for display.
    # Inspect Dash's callback context to see what triggered this update.
    ctx = dash.callback_context
    if not ctx.triggered:
        # Validate inputs / state before continuing.
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    which = ctx.triggered[0]["prop_id"].split(".")[0]
    if which == "btn-node-filters-shortcut":
        # Branch based on the current state / selection.
        sub = "nodes"
    elif which == "btn-links-filters-shortcut":
        # Alternative branch for a different condition.
        sub = "links"
    elif which == "btn-chunks-filters-shortcut":
        # Alternative branch for a different condition.
        sub = "chunks"
    else:
        # Stop here to avoid updating outputs when the callback should not run yet.
        raise PreventUpdate
    return "filters", sub

@app.callback(
    Output("multi-logs", "data", allow_duplicate=True),
    Output("topo-logs", "data", allow_duplicate=True),
    Output("target-collective-id", "data", allow_duplicate=True),
    Output("active-collectives-map", "data", allow_duplicate=True),
    Output("data-status", "children", allow_duplicate=True),
    Output("time-min", "data", allow_duplicate=True),
    Output("time-max", "data", allow_duplicate=True),
    Output("slider-step", "data", allow_duplicate=True),
    Output("store-sends", "data", allow_duplicate=True),
    Output("store-chunk-finish-times", "data", allow_duplicate=True),
    Output("store-chunk-start-times", "data", allow_duplicate=True),
    Output("chunk-events", "data", allow_duplicate=True),
    Output("chunk-presence", "data", allow_duplicate=True),
    Output("node-contents", "data", allow_duplicate=True),
    Output("node-events", "data", allow_duplicate=True),
    Output("segment-range", "value", allow_duplicate=True),
    
    Input("load-log-btn", "n_clicks"),
    State("log-path-input", "value"),
    State("target-collective-id", "data"),
    State("topology-radio", "value"),
    State("topo-logs", "data"),
    State("active-collectives-map", "data"),
    State("multi-logs", "data"),
    State("time-min", "data"),
    State("time-max", "data"),
    prevent_initial_call=True
)
def load_log_complete(_n, path, target_cid, active_tid, topo_collectives, active_coll_map, multi_logs, old_tmin, old_tmax):
    # Load and parse log data, then update the derived metrics used by plots and filters.
    # Stop here to avoid updating outputs when the callback should not run yet.
    if not _n: raise PreventUpdate
    
    # If no collective is targeted, warn the user
    if not target_cid:
        # Validate inputs / state before continuing.
        return (no_update,) * 15 + (no_update,)

    # Resolve and validate filesystem paths before using them.
    p = os.path.expanduser(path or "")
    # Resolve and validate filesystem paths before using them.
    if not os.path.isabs(p): p = os.path.join(BASE_DIR, p)
    
    if not os.path.exists(p):
        # Validate inputs / state before continuing.
        return (no_update, no_update, no_update, no_update, f"File not found: {p}", no_update, no_update, no_update, [], {}, {}, {"events": []}, None, None, {"events": []}, no_update)

    # 1. Init Visualizer (Set Global VIZ)
    global VIZ, TOPO_FILE
    try:
        # Load using the currently active topology file
        if str(p).lower().endswith(".json"):
            # Branch based on the current state / selection.
            V = JsonVisualizer(p, TOPO_FILE)
        else:
            V = interactiveinfo.Visualizer(p, TOPO_FILE)
        VIZ = V
    except Exception as e:
        # Recover from a failure case and return a safe default.
        return (no_update, no_update, no_update, no_update, f"Init failed: {e}", no_update, no_update, no_update, [], {}, {}, {"events": []}, None, None, {"events": []}, no_update)

    # 2. Create Log Bundle
    import time
    lid = int(time.time() * 10000)
    # Resolve and validate filesystem paths before using them.
    label = os.path.basename(p)
    color = _next_color(len(multi_logs or []))
    
    tmin, tmax = _time_bounds_from_viz()
    step = max(1.0, round((tmax - tmin) / 500.0, 3)) if tmax > tmin else 1.0

    df_sends = _extract_sends_df()
    finish_map = _compute_chunk_finish_times()
    start_map  = _compute_chunk_start_times()
    chunk_cnt = int(getattr(V, "chunkCount", 0))
    
    MULTI_VIZ_OBJS[lid] = V
    
    bundle = {
        "id": lid, "path": p, "label": label, "color": color,
        "tmin": tmin, "tmax": tmax, 
        "sends": df_sends.to_dict("records"),
        "fin_map": {int(k):v for k,v in finish_map.items()},
        "start_map": {int(k):v for k,v in start_map.items()},
        "chunk_count": chunk_cnt
    }
    
    # 3. Update Multi-Logs (Linear list for plots)
    multi_logs = multi_logs or []
    multi_logs.append(bundle)

    # 4. Insert into Topology -> Collective -> Logs
    topo_collectives = topo_collectives or {}
    tid = str(active_tid)
    collectives = topo_collectives.get(tid, [])
    coll_name = "?"
    
    found = False
    for coll in collectives:
        # Iterate over the relevant items and accumulate results.
        if str(coll["id"]) == str(target_cid):
            # Branch based on the current state / selection.
            coll["logs"].append(bundle)
            coll_name = coll["name"]
            found = True
            break
    
    if found:
        # Branch based on the current state / selection.
        topo_collectives[tid] = collectives

    # 5. Auto-activate the collective
    active_coll_map = active_coll_map or {}
    current_actives = active_coll_map.get(tid, [])
    if target_cid not in current_actives:
        # Validate inputs / state before continuing.
        current_actives.append(target_cid)
        active_coll_map[tid] = current_actives

    msg = f"Loaded {label} into '{coll_name}'."
    
    # Time window updates
    try:
        have_prev = (old_tmin is not None and old_tmax is not None and float(old_tmax) > 0.0)
    except: have_prev = False
    
    out_tmin = float(old_tmin) if have_prev else float(tmin)
    out_tmax = float(old_tmax) if have_prev else float(tmax)

    return (
        multi_logs,
        topo_collectives,
        target_cid,  # Keep target so you can load multiple logs into the same collective
        active_coll_map,
        msg,
        out_tmin,
        out_tmax,
        step,
        df_sends.to_dict("records"),
        finish_map,
        start_map,
        {"events": []},
        None,
        None,
        {"events": []},
        [out_tmin, out_tmax]
    )

@app.callback(
    Output("multi-logs", "data", allow_duplicate=True),
    Input("topology-radio", "value"),
    State("topo-logs", "data"),
    prevent_initial_call=True
)
def sync_collectives_to_multi(active_tid, topo_collectives):
    # Flattens the active topology's collectives into a list for the XY plotter
    # Sync collectives to multi.
    if not active_tid: return []
    tid = str(active_tid)
    collectives = (topo_collectives or {}).get(tid, [])
    all_logs = []
    for c in collectives:
        # Iterate over the relevant items and accumulate results.
        all_logs.extend(c.get("logs", []))
    return all_logs



if __name__ == "__main__":
    # print(f"[layout] Default preset path: {PRESET_FILE}")
    # print(f"[session] Default session path: {SESSION_FILE}")
    # print(f"[defaults] Named defaults file: {DEFAULTS_FILE}")
    # print(f"[groups] Node groups file: {GROUPS_FILE}")
    # print(f"[logs] Default .vis path: {LOG_FILE}")
    app.run(debug=True, host="0.0.0.0", port=8051)

# =========================\n# Logs \(upload \+ load\)\n# =========================
