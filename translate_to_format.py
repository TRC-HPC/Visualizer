import json
import re
import sys
import os

def identify_files(file_path_1, file_path_2):
    """
    Determines which file is the mapping file and which is the simulation file
    based on the header "[Chunk Elements Bytes]".
    """
    files = [file_path_1, file_path_2]
    mapping_file = None
    simulation_file = None

    for f_path in files:
        if not os.path.exists(f_path):
            print(f"Error: File not found: {f_path}")
            return None, None
            
        try:
            with open(f_path, 'r') as f:
                # Read the first non-empty line
                first_line = ""
                for line in f:
                    if line.strip():
                        first_line = line.strip()
                        break
                
                # Check for the specific header
                if first_line == "[Chunk Elements Bytes]":
                    mapping_file = f_path
                else:
                    simulation_file = f_path
        except Exception as e:
            print(f"Error reading {f_path}: {e}")
            return None, None

    return mapping_file, simulation_file

def parse_mapping_file(filename):
    """
    Parses the mapping file for Preconds, Postconds, and FlowInfo hex mappings.
    """
    precons = {}
    postcons = {}
    flow_info_map = {}
    
    print(f"Reading mapping data from: {filename}")
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            
            # Parse Postconditions
            match = re.match(r"Postcond (\d+): (.+)", line)
            if match:
                node_id = match.group(1)
                chunks = [int(x) for x in match.group(2).split()]
                postcons[node_id] = chunks
                continue
            
            # Parse Preconditions
            match = re.match(r"Precond (\d+): (.+)", line)
            if match:
                node_id = match.group(1)
                chunks = [int(x) for x in match.group(2).split()]
                precons[node_id] = chunks
                continue
                
            # Parse FlowInfo Hex Map
            match = re.match(r"FlowInfo\*=(0x[0-9a-fA-F]+) -> (.+)", line)
            if match:
                hex_val = match.group(1)
                chunks = [int(x) for x in match.group(2).split()]
                flow_info_map[hex_val] = chunks
                continue
                
    return precons, postcons, flow_info_map

def parse_simulation_file(filename, flow_info_map):
    """
    Parses the simulation log to generate Flow (link) and Dvars (data) events.
    """
    print(f"Reading simulation data from: {filename}")
    # --- NEW: Pre-scan to find the final simulation time ---
    final_sim_time = 0
    try:
        with open(filename, 'r') as f:
            for line in f:
                if line.startswith("Simulation time"):
                    match = re.search(r"Simulation time (\d+)ns", line)
                    if match:
                        final_sim_time = int(match.group(1))
        print(f"Final simulation time detected: {final_sim_time}ns")
    except Exception as e:
        print(f"Warning: Could not determine final time: {e}")
    # -------------------------------------------------------

    flow_events = [] 
    dvar_events = [] 
    
    active_flows = {} # flow_id -> {chunk_id, path}
    flow_hex_counters = {k: 0 for k in flow_info_map.keys()}
    pending_flows = {} 
    
    current_time = 0
    
    with open(filename, 'r') as f:
        for line in f:
            line = line.strip()
            
            # Simulation Time
            if line.startswith("Simulation time"):
                match = re.search(r"Simulation time (\d+)ns", line)
                if match:
                    current_time = int(match.group(1))
                continue
            
            # 1. Map Flow Info (Hex) to Chunk ID
            if line.startswith("Flow") and "info" in line:
                match = re.match(r"Flow #(\d+) info (0x[0-9a-fA-F]+)", line)
                if match:
                    fid = match.group(1)
                    hex_val = match.group(2)
                    
                    if hex_val in flow_info_map:
                        idx = flow_hex_counters[hex_val]
                        if idx < len(flow_info_map[hex_val]):
                            chunk_id = flow_info_map[hex_val][idx]
                            flow_hex_counters[hex_val] += 1
                        else:
                            chunk_id = flow_info_map[hex_val][-1] 
                            
                        if fid not in pending_flows:
                            pending_flows[fid] = {}
                        pending_flows[fid]['chunk'] = chunk_id
                continue
            
            # 2. Capture Flow Path
            if line.startswith("Flow") and "path" in line:
                match = re.match(r"Flow #(\d+) path #\d+ (.+)", line)
                if match:
                    fid = match.group(1)
                    nodes = [int(x) for x in match.group(2).split()]
                    if fid not in pending_flows:
                        pending_flows[fid] = {}
                    pending_flows[fid]['path'] = nodes
                continue
            
            # 3. Handle Flow Start (Transmitting) -> Generate 'start' events
            if line.startswith("Flow") and "transmitting" in line:
                match = re.match(r"Flow #(\d+) transmitting", line)
                if match:
                    fid = match.group(1)
                    if fid in pending_flows:
                        chunk_id = pending_flows[fid].get('chunk')
                        path = pending_flows[fid].get('path')
                        
                        if chunk_id is not None and path:
                            for i in range(len(path) - 1):
                                u, v = path[i], path[i+1]
                                
                                # LINK START
                                dvar_events.append({
                                    "time": current_time,
                                    "entity_id": [u, v],
                                    "src": u,
                                    "data_id": chunk_id,
                                    "enum": "start"
                                })
                                # NODE START
                                dvar_events.append({
                                    "time": current_time,
                                    "entity_id": v,
                                    "src": u,
                                    "data_id": chunk_id,
                                    "enum": "start"
                                })
                                
                            active_flows[fid] = {'chunk': chunk_id, 'path': path}
                continue
                
            # 4. Handle Link Throughput
            if line.startswith("Link"):
                match = re.match(r"Link \((\d+),(\d+)\) throughput (\d+)bps", line)
                if match:
                    u = int(match.group(1))
                    v = int(match.group(2))
                    throughput = int(match.group(3))
                    
                    flow_events.append({
                        "time": current_time,
                        "link": [u, v],
                        "flow": throughput
                    })
                continue
                
            # 5. Handle Flow Completion -> Generate 'leave' (link) and 'arrive' (node)
            if line.startswith("Flow") and "completed" in line:
                match = re.match(r"Flow #(\d+) completed", line)
                if match:
                    fid = match.group(1)
                    if fid in active_flows:
                        chunk = active_flows[fid]['chunk']
                        path = active_flows[fid]['path']
                        
                        for i in range(len(path) - 1):
                            u, v = path[i], path[i+1]
                            
                            # LINK LEAVE
                            dvar_events.append({
                                "time": current_time,
                                "entity_id": [u, v],
                                "src": u,
                                "data_id": chunk,
                                "enum": "leave"
                            })
                            # NODE ARRIVE
                            dvar_events.append({
                                "time": current_time,
                                "entity_id": v,
                                "src": u,
                                "data_id": chunk,
                                "enum": "arrive"
                            })
                            
                            # --- NEW: Reset Link Throughput to 0 ONLY at the final time ---
                            if current_time == final_sim_time:
                                flow_events.append({
                                    "time": current_time,
                                    "link": [u, v],
                                    "flow": 0
                                })
                            # --------------------------------------------------------------
                            
                        del active_flows[fid]
                continue

    return flow_events, dvar_events

def main():
    # 1. Get file paths
    if len(sys.argv) >= 3:
        file_input_1 = sys.argv[1]
        file_input_2 = sys.argv[2]
        output_file = sys.argv[3] if len(sys.argv) > 3 else 'merged_output.json'
    else:
        print("--- Merge Tool ---")
        file_input_1 = input("Enter path for the first file: ").strip().strip('"').strip("'")
        file_input_2 = input("Enter path for the second file: ").strip().strip('"').strip("'")
        output_name_input = input("Enter name for the output file (default: merged_output): ").strip()
        output_name_input = output_name_input + ".json"
        output_file = output_name_input if output_name_input else 'merged_output.json'
        print(f"Output will be saved to: {output_file}")

    # 2. Identify which file is which
    mapping_file, simulation_file = identify_files(file_input_1, file_input_2)
    
    if not mapping_file or not simulation_file:
        print("\n[!] FATAL ERROR: Could not identify the file types.")
        print("Ensure one file starts with '[Chunk Elements Bytes]' (the mapping file).")
        return

    print("\nFile Identification Successful:")
    print(f"  Mapping File:    {os.path.basename(mapping_file)}")
    print(f"  Simulation Log:  {os.path.basename(simulation_file)}")
    print("-" * 40)

    # 3. Process
    try:
        precons, postcons, flow_info_map = parse_mapping_file(mapping_file)
        flow_events, dvar_events = parse_simulation_file(simulation_file, flow_info_map)

        # Calculate total nodes (Varcount)
        all_nodes = set(precons.keys()) | set(postcons.keys())
        varcount = len(all_nodes) if all_nodes else 64 

        # 4. Construct Final JSON
        result = {
            "Flow": {
                "Vartype": "link",
                "Values": flow_events
            },
            "Dvars": {
                "Vartype": "data",
                "Varcount": varcount,
                "Starting postcons": postcons,
                "Starting chunks": precons,
                "Values": dvar_events
            }
        }

        # 5. Save
        with open(output_file, 'w') as f:
            json.dump(result, f, indent=4)
            
        print("-" * 40)
        print(f"SUCCESS: Merged data saved to '{output_file}'")

    except Exception as e:
        print(f"\n[!] An error occurred during processing: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()