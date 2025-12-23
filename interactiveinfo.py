import pickle as pkl
import sys
import os
import pandas as pd
from collections import defaultdict

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from topologyReader import TopologyReader
from linksInfo import LinksInfo

'''
A tool that answers queries about a simulation.

TODO: add ns3 information to get actual paths and times.
TODO: check added support for chunk splits.
TODO: add execl support - get results in excel. 
TODO: add actual visualization
'''

class Visualizer:
    def __init__(self, logFile, topologyFile):
        # Load log file 
        with open(logFile, "rb") as file:
            data = pkl.load(file)
        
        self.log, self.chunkSizes, self.subChunks, self.chunkParent, self.preCond, self.postCond, self.time = data

        # Get linkInfo 
        topoReader = TopologyReader()
        topoReader.read_real_topology(topologyFile)
        self.linkInfo = topoReader.createLinkInfo()
        
        # create rank sends - mapping between srcRank, dstRank, chunkId to start time and end time 
        self.rankSends = dict()
        self.rankSendsByTime = dict()
        self.chunkCount = len(self.chunkSizes)
        
        active = 0
        maxActive = 0
        s = 0
        d = 0

        for actionFlag, flowInfoList, time in self.log:
            for action in flowInfoList:
                
                srcPort = None
                if len(action) == 4:
                    srcRank, dstRank, srcPort, chunkId = action
                else:
                    srcRank, dstRank, chunkId = action
                
                if type(chunkId) == int:
                    chunkId = tuple([chunkId])
                
                # No Action
                if chunkId is None:
                    continue 
                
                if not isinstance(chunkId, tuple):
                    chunkId = tuple([chunkId])
                
                srcPort, _ = self.linkInfo.getDefaultPorts(srcRank, dstRank, srcPort)
                # we start sending
                if actionFlag:
                    active += 1
                    self.rankSends[(srcRank, dstRank, srcPort, chunkId)] = [time]
                    if (srcRank // 8) != dstRank // 8:
                        s += 1
                        d += sum([self.chunkSizes[chunk] for chunk in chunkId])
                else:
                    active -= 1
                    self.rankSends[(srcRank, dstRank, srcPort, chunkId)].append(time)
                    self.rankSends[(srcRank, dstRank, srcPort, chunkId)] = tuple(self.rankSends[(srcRank, dstRank, srcPort, chunkId)])
                    data = (srcRank, dstRank, srcPort, chunkId)
                    times = self.rankSends[(srcRank, dstRank, srcPort, chunkId)]
                    if not times in self.rankSendsByTime.keys():
                        self.rankSendsByTime[times] = [data]
                    else:
                        self.rankSendsByTime[times].append(data)
                maxActive = max(maxActive,active)
            
        print(f'maximum concurrent flows {maxActive}')

        # create mapping from src->dst to linkIndex
        self.linkMapping = {(self.linkInfo.linkList[linkIndex].src, self.linkInfo.linkList[linkIndex].dst): linkIndex for linkIndex in range(len(self.linkInfo.linkList))}

        # create link prespective - when is every link busy
        self.sendEvents = [list() for _ in range(len(self.linkInfo.linkList))]
        # self.globalSends 
        # create chunk prespective - where is the chunk at all times
        self.chunkLifeCycle = [dict() for _ in range(self.chunkCount)]  
                
        # create node prespective - when did he recive chunks
        self.nodeLifeCycle = [dict() for _ in range(self.linkInfo.rankCount)]
        # create post-condition end times - should maybe normalize according to distance or something to really compare
        self.postCondFinishTimes = [{cid: self.time for cid in self.postCond[pc]} for pc in range(len(self.postCond))]

        # Initallize chunk, node life cycle and postcond finish times according to pre condition 
        for rank, preCond in enumerate(self.preCond):
            for chunk in preCond:
                self.chunkLifeCycle[chunk][rank] = [(0, "pre condition")]
                self.nodeLifeCycle[rank][chunk] = [(0, "pre condition")]
                if chunk in self.postCondFinishTimes[rank]:
                    self.postCondFinishTimes[rank][chunk] = 0

        # Update data structures accoding to sends we got from the simulation
        for times, events in self.rankSendsByTime.items():
            for event in events:
                srcRank, dstRank, srcPort, chunks = event
                begTime, endTime = times
                if not isinstance(chunks,tuple):
                    chunks = tuple([chunks])
                for chunkId in chunks:
                    # links
                    linkIndexes = self.linkInfo.getLinks(srcRank, dstRank, srcPort)
                    for linkIndex in linkIndexes:
                        self.sendEvents[linkIndex].append((begTime, chunkId, "start"))
                        self.sendEvents[linkIndex].append((endTime, chunkId, "end"))

                    # Chunk has first arrived 
                    if chunkId not in self.nodeLifeCycle[dstRank].keys():
                        self.nodeLifeCycle[dstRank][chunkId] = [(endTime, f"rank {srcRank}")]
                        self.chunkLifeCycle[chunkId][dstRank] = [(endTime, f"rank {srcRank}")]
                        # Check if any parent chunk is now 'complete' and update data structure accordingly
                        self.mergeChunks(dstRank, chunkId, endTime)
                    else: # This is a bad thing we want to avoid
                        self.nodeLifeCycle[dstRank][chunkId].append((endTime, f"rank {srcRank}"))
                        self.chunkLifeCycle[chunkId][dstRank].append((endTime, f"rank {srcRank}"))
                    
                    # Can be caused because a parent had arrived - nothing to do, just check
                    if chunkId not in self.nodeLifeCycle[srcRank].keys():
                        check =  False
                        parents = []
                        self.getParents(chunkId, parents)
                        for parent in parents:
                            if parent in self.nodeLifeCycle[srcRank].keys():
                                check = True
                                break
                        if not check:
                            print("chunk sent but never got here")
                            exit(-1)
                    # else: Nothing to do here as chunk was already registered here

                    # update post cond finish times if needed
                    if chunkId in self.postCondFinishTimes[dstRank]:
                        self.postCondFinishTimes[dstRank][chunkId] = min(self.postCondFinishTimes[dstRank][chunkId], endTime)

    # show congestion in links according to startSend, endSend EM: TODO: maybe choose maximal because threshold works badly
    def getCongestion(self, congestionThreshold):
        print("------------------------------------------")
        print("Showing congestion:")
        print("------------------------------------------")
        linksWithCongestion = dict()
        for linkIndex in range(self.linkInfo.getLinkCount()):
            # define curr load and load threshold s.t. if currLoad > loadThreshold we have congestion
            currLoad = 0
            # TODO: fix defenition - multiply by G=2^30. also whole model is not realy accurate
            loadThreshold = self.linkInfo.linkList[linkIndex].bandwidth / congestionThreshold * 1e9
            congestionEvent = []
            congestionTimes = []
            for time, chunkId, eventType in self.sendEvents[linkIndex]:
                # Update curr load
                if eventType == "start":
                    currLoad += self.chunkSizes[chunkId]
                else: # "end"
                    currLoad -= self.chunkSizes[chunkId]

                # if we were already in a congestion event
                if congestionEvent:
                    congestionTimes.append(time)
                    if tuple(congestionTimes) in linksWithCongestion.keys():
                        linksWithCongestion[tuple(congestionTimes)].append(tuple(congestionEvent))
                    else:
                        linksWithCongestion[tuple(congestionTimes)] = [tuple(congestionEvent)]
                    congestionEvent.clear()
                    congestionTimes.clear()
                 
                # we are in a congestion event
                if currLoad > loadThreshold:
                    congestionEvent.append(self.linkInfo.linkList[linkIndex].src)
                    congestionEvent.append(self.linkInfo.linkList[linkIndex].dst)
                    congestionEvent.append(self.linkInfo.linkList[linkIndex].bandwidth)
                    congestionEvent.append(currLoad)
                    congestionTimes.append(time)

            # print all congestion events
            for times, values in linksWithCongestion.items():
                begTime, endTime = times
                print(f"From time {begTime} to {endTime} had congestion on the following links:")
                for i, value in enumerate(values):
                    src, dst, bandwidth, load = value
                    print(f"Congestion event {i}: On link {src}->{dst} - load = {load}bps, bandwidth = {bandwidth}Gbps")

    # show link life cycle
    def getLinkLifeCycle(self, src, dst):
        # check if link is present
        if (src, dst) not in self.linkMapping:
            print(f"no link {src}->{dst}!")
            return
        
        # Get linkIndex
        linkIndex = self.linkMapping[(src, dst)]
        print("------------------------------------------")
        print("Showing links'", src, "->", dst, "life cycle:")
        print("------------------------------------------")
        l = list(self.sendEvents[linkIndex])
        l.sort()
        currLoad = 0
        for time, chunkId, type in l:
            currLoad += self.chunkSizes[chunkId] * (-1 if type == "end" else 1)
            print(f"chunk {chunkId}'s send over {src}->{dst} {type}ed at time {time}. curr load = {currLoad}bps/{self.linkInfo.linkList[linkIndex].bandwidth}Gbps")
        
        print("Done!")

    def linksLifeCycleToExcel(self,  src, dst): # Currently doesn't work for some reason TODO: fix
        # check if link is present
        if (src, dst) not in self.linkMapping:
            print(f"no link {src}->{dst}!")
            return
        
        # Get linkIndex
        linkIndex = self.linkMapping[(src, dst)]

        l = list(self.sendEvents[linkIndex])
        l.sort()
        timeToLoad = {"times": [], "load": []}
        currLoad = 0
        for time, chunkId, type in l:
            timeToLoad["times"].append(time)
            currLoad += self.chunkSizes[chunkId] * (1 if type == "start" else -1)
            timeToLoad["load"].append(currLoad)

        writer = pd.ExcelWriter("linkResult.xlsx", engine='xlsxwriter')
        pd.DataFrame(timeToLoad).to_excel(writer)
        print("Done!")

    # show chunks life cycle 
    def getChunkLifeCycle(self, chunkId):
        print("------------------------------------------")
        print("Showing chunks'", chunkId, "life cycle:")
        print("------------------------------------------")
        for rank, arriveList in self.chunkLifeCycle[chunkId].items():
            time, msg = arriveList[0]
            print(f"chunk {chunkId} arrived to rank {rank} at {time} from {msg}")
            for i in range(1, len(arriveList)):
                time, msg = arriveList[i]
                print(f"BAD: chunk {chunkId} has been sent again to {rank} at {time} from {msg}")
        print("Done!")

    # show nodes life cycle 
    def getNodeLifCycle(self, rank):
        print("------------------------------------------")
        print("Showing node", rank, "life cycle:")
        print("------------------------------------------")
        for chunkId, arriveList in self.nodeLifeCycle[rank].items():
            time, msg = arriveList[0]
            print(f"chunk {chunkId} arrived to {rank} at {time} from {msg}")
            for i in range(1, len(arriveList)):
                time, msg = arriveList[i]
                print(f"BAD: chunk {chunkId} has been sent again to {rank} at {time} from {msg}")
        print("Done!")
    

    def getAllNodesLifeCycle(self):
        print("Showing all nodes life cycle!")
        for rank in range(self.linkInfo.rankCount):
            self.getNodeLifCycle(rank)

    def getAllChunksLifeCycle(self):
        print("Showing all chunks life cycle!")
        for chunkId in range(self.chunkCount):
            self.getChunkLifeCycle(chunkId)

    # Show post condition finish times
    def getPostCondFinishTimes(self, numOfChunksToPrint):
        print("------------------------------------------")
        print("Showing post condition finish times:")
        print("------------------------------------------")

        times = set()
        reverseMapping = defaultdict(list)

        for rank in range(len(self.postCondFinishTimes)):
            for chunk, time in self.postCondFinishTimes[rank].items():
                reverseMapping[time].append((chunk, rank))
                times.add(time)

        list().sort()
        times = list(times)
        times.sort()

        currTime = -1
        currIdx = 0
        while numOfChunksToPrint > 0 and -1 * currTime <= len(times):
            time = times[currTime]
            chunk, rank = reverseMapping[time][currIdx]  
            print(f"Post-condition {chunk}->{rank} completed at {time}.")
            currIdx += 1
            if len(reverseMapping[time]) <= currIdx:
                currIdx = 0
                currTime -= 1

            numOfChunksToPrint -= 1

    # Define assistance functions
    def getParents(self, chunkId, parents):
        if self.chunkParent[chunkId] == None:
            return
        
        parents.append(self.chunkParent[chunkId])

        return self.getParents(self.chunkParent[chunkId], parents)

    def mergeChunks(self, rank, chunkId, time): 
        # In case we 'complete' the parent chunk, add parent chunk to node\chunk life cycles and update postconditions
        parent = self.chunkParent[chunkId]
        if parent is None:
            return 
        # See in which subChunkList of the parent we are
        parentArrived = True
        for subChunkList in self.subChunks[parent]:
            # Not our group
            if not chunkId in subChunkList:
                continue
            
            # check all chunks arrived            
            for subChunk in subChunkList:
                if not subChunk in self.nodeLifeCycle[rank].keys():
                    parentArrived = False
                    break
            break
        # Parent arrived
        if parentArrived:
            if parent not in self.nodeLifeCycle[rank].keys():
                self.nodeLifeCycle[rank][parent] = [(time, "merged chunk")]
                self.chunkLifeCycle[parent][rank] = [(time, "merged chunk")]
            else:
                self.nodeLifeCycle[rank][parent].append((time, "merged chunk"))
                self.chunkLifeCycle[parent][rank].append((time, "merged chunk"))
            
            # update postcons if parent is a postcon
            if parent in self.postCondFinishTimes[rank]:
                self.postCondFinishTimes[rank][parent] = min(self.postCondFinishTimes[rank][parent], time)

            self.mergeChunks(rank, parent, time)
        
        # No 'top' chunk was completed
        return


def main():
    argv = sys.argv

    if len(argv) != 3:
        print("Expecting 2 aruments: logFilePath topologyFilePath! got " + str(len(argv)-1) + " insted.")
        exit(-1)

    # Get file pathes
    logFilePath = argv[1]
    topologyFilePath = argv[2]

    # Initiallize visualizer
    visualizer = Visualizer(logFilePath, topologyFilePath)

    # Answer queries
    while True:
        print("Menu:")
        print("0. Show congestion\n\tDescription Prints all congestion events on link that have load above loadThreshold\n\tParameters: loadThreshold")
        print("1. Get node life cycle\n\tDescription: Prints all the chunks that arrived to node x.\n\tParameters: rank")
        print("2. Get chunk life cycle\n\tDescription: Prints all the nodes that chunk x arrived to.\n\tParameters: chunkId")
        print("3. Get link life cycle\n\tDescription: Prints all the chunks that were sent on link x.\n\tParameters: src, dst")
        print("4. Get all nodes life cycle\n\tDescription: Prints all nodes life cycle\n\tParameters: None")
        print("5. Get all chunks life cycle\n\tDescription: Prints all chunks life cycle\n\tParameters: None")
        print("6. Get link life cycle excel")
        print("7. Get post condition finish times")
        print("To exit - enter")

        userRequest = input().split()

        # Exit if requested
        if not userRequest or userRequest[0] == "exit":
            print("Exiting!")
            break
        
        # Check that we got a number
        try:
            requestNum = int(userRequest[0])
        except ValueError:
            print("Pleasr enter a number!")
            continue

        # Define function and number of paramaters each function expacts
        functions = [visualizer.getCongestion, visualizer.getNodeLifCycle, visualizer.getChunkLifeCycle, visualizer.getLinkLifeCycle, \
                      visualizer.getAllNodesLifeCycle, visualizer.getAllChunksLifeCycle, visualizer.linksLifeCycleToExcel, visualizer.getPostCondFinishTimes]
        parameterCount = [1, 1, 1, 2, 0 ,0, 2, 1]
        # TODO: Add 2d array of types

        # Check we got a number in range
        if requestNum >= len(functions) or requestNum < 0:
            print("Please enter a number in the menu!")
            continue

        

        # Check that the right amount of parameters were given
        if parameterCount[requestNum] != len(userRequest) - 1:
            print(f"please pass {parameterCount[requestNum]} parameters!")
            continue

        # Convert parameters to a tuple 
        try:
            pars = (int(par) for par in userRequest[1:])
        except:
            print("All given parameters are excpected to be ints!")
            continue

        # Call function
        functions[requestNum](*pars)


if __name__ == "__main__":
    main()