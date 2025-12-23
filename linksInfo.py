from collections import defaultdict, Counter
from collections import namedtuple
import copy
import random
import time
#import timeit


LinkData = namedtuple('LinkData', ('src', 'srcPort', 'dst', 'dstPort', 'latency', 'bandwidth'))

class LinkVertex():
    def __init__(self, linkIndex, childLinkVertexList):
        # The link index
        self.linkIndex = linkIndex

        # The rememing paths from this link index
        self.childLinkVertexList = childLinkVertexList
    
    # Number of paths exiting our current position
    def getChildCount(self):
        return len(self.childLinkVertexList)
    
    # Add Child
    def addChild(self, childLinkVertex):
        self.childLinkVertexList.append(childLinkVertex)
    
    # Get link index
    def getLinkIndex(self):
        return self.linkIndex
    
    # Get child
    def getChild(self, childIndex):
        return self.childLinkVertexList[childIndex]
 
    def getNextRandomChild(self):
        if self.childLinkVertexList:
            return self.childLinkVertexList[time.time_ns() % len(self.childLinkVertexList)]
        else:
            return None
        
    def getRandomPathR(self, currPath):
        # Choose child
        nextChild = self.getNextRandomChild()
        
        # Child is None
        if nextChild is None:
            return currPath
        
        # Append childs' linkIndex
        currPath.append(nextChild.getLinkIndex())
        
        # Call child in recursion
        return nextChild.getRandomPath(currPath)
    
    def getRandomPath(self, currPath):
        nextChild = self.getNextRandomChild()
        while nextChild is not None:
            currPath.append(nextChild.getLinkIndex())
            nextChild = nextChild.getNextRandomChild()

        return currPath
    
    def getFirstPath(self, currPath):
        # we reached dst
        if not self.childLinkVertexList:
            return
        
        # get first child
        nextChild = self.childLinkVertexList[0]

        # append childs' linkIndex
        currPath.append(nextChild.getLinkIndex())

        # call child in recursion
        return nextChild.getFirstPath(currPath)
    
    # MM: This should be deleted
    # get all the link indexes that are the last links
    def getAllDstLinks(self):
        # we reached the dst. return link number
        if not self.childLinkVertexList:
            return {self.linkIndex}
        
        # get all the dst links recursively
        links = set()
        for child in self.childLinkVertexList:
            links.update(child.getAllDstLinks())
        
        return links      
    
class LinksInfo():
    def __init__(self, rankCount, switchCount, linkList):
        # Compute data about the real topology
        self.setData(rankCount, switchCount, linkList)               
            
    # Note: Assumes the ranks indices are first, and the switch are second and consecutive
    #       Otherwise, we will need to create mapping from links src/dst to actual index
    def setData(self, rankCount, switchCount, linkList):
        # Number of ranks (end-points)
        self.rankCount = rankCount
        
        # Number of switches
        self.switchCount = switchCount
        
        # Link List
        self.linkList = copy.deepcopy(linkList)
        
        # ElementCount
        self.elementCount = self.rankCount + self.switchCount
        self.elementOutLinks = [set() for _ in range(self.elementCount)]
        self.elementInLinks = [set() for _ in range(self.elementCount)]
        self.portCount = [0 for _ in range(self.elementCount)]

        # MM: Can get portCount from topologyReader
        # Update outgoing / incoming links and element ports
        for index, link in enumerate(self.linkList):
            self.elementOutLinks[link.src].add(index)
            self.elementInLinks[link.dst].add(index)
            self.portCount[link.src] = max(self.portCount[link.src], link.srcPort + 1)
            self.portCount[link.dst] = max(self.portCount[link.dst], link.dstPort + 1)

        # MM: Can unite with previous loop if we have portCount
        self.portOutLinks = [[set() for _ in range(self.portCount[element])] for element in range(self.elementCount)]
        
        for index, link in enumerate(self.linkList):
            self.portOutLinks[link.src][link.srcPort].add(index)

        # Initialize maximum distance between each tuple of src srcPort ant dst
        # Distance to ourself is 0        
        self.elementDistancePort = [[[self.elementCount + 1 for _ in range(self.elementCount)] for port in range(self.portCount[element])] \
                                for element in range(self.elementCount)]        
        for element in range(self.elementCount):
            for port in range(self.portCount[element]):
                self.elementDistancePort[element][port][element] = 0
            
        # Link Vertexs - contains all the shortest paths to each destination       
        self.pathToDstPort = [[[[] for _ in range(self.elementCount)] for port in range(self.portCount[element])] for element in range(self.elementCount)]
        self.pathToDst = [[[] for _ in range(self.elementCount)] for _ in range(self.elementCount)]

        # All elements at distance d from us (starting with d = 0)
        foundElements = True
        distance = 0
        prevDistElementsList = [{elementIndex} for elementIndex in range(self.elementCount)]        
        while foundElements:
            # Look for elements at distance d + 1
            distance += 1
            
            # Empty the elements at distance 'd' from us
            nextDistElementsList = [set() for elementIndex in range(self.elementCount)]
            
            # Assume didn't find elements at distance d
            foundElements = False
                    
            # Check each element
            for element in range(self.elementCount):         
                for port in range(self.portCount[element]):
                    # --------#
                    # Step 1: # 
                    # --------#
                    # Check the new elements we are able to reach within 'distance' hops, and how many routes we have to this element

                    # MM: Remove extra calculations of add factor, dstElementCount, etc.
                    # Specify for each new element, how many routes we have found to reach                
                    dstElementCount = dict()
                    
                    # Check all our direct neighbor elements
                    for linkIndex in self.portOutLinks[element][port]:
                        # Get neighbor
                        neighborElement = self.linkList[linkIndex].dst
                        
                        assert neighborElement != element
                        
                        # Check for each of its previous elements (at distance 'd - 1' from neighbor), if we are getting to them, and how many times
                        for dstElement in prevDistElementsList[neighborElement]:
                            if self.elementDistancePort[element][port][dstElement] > distance:
                                if dstElement in dstElementCount:
                                    dstElementCount[dstElement] = dstElementCount[dstElement] + 1
                                else:
                                    dstElementCount[dstElement] = 1
                    
                    # --------#
                    # Step 2: #
                    # --------#
                    # Append the links from our neighbors to new desination, while considering the split of payload we perform                
                    # The bandwidth on each outgoing link to our neighbor will be divided by the number of routes we have to destination
                    for linkIndex in self.portOutLinks[element][port]:
                        # Get neighbor
                        neighborElement = self.linkList[linkIndex].dst
                                                
                        # Check for each of its previous elements (at distance 'd - 1' from neighbor), if we are getting to them, and how many times
                        for dstElement in prevDistElementsList[neighborElement]:
                            if self.elementDistancePort[element][port][dstElement] > distance:                            
                                # Add to paths to destination
                                self.pathToDstPort[element][port][dstElement].append(LinkVertex(linkIndex, self.pathToDst[neighborElement][dstElement]))    
                    
                    
                    # Update the distance to those elements
                    for dstElement in dstElementCount.keys(): 
                        self.elementDistancePort[element][port][dstElement] = min(distance, self.elementDistancePort[element][port][dstElement])
                        nextDistElementsList[element].add(dstElement)
                    if len(nextDistElementsList[element]) > 0:
                        foundElements = True
                        
            # MM: Only take the lowest distances, shouldn't take longer paths.
            # redefine pathToDst
            for src in range(self.elementCount):
                for dst in range(self.elementCount):
                    self.pathToDst[src][dst] = []
                    for port in range(self.portCount[src]):
                        self.pathToDst[src][dst].extend(self.pathToDstPort[src][port][dst])

            # Swap Lists
            prevDistElementsList = nextDistElementsList

        # MM: This is not needed and no one knows what it does (This is used in visulizer, should switch there also)
        # Get Dst Ports
        self.dstPorts = [[[set() for port in range(self.portCount[src])] for dst in range(self.elementCount)] for src in range(self.elementCount)] 
        for src in range(self.elementCount):
            for dst in range(self.elementCount):
                for port in range(self.portCount[src]):
                    self.dstPorts[src][dst][port] = list(LinkVertex(-1, self.pathToDstPort[src][port][dst]).getAllDstLinks())
                    self.dstPorts[src][dst][port].sort()
                    # convert to dstPort numbers
                    for i in range(len(self.dstPorts[src][dst][port])):
                        self.dstPorts[src][dst][port][i] = self.linkList[self.dstPorts[src][dst][port][i]].dstPort

        # Get element distance - min distance between two nodes with no regard to ports
        self.elementDistance = [[self.elementDistancePort[src][0][dst] for dst in range(self.elementCount)] for src in range(self.elementCount)]
        for src in range(self.elementCount):
            for port in range(self.portCount[src]):
                for dst in range(self.elementCount):
                    self.elementDistance[src][dst] = min(self.elementDistance[src][dst], self.elementDistancePort[src][port][dst])

        # Get maximum distance
        self.maxDistance = max(item for sublist in self.elementDistance[:self.getRankCount()] for item in sublist) 

    def getRankCount(self):
        return self.rankCount
    
    def getSwitchCount(self):
        return self.switchCount
    
    def getElementCount(self):
        return self.elementCount
    
    def getOutgoingLinks(self, elementIndex):
        return self.elementOutLinks[elementIndex]
    
    def getIncomingLinks(self, elementIndex):
        return self.elementInLinks[elementIndex]

    def getDistance(self, src, dst, port = None):
        if port != None:
            return self.elementDistancePort[src][port][dst]
        else:
            return self.elementDistance[src][dst] 

    def getMaxDistance(self):
        return self.maxDistance
    
    def isEndpoint(self, rank):
        return rank < self.rankCount
    
    def getDstPorts(self, srcRank, dstRank, srcPort):
        return self.dstPorts[srcRank][dstRank][srcPort]
    
    def getElementDistanceArray(self):
        return self.elementDistance
    
    def getPathsToDst(self, src, dst, port = None):
        if port == None:
            return LinkVertex(-1, self.pathToDst[src][dst])
        else:
            return LinkVertex(-1, self.pathToDstPort[src][port][dst])

    def getLink(self, linkIndex):
        return self.linkList[linkIndex]
    
    def getPortCount(self,rank):
        return self.portCount[rank]
    
    def getLinkCount(self):
        return len(self.linkList)
    
    def getTimeToSend(self, src, dst, chunkSize, port = None):
        # Get links path from source to destination
        linkPathList = []
        self.getPathsToDst(src, dst, port).getRandomPath(linkPathList)
        
        # No path
        if not linkPathList:
            return 0
        
        # Summarize latency, and get minimum bandwidth
        timeSum = 0
        minBand = float('inf')
        # Traverse all links on the way
        for index, linkIndex in enumerate(linkPathList):
            currLink = self.getLink(linkIndex)
            
            # Accumulate the time
            minBand = min(minBand,currLink.bandwidth)
            timeSum += currLink.latency            
        
        timeSum += chunkSize / minBand
        # Return timing
        # AZ: TODO: Consider what is the beta / bandwidth you store, and prevent yourself from translating from one to the other over and over
        return timeSum

    def getDefaultPorts(self, srcRank, dstRank, srcPort=None):
        # get options to srcPort (if given choose itself, otherwise everyport)
        if srcPort == None:        
            # go through options and take shortest option (hop distance)
            bestDist = self.getDistance(srcRank, dstRank)
            for srcPortOption in range(self.portCount[srcRank]):
                # TODO: Maybe improve efficiency 
                if self.getDistance(srcRank, dstRank, srcPortOption) == bestDist:
                    srcPort = srcPortOption
                    break
                     
        # if there isn't any viable option
        if srcPort == None:
            print(f'When sending from {srcRank} to {dstRank} no viable ports!')
            exit(-1)

        # get dstPort
        dstPort = self.getDstPorts(srcRank, dstRank, srcPort)[0]

        return srcPort, dstPort
    
    def getLinks(self, srcRank, dstRank, srcPort):
        path = []
        LinkVertex(-1, self.pathToDstPort[srcRank][srcPort][dstRank]).getFirstPath(path)
        return path

# MM: Complete all queries
class CliqueLinksInfo():
    def __init__(self, rankCount, alpha, bandwidth):
        self.rankCount = rankCount
        self.alpha = float(alpha)
        self.bandwidth = float(bandwidth)
        
    def getLinkIndex(self, srcRank, dstRank):
        return srcRank * self.rankCount + dstRank
    
    def getRankCount(self):
        return self.rankCount
    
    def getSwitchCount(self):
        return 0
    
    def getElementCount(self):
        return self.rankCount    
    
    def getOutgoingLinks(self, elementIndex):
        outgoingLinks =  [self.getLinkIndex(elementIndex, i) for i in range(self.rankCount)]        
        outgoingLinks.remove(self.getLinkIndex(elementIndex, elementIndex))
        return outgoingLinks
    
    def getIncomingLinks(self, elementIndex):
        incomingLinks =  [self.getLinkIndex(i, elementIndex) for i in range(self.rankCount)]        
        incomingLinks.remove(self.getLinkIndex(elementIndex, elementIndex))
        return incomingLinks

    def getMaxDistance(self):
        return 1

    def getPortCount(self,rank):
        return 1

    def getDistance(self, src, dst, port = None):
        return 1
    
    def getPathsToDst(self, src, dst, port = None):
        return LinkVertex(-1, [LinkVertex(self.getLinkIndex(src, dst), [])])
    
    def getLink(self, linkIndex):        
        dstRank = linkIndex % self.rankCount
        srcRank = (linkIndex - dstRank) / self.rankCount
        return LinkData(srcRank, 0,dstRank,0, self.alpha, self.bandwidth)
    
    def getLinkCount(self):
        return self.rankCount * self.rankCount
    
    def getLinksToDst(self, src, dst):
        return {self.getLinkIndex(src, dst) : 1}
    
    def getTimeToSend(self, src, dst, chunkSize):
        return self.alpha +  chunkSize / self.bandwidth

# MM: Add unit tests to link info
if __name__ == "__main__":
    l = LinksInfo(256,4,"data/topologies/A2.real")

    