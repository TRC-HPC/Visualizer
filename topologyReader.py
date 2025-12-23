from linksInfo import LinksInfo
from linksInfo import LinkData
from copy import deepcopy

# MM: Move this to real file generation
MAX_BANDWIDTH=4000.0

"""
    Take a topology file discribing the actual topology we want to represent 
    and get required data from it - linkInfo, mapping to ns3, and printing an ns3 file
    The format of the input is as following:
    first line: name
    second line: elementCount switchCount linkCount
    every other line represents a link:
    src rank, src port, dst rank, dst port, bandwidth, latency
"""
# MM: Do we need dest port?
# MM: Check ports are correct
# MM: Note that switches always go after ranks.

class TopologyReader():    
    def __init__(self): 
        # define as False until we initallize 
        self.isTopoRead = False
        self.isNs3Mapped = False

    # Given real topology file reads it and saves the data in a numerical way (instead a string)
    def read_real_topology(self, file_path): 
        with open(file=file_path, mode="rt") as file:
            # read lines
            lines = file.readlines() 
        
            # get name
            self.topoName = lines[0]

            # get elementCount switchCount and linkCount
            parsedLine = lines[1].split(" ")
            if len(parsedLine) != 3:
                print("Usage: elementCount switchCount linkCount")
                exit(-1)
            
            # Read the number of elements (i.e. nodes + switches), switches, and links
            self.elementCount, self.switchCount, self.linkCount = map(int, parsedLine)
            self.rankCount = self.elementCount - self.switchCount

            # get all links, and turn them into numbers
            lines = lines[2:]
            self.links = list()
            for i in range(self.linkCount):
                parsedLine = lines[i].split(" ")
                if len(parsedLine) != 6:
                    print("Each link line must contain exectly 6 values:\n\
                            src, srcPort, dst, dstPort, bandwidth, latency")
                    print(f"line {i} only contains {len(parsedLine)}!")
                    exit(-1)
                # convert link to tuple 
                self.links.append(LinkData(*(int(parsedLine[j]) if j <=3 else float(parsedLine[j]) for j in range(len(parsedLine)))))

        # redefine as ready
        self.isTopoRead = True

    # after a topology file is read, goes through the links and creates linkInfo
    def createLinkInfo(self):
        # if didn't read topology file yet
        if not self.isTopoRead:
            return None

        # Else create linkInfo and return it
        linkList = list()
        for (src, srcPort, dst, dstPort, bandwidth, latency) in self.links: 
            # create links in a symmetric manner
            linkList.append(LinkData(src, srcPort, dst, dstPort, latency, bandwidth))
            linkList.append(LinkData(dst, dstPort, src, srcPort, latency, bandwidth))
        
        # return linkInfo
        return LinksInfo(self.rankCount, self.switchCount, linkList)

    # after a topology file is read creates mapping to ns3 topology. can be used to print ns3 topology file
    def createNs3Mapping(self):        
        # if didn't read topology file yet
        if not self.isTopoRead:
            return None

        # number of ports for each element
        self.portCount = [0 for _ in range(self.elementCount)]

        # calculate portCount
        for (src, srcPort, dst, dstPort, _, __) in self.links:
            for node, nodePort in [(src,srcPort), (dst,dstPort)]:
                # get the maximum port number - we expect that for each element ports will be 0,1...
                self.portCount[node] = max(self.portCount[node], nodePort + 1)         

        # create mapping between node, port to ns3 element and count number of such elements
        self.ns3ElementCount = self.elementCount

        # define representatives for elements - fake switches\themselves
        self.elementReps = [node for node in range(self.elementCount)]

        # represent nodes with fake switches 
        for node in range(self.rankCount):
            self.elementReps[node] = self.ns3ElementCount
            self.ns3ElementCount += 1

        # redefine as true
        self.isNs3Mapped = True

        # return mapping
        return deepcopy((self.elementReps, self.ns3ElementCount, self.rankCount))  

    # prints ns3 file
    def printNs3File(self, file_path, multiPortMode=1):
        # if didn't create mapping yet
        if not self.isNs3Mapped:
            if self.createNs3Mapping() == None:
                return None

        ns3Links = set()
        # for every link create suitnig link and link to reps if needed
        for (src, _, dst, _, bandwidth, latency) in self.links:
            # get the ns3 ranks
            ns3SrcRep = self.elementReps[src]
            ns3DstRep = self.elementReps[dst]
            # create actual link between reps
            ns3Links.add((ns3SrcRep, ns3DstRep, bandwidth, latency))
            # create links to reps if needed
            for element in [src,dst]:
                # meaning we have a fake switch represanting us
                if self.elementReps[element] != element:
                    ns3Links.add((element, self.elementReps[element], MAX_BANDWIDTH, 0))  
       
        # sort to get links orderd nicely
        ns3Links = list(ns3Links)
        ns3Links.sort()

        with open(file=file_path, mode="wt") as file:
            # print name
            file.write(f"{self.topoName}")
            # print metadata
            file.write(f"{self.ns3ElementCount} {self.ns3ElementCount-self.rankCount} {len(ns3Links)} {multiPortMode}\n")
            # print switches
            for switch in range(self.rankCount, self.ns3ElementCount): file.write(f"{switch} ") 
            file.write("\n")
            # print links
            for link in ns3Links:
                # MM: Check PDR
                file.write(f"{link[0]} {link[1]} {link[2]}Gbps {link[3]}us PDR 0.0\n")
