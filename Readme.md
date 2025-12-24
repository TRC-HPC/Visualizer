# CAL Visualizer Module
This is the git repository of the CAL Visualizer Module.


### Usage of fetsh.sh
##### Author: Tomer Hambra
fetsh is really hard coded for Toga Cluster CAL use.
General Usage:
```
./fetsh.sh <cluster_username> <CAL path> <directory_in_files> <log file name> 

# Example
./fetsh.sh thambra CAL bcasts bcast_classic_r0 
```
Assumption:
run command uses "visualizer_log.txt" for vis log output, and "ns3_log.txt" for ns3 log.
info about generating the logs in CAL is provided inside the CALTest.cpp, in a `std::cerr << "Usage: "` block

### Contributors

- Yarin Saraga (everything except readme + fetsh)
- Tomer Hambra (everything except what yarin is doing)