# the word fetsh stands for "fetch from ssh"
# it is NOT a typo
# example usage:
# ./fetsh.sh thambra CAL bcasts bcast_classic_r0 
user=$1
calpath=$2 # relative to user's ~
dirname=$3 # one dir inside files/
logname=$4
mkdir -p files/${dirname}
scp ${user}@192.168.20.10:/mnt/central/users/${user}/${calpath}/visualizer_log.txt files/${dirname}/
scp ${user}@192.168.20.10:/mnt/central/users/${user}/${calpath}/ns3_log.txt files/${dirname}/
python3 translate_to_format.py files/${dirname}/ns3_log.txt files/${dirname}/visualizer_log.txt files/${dirname}/${logname}_log
echo "Fetched visualization and ns3 logs from SSH and translated to JSON format."
echo "Output file: files/${dirname}/${logname}_log.json"