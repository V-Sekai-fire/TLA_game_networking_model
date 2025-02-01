import starvote
from starvote import hashed_ballots_tiebreaker
import json

tasks = [
    {
        # "Linearizability"
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 100,
        "Leader-Based Event Synchronization": 100,
        "Multi-Primary Replication with Conflict Resolution": 30,
        "Sharded Scene Tree with Centralized Coordination": 80,
        "Full State Replication with Quorum": 20,
    },
    {
        # "Fault Tolerance"
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 100,
        "Leader-Based Event Synchronization": 80,
        "Multi-Primary Replication with Conflict Resolution": 90,
        "Sharded Scene Tree with Centralized Coordination": 90,
        "Full State Replication with Quorum": 70,
        
    },
    {
        # "Space Complexity"
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 30,
        "Leader-Based Event Synchronization": 70,
        "Multi-Primary Replication with Conflict Resolution": 50,
        "Sharded Scene Tree with Centralized Coordination": 60,
        "Full State Replication with Quorum": 90,
    },
    {
        # "Time Complexity"
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 40,
        "Leader-Based Event Synchronization": 70,
        "Multi-Primary Replication with Conflict Resolution": 60,
        "Sharded Scene Tree with Centralized Coordination": 50,
        "Full State Replication with Quorum": 80,
    },
    {
       #  "Complexity"
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 30,
        "Leader-Based Event Synchronization": 60,
        "Multi-Primary Replication with Conflict Resolution": 50,
        "Sharded Scene Tree with Centralized Coordination": 50,
        "Full State Replication with Quorum": 80,
    },
    {
        # "Scalability"
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 90,
        "Leader-Based Event Synchronization": 70,
        "Multi-Primary Replication with Conflict Resolution": 80,
        "Sharded Scene Tree with Centralized Coordination": 80,
        "Full State Replication with Quorum": 50,
    },
    {
       # "Communication Load": {
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 30,
        "Leader-Based Event Synchronization": 60,
        "Multi-Primary Replication with Conflict Resolution": 40,
        "Sharded Scene Tree with Centralized Coordination": 50,
        "Full State Replication with Quorum": 20,
    },
    {
        # "Communication Complexity"
        "Distributed Consensus Algorithm (e.g., Raft or Paxos)": 30,
        "Leader-Based Event Synchronization": 60,
        "Multi-Primary Replication with Conflict Resolution": 40,
        "Sharded Scene Tree with Centralized Coordination": 50,
        "Full State Replication with Quorum": 80,
    },
]

seats = 1

results = starvote.election(
    method=starvote.star if seats < 2 else starvote.allocated,
    ballots=tasks,
    seats=seats,
    tiebreaker=hashed_ballots_tiebreaker,
    maximum_score=100,
)

print(json.dumps(results, indent=4))
