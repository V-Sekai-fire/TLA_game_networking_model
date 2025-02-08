run:
    java -XX:+UseParallelGC -Dtlc.timeout=60 -jar ../tla2tools.jar -config raft/Raft.cfg raft/Raft.tla
    # java -XX:+UseParallelGC -jar ../tla2tools.jar -config parallel_commits/ParallelCommits.cfg parallel_commits/ParallelCommits.tla
    # java -XX:+UseParallelGC -jar ../tla2tools.jar -config bounded_counter/BoundedCounter.cfg bounded_counter/BoundedCounter.tla
    # java -XX:+UseParallelGC -jar ../tla2tools.jar -config hybrid_logic_clock/HybridLogicClock.cfg hybrid_logic_clock/HybridLogicClock.tla
