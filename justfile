run:
    java -XX:+UseParallelGC -Dtlc.timeout=360 -jar ./thirdparty/tla2tools.jar -config QueueLoad/QueueLoad-1ops.cfg QueueLoad/QueueLoad.tla || true
    java -XX:+UseParallelGC -Dtlc.timeout=360 -jar ./thirdparty/tla2tools.jar -config QueueLoad/QueueLoad-10ops.cfg QueueLoad/QueueLoad.tla || true
    java -XX:+UseParallelGC -Dtlc.timeout=360 -jar ./thirdparty/tla2tools.jar -config QueueLoad/QueueLoad-50ops.cfg QueueLoad/QueueLoad.tla || true
    #java -XX:+UseParallelGC -Dtlc.timeout=360 -jar ./thirdparty/tla2tools.jar -config message_scaling_test/WorstCase10Soldiers.cfg message_scaling_test/WorstCase10.tla
    # java -XX:+UseParallelGC -Dtlc.timeout=60 -jar ./thirdparty/tla2tools.jar -config raft/Raft.cfg raft/Raft.tla
    # java -XX:+UseParallelGC -jar ./thirdparty/tla2tools.jar -config parallel_commits/ParallelCommits.cfg parallel_commits/ParallelCommits.tla
    # java -XX:+UseParallelGC -jar ./thirdparty/tla2tools.jar -config bounded_counter/BoundedCounter.cfg bounded_counter/BoundedCounter.tla
    # java -XX:+UseParallelGC -jar ./thirdparty/tla2tools.jar -config hybrid_logic_clock/HybridLogicClock.cfg hybrid_logic_clock/HybridLogicClock.tla
