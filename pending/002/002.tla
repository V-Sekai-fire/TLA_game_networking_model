---- MODULE Simulation ----
EXTENDS Naturals

VARIABLES
    playerStates,    \* Map from sessionId to player state
    currentTime

(* --algorithm PlayerSimulation
    variables playerStates = [sessionId \in Sessions |-> InitialState],
              currentTime = 0;

    process Simulation {
        while (TRUE) {
            currentTime := currentTime + dt;
            forEach sessionId \in Sessions {
                LET state = playerStates[sessionId]
                IN playerStates[sessionId] := 
                    [state EXCEPT 
                        !.position = state.position + state.velocity * dt
                    ]
            }
            await tick;
        }
    }
end algorithm -- *)