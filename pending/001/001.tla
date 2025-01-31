--------------------------- MODULE Server ---------------------------
EXTENDS Naturals, Sequences

CONSTANT N \* Number of players
CONSTANT InputRate \* Frequency of input in Hz
CONSTANT PacketSize \* Number of inputs per packet
CONSTANT BufferSize \* Capacity of the perf buffer
CONSTANT LostProbability

VARIABLE perfBuffer \* Holds processed inputs per CPU
VARIABLE playerState \* Tracks each player's state
VARIABLE queuedPackets \* Queued inputs waiting to be processed

(* Simple representation of a packet *)
\* Each packet has PacketSize inputs, possibly including some redundant data
PACKET == [inputs: 1..PacketSize]

(* Utility function to simulate potential packet drop *)
lost(packet) ==
    IF RandomElement({TRUE, FALSE}) THEN packet ELSE Null

(* PlusCal algorithm. *)
(************************************************************************)
\* --algorithm FPS
procedure ProcessPackets() {
  while TRUE do
    if queuedPackets = << >> then
      skip;
    else
      \* Dequeue next packet
      packet := Head(queuedPackets);
      queuedPackets := Tail(queuedPackets);

      \* Check for loss
      incoming := lost(packet);

      if incoming # Null then
        \* Put new inputs in perf buffer
        if Len(perfBuffer) < BufferSize then
          perfBuffer := Append(perfBuffer, incoming);
        end if;
      end if;
    end if;
  end while;
}

process (Client \in 1..N)
variable i = 1;
{
  while TRUE do
    \* Build a packet of PacketSize inputs
    newPacket := [inputs |-> 1..PacketSize];

    \* Redundancy is not modeled in detail here, just appended
    queuedPackets := Append(queuedPackets, newPacket);

    i := i + 1;
    \* Wait some time to model InputRate
    skip;
  end while;
}

process (Server = "Server")
{
  ProcessPackets();
}
(************************************************************************)

\* Fairness conditions
Fairness == TRUE

\* Initial definitions
Init ==
  /\ perfBuffer = << >>
  /\ playerState = [p \in 1..N |-> 0]
  /\ queuedPackets = << >>

Next == /\ FPS.next
        /\ UNCHANGED << playerState >>

Spec == Init /\ [][Next]_<< perfBuffer, playerState, queuedPackets >>

=============================================================================