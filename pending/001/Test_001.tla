--------------------------- MODULE Test_001 ---------------------------
EXTENDS Server, TLC

(* Test 001: Tests for Server Module Failure Modes *)

(* Test 1: POST REQUEST fails *)
Test1_PostRequestFails ==
    /\ POST_REQUEST_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ POST_REQUEST_FAIL]_<< perfBuffer, playerState, queuedPackets >>

(* Test 2: DELIVER REQUEST fails *)
Test2_DeliverRequestFails ==
    /\ DELIVER_REQUEST_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ DELIVER_REQUEST_FAIL]_<< perfBuffer, playerState, queuedPackets >>

(* Test 3: VALIDATE REQUEST fails *)
Test3_ValidateRequestFails ==
    /\ VALIDATE_REQUEST_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ VALIDATE_REQUEST_FAIL]_<< perfBuffer, playerState, queuedPackets >>

(* Test 4: UPDATE SERVER STATE fails *)
Test4_UpdateServerStateFails ==
    /\ UPDATE_SERVER_STATE_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ UPDATE_SERVER_STATE_FAIL]_<< perfBuffer, playerState, queuedPackets >>

(* Test 5: POST REPLY fails *)
Test5_PostReplyFails ==
    /\ POST_REPLY_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ POST_REPLY_FAIL]_<< perfBuffer, playerState, queuedPackets >>

(* Test 6: DELIVER REPLY fails *)
Test6_DeliverReplyFails ==
    /\ DELIVER_REPLY_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ DELIVER_REPLY_FAIL]_<< perfBuffer, playerState, queuedPackets >>

(* Test 7: VALIDATE REPLY fails *)
Test7_ValidateReplyFails ==
    /\ VALIDATE_REPLY_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ VALIDATE_REPLY_FAIL]_<< perfBuffer, playerState, queuedPackets >>

(* Test 8: UPDATE CLIENT STATE fails *)
Test8_UpdateClientStateFails ==
    /\ UPDATE_CLIENT_STATE_FAIL == TRUE
    /\ Spec' = Init /\ [][Next /\ UPDATE_CLIENT_STATE_FAIL]_<< perfBuffer, playerState, queuedPackets >>

=============================================================================