Require Import network_model.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Module TestNetworkModel.

    (* Test Initialization with 100 players *)
    Lemma init_global_state_players_count :
        length (players init_global_state) = MAX_PLAYERS.
    Proof.
        unfold init_global_state, MAX_PLAYERS.
        rewrite map_length, seq_length.
        reflexivity.
    Qed.

    (* Test Adding a Player *)
    Lemma add_player_increases_count :
        length (players (add_player init_global_state {| position := zero_vector; velocity := zero_vector; aggregate_group := None |})) = MAX_PLAYERS + 1.
    Proof.
        unfold add_player, init_global_state, MAX_PLAYERS.
        simpl.
        rewrite map_length, seq_length.
        simpl.
        lia.
    Qed.

    (* Test Deleting a Player *)
    Lemma delete_player_decreases_count :
        length (players (delete_player (add_player init_global_state {| position := zero_vector; velocity := zero_vector; aggregate_group := None |}) 0)) = MAX_PLAYERS.
    Proof.
        unfold add_player, delete_player, init_global_state, MAX_PLAYERS.
        simpl.
        rewrite map_length, seq_length.
        simpl.
        lia.
    Qed.

    (* Test Upvoting a Player's Velocity *)
    Lemma add_vote_updates_velocity :
        let st := init_global_state in
        let st' := add_vote st 0 in
        velocity (snd (List.nth 0 st'.players (0, {| position := zero_vector; velocity := zero_vector; aggregate_group := None |}))) = {| x := 1; y := 0; z := 0 |}.
    Proof.
        unfold init_global_state, add_vote, PlayerState, zero_vector.
        simpl.
        destruct (0 =? 0) eqn:H.
        - rewrite Nat.eqb_eq in H. subst.
            simpl. reflexivity.
        - discriminate.
    Qed.

End TestNetworkModel.