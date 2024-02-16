(*
 * Copyright © 2023 Mark Raynsford <code@io7m.com> https://www.io7m.com
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Northpike.Plan.Parameters.
Require Import Northpike.Plan.State.
Require Import Northpike.Plan.Transition.

Module Type S
  (P     : Parameters.S)
  (Maps  : TotalMap.S)
  (State : State.S P Maps)
<: Transition.S P Maps State.

  Import State.

  Definition arguments : Set :=
    nat * P.agent.

  Definition timeRemaining (a : arguments) : nat :=
    fst a.

  Definition agentOf (a : arguments) : P.agent :=
    snd a.

  Lemma executingDec : forall s e a m,
    {EExecuting a m = statusOf s e}+{~EExecuting a m = statusOf s e}.
  Proof.
    move => s e a m.
    elim (statusOf s e).
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - move => a1 n.
      elim (PeanoNat.Nat.eq_dec m n).
      * move => Heq; subst.
        elim (P.agentEqDec a a1).
        ** move => Heq; subst. left; reflexivity.
        ** move => Hneq. right; congruence.
      * move => Hneq.
        elim (P.agentEqDec a a1).
        ** move => Heq; subst. right; congruence.
        ** move => Hneq2. right; congruence.
  Qed.

  Lemma agentExecutingDec : forall s e a,
    {ASExecuting e = agentStatusOf s a}+{~ASExecuting e = agentStatusOf s a}.
  Proof.
    move => s e a.
    elim (agentStatusOf s a).
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - move => e1.
      elim (P.elementEqDec e e1).
      * move => Heq; subst. left; reflexivity.
      * move => Hneq. right; congruence.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
  Qed.

  (** The "agent failed executing" precondition. A task can fail if
      if:
      - The element _e_ is a task.
      - The status of the element is _EExecuting a m_.
      - m <> 0
      - The status of the agent is _ASExecuting e_.
  *)
  Definition preconditions
    (s : state)
    (a : arguments)
    (e : P.element)
  : Prop :=
       P.elementIsTask e
    /\ (timeRemaining a) <> 0
    /\ EExecuting (agentOf a) (timeRemaining a) = statusOf s e
    /\ ASExecuting e = agentStatusOf s (agentOf a).

  (** The state transitions to a new state where the task has failed. *)
  Definition transition
    (s : state)
    (a : arguments)
    (e : P.element)
  : state :=
    let s1 := withStatus s e ESuccess in
      withAgentStatus s1 (agentOf a) (ASFailed e).

  Theorem preconditionsDecidableE : forall
    (s : state)
    (a : arguments)
    (e : P.element),
      {preconditions s a e}+{~preconditions s a e}.
  Proof.
    move => s [t a] e.
    unfold preconditions.
    simpl in *.

    elim (P.elementIs e).
    - move => Ht.
      elim (executingDec s e a t) => [HL|HR].
      * elim (agentExecutingDec s e a) => [Hacc|Hneq].
        ** elim (PeanoNat.Nat.eq_dec t 0) => [He0|Hn0].
           *** right; intuition.
           *** left; intuition.
        ** elim (PeanoNat.Nat.eq_dec t 0) => [He0|Hn0].
           *** right; intuition.
           *** right; intuition.
      * elim (agentExecutingDec s e a) => [Hacc|Hneq].
        ** elim (PeanoNat.Nat.eq_dec t 0) => [He0|Hn0].
           *** right; intuition.
           *** right; intuition.
        ** elim (PeanoNat.Nat.eq_dec t 0) => [He0|Hn0].
           *** right; intuition.
           *** right; intuition.
    - move => Hb.
      right.
      move => [H0 [H1 H2]].
      pose proof (P.elementIsNot0 e H0) as H3.
      contradiction.
  Qed.

  (** For a given element state _s_, it is decidable whether the
      precondition holds. *)
  Theorem preconditionsDecidable : forall
    (s : state)
    (a : arguments),
      {exists e, preconditions s a e}+{~exists e, preconditions s a e}.
  Proof.
    move => s a.
    apply (EFacts.elementDecidable _ (preconditionsDecidableE s a)).
  Qed.

  Lemma invariants0 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateBarrierNeverExecuting (transition s a e).
  Proof.
    move => s [t a] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [H1 [H2 H3]].

    unfold transition.
    unfold stateBarrierNeverExecuting in *.
    simpl in *.

    move => e1 a1 n Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      pose proof (P.elementIsNot0 e1 H1).
      contradiction.
    - rewrite <- statusOfIndependence.
      rewrite <- withStatusNotOf.
      apply Hi0; auto.
      symmetry; auto.
  Qed.

  Lemma invariants1 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateBarrierNeverWaitingForAgent (transition s a e).
  Proof.
    move => s [t a] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [H1 [H2 H3]].

    unfold transition.
    unfold stateBarrierNeverWaitingForAgent in *.
    simpl in *.

    move => e1 n Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      pose proof (P.elementIsNot0 e1 H1).
      contradiction.
    - rewrite <- statusOfIndependence.
      rewrite <- withStatusNotOf.
      apply Hi1; auto.
      symmetry; auto.
  Qed.

  Lemma invariants2 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementNoDependenciesNeverWaiting (transition s a e).
  Proof.
    move => s [t a] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [H1 [H2 H3]].

    unfold transition.
    unfold stateElementNoDependenciesNeverWaiting in *.
    simpl in *.

    move => e1 Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      rewrite <- statusOfIndependence.
      rewrite withStatusOf.
      discriminate.
    - rewrite <- statusOfIndependence.
      rewrite <- withStatusNotOf.
      apply (Hi2 _ Hb).
      symmetry; auto.
  Qed.

  Lemma invariants3 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementExecutingAgentStatus (transition s a e).
  Proof.
    move => s [t a0] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [H1 [H2 [H3 H4]]].

    unfold transition.
    unfold stateElementExecutingAgentStatus in *.
    simpl in *.

    move => e1 a1 m Hb.
    elim (P.agentEqDec a0 a1) => [HaL|HaR].
    - elim (P.elementEqDec e0 e1) => [HeL|HeR].
      * subst.
        rewrite <- statusOfIndependence in Hb.
        rewrite withStatusOf in Hb.
        contradict Hb; discriminate.
      * subst.
        rewrite <- statusOfIndependence in Hb.
        rewrite <- withStatusNotOf in Hb.
        elim (Hi3 _ _ _ Hb) => [HL|HR].
        ** contradict H4. rewrite <- HL; congruence.
        ** contradict H4; rewrite <- HR; congruence.
        ** symmetry; auto.
    - elim (P.elementEqDec e0 e1) => [HeL|HeR].
      * subst.
        rewrite <- statusOfIndependence in Hb.
        rewrite withStatusOf in Hb.
        contradict Hb; discriminate.
      * rewrite <- statusOfIndependence in Hb.
        rewrite <- withStatusNotOf in Hb.
        elim (Hi3 _ _ _ Hb) => [HL|HR].
        ** left.
           rewrite <- withAgentStatusNotOf.
           rewrite <- agentStatusOfIndependence.
           exact HL. symmetry; auto.
        ** right.
           rewrite <- withAgentStatusNotOf.
           rewrite <- agentStatusOfIndependence.
           exact HR. symmetry; auto.
        ** symmetry; auto.
  Qed.

  Lemma invariants4 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementTimeValid0 (transition s a e).
  Proof.
    move => s [n a] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 [Hp1 [Hp2 Hp3]]].

    unfold transition.
    unfold stateElementTimeValid0 in *.
    simpl in *.

    move => e1 m Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      rewrite <- statusOfIndependence in Hb.
      rewrite withStatusOf in Hb.
      contradict Hb; discriminate.
    - rewrite <- statusOfIndependence in Hb.
      rewrite <- withStatusNotOf in Hb.
      apply (Hi4 e1 m Hb).
      symmetry; auto.
  Qed.

  Lemma invariants5 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementTimeValid1 (transition s a e).
  Proof.
    move => s [n a] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 [Hp1 [Hp2 Hp3]]].

    unfold transition.
    unfold stateElementTimeValid1 in *.
    simpl in *.

    move => e1 a1 m Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      rewrite <- statusOfIndependence in Hb.
      rewrite withStatusOf in Hb.
      assert (m = Nat.pred n) as Hmn by congruence.
      pose proof (Hi5 e1 a n Hp2) as Hm0.
      subst.
      assert (Nat.pred n <= n) as Hnle
        by apply PeanoNat.Nat.le_pred_l.
      apply (PeanoNat.Nat.le_trans (Nat.pred n) n P.timeoutExecution Hnle Hm0).
    - rewrite <- statusOfIndependence in Hb.
      rewrite <- withStatusNotOf in Hb.
      apply (Hi5 e1 a1 m Hb).
      symmetry; auto.
  Qed.

  Theorem transitionInvariants : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateInvariants (transition s a e).
  Proof.
    move => s n e0 Hpre.
    constructor. apply invariants0; auto.
    constructor. apply invariants1; auto.
    constructor. apply invariants2; auto.
    constructor. apply invariants3; auto.
    constructor. apply invariants4; auto.
    apply invariants5; auto.
  Qed.

End S.

Module Make
  (P     : Parameters.S)
  (Maps  : TotalMap.S)
  (State : State.S P Maps)
<: S P Maps State.
  Include S P Maps State.
End Make.
