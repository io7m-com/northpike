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

  Lemma waitingForAgentDec : forall s e m,
    {EWaitingForAgent m = statusOf s e}+{~EWaitingForAgent m = statusOf s e}.
  Proof.
    move => s e m.
    elim (statusOf s e).
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - move => n.
      elim (PeanoNat.Nat.eq_dec m n).
      * move => ?; subst; left; reflexivity.
      * move => ?; right; congruence.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
  Qed.

  Lemma agentIdleDec : forall s a,
    {ASIdle = agentStatusOf s a}+{~ASIdle = agentStatusOf s a}.
  Proof.
    move => s a.
    elim (agentStatusOf s a).
    - left; reflexivity.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
  Qed.

  (** The "agent accepted a task" precondition. An agent can have accepted a task
      if:
      - The element is a task.
      - The status of the element is _EWaitingForAgent m_.
      - The status of the agent is _ASIdle_.
  *)
  Definition preconditions
    (s : state)
    (a : arguments)
    (e : P.element)
  : Prop :=
       P.elementIsTask e
    /\ EWaitingForAgent (timeRemaining a) = statusOf s e
    /\ ASIdle = agentStatusOf s (agentOf a).

  (** The state transitions to a new state where the element has been accepted by the agent. *)
  Definition transition
    (s : state)
    (a : arguments)
    (e : P.element)
  : state :=
    let s1 := withStatus s e (EExecuting (agentOf a) P.timeoutExecution) in
      withAgentStatus s1 (agentOf a) (ASAccepted e).

  Theorem preconditionsDecidableE : forall
    (s : state)
    (a : arguments)
    (e : P.element),
      {preconditions s a e}+{~preconditions s a e}.
  Proof.
    move => s [t a] e.
    unfold preconditions.

    elim (P.elementIs e).
    - move => Ht.
      elim (waitingForAgentDec s e t) => [HeL|HeR].
      * elim (agentIdleDec s a) => [HaL|HaR].
        ** left; intuition.
        ** right; intuition.
      * elim (agentIdleDec s a) => [HaL|HaR].
        ** right; intuition.
        ** right; intuition.
    - move => Hb.
      right.
      move => [H0 H1].
      pose proof (P.elementIsNot0 e H0) as H2.
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
    move => s [t a0] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 Hp1].

    unfold transition.
    unfold stateBarrierNeverExecuting in *.
    move => e1 a1 m Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      pose proof (P.elementIsNot0 e1 Hp0).
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
    move => s [t a0] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 Hp1].

    unfold transition.
    unfold stateBarrierNeverWaitingForAgent in *.
    move => e1 n Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      pose proof (P.elementIsNot0 e1 Hp0).
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
    move => s [t a0] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 Hp1].

    unfold transition.
    unfold stateElementNoDependenciesNeverWaiting in *.
    move => e1 Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      rewrite <- statusOfIndependence.
      rewrite withStatusOf.
      discriminate.
    - rewrite <- statusOfIndependence.
      rewrite <- withStatusNotOf.
      apply Hi2; auto.
      symmetry; auto.
  Qed.

  Lemma invariants3 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementExecutingAgentStatus (transition s a e).
  Proof.
    move => s [t a0] e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 [Hp1 Hp2]].

    unfold transition.
    unfold stateElementExecutingAgentStatus in *.
    move => e1 a m Hb.
    elim (P.agentEqDec a a0) => [HaL|HaR].
    - elim (P.elementEqDec e0 e1) => [HeL|HeR].
      * subst.
        left.
        rewrite withAgentStatusOf.
        reflexivity.
      * subst a0.
        left.
        rewrite <- statusOfIndependence in Hb.
        rewrite <- withStatusNotOf in Hb.
        simpl in *.
        elim (Hi3 _ _ _ Hb) => [HL|HR].
        ** contradict Hp2; rewrite <- HL; discriminate.
        ** contradict Hp2; rewrite <- HR; discriminate.
        ** symmetry; auto.
    - elim (P.elementEqDec e0 e1) => [HeL|HeR].
      * subst.
        simpl in *.
        rewrite <- statusOfIndependence in Hb.
        rewrite withStatusOf in Hb.
        rewrite <- withAgentStatusNotOf.
        rewrite <- agentStatusOfIndependence.
        have Haeq : (a = a0) by congruence.
        subst.
        contradict HaR; intuition.
        auto.
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
    move => [Hp0 [Hp1 Hp2]].

    unfold transition.
    unfold stateElementTimeValid0 in *.
    move => e1 m Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      simpl in *.
      rewrite <- statusOfIndependence in Hb.
      rewrite withStatusOf in Hb.
      contradict Hb.
      discriminate.
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
    move => [Hp0 [Hp1 Hp2]].

    unfold transition.
    unfold stateElementTimeValid1 in *.
    move => e1 a1 m Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      simpl in *.
      rewrite <- statusOfIndependence in Hb.
      rewrite withStatusOf in Hb.
      assert (m = P.timeoutExecution) as Hk by congruence.
      subst.
      auto.
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
