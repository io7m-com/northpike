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
    P.agent.

  Lemma agentFailedDec : forall s e a,
    {ASFailed e = agentStatusOf s a}+{~ASFailed e = agentStatusOf s a}.
  Proof.
    move => s e a.
    elim (agentStatusOf s a).
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - move => e1.
      elim (P.elementEqDec e e1).
      * move => Heq; subst. left; reflexivity.
      * move => Hneq. right; congruence.
    - right; move => H; inversion H.
  Qed.

  (** The "agent went idle" precondition. This state transition can
      occur if:
      - The element _e_ is a task.
      - The status of the agent is _ASFailed e_.

      This state transition encodes the notion of an agent failing a task
      and then going back to being idle.
  *)
  Definition preconditions
    (s : state)
    (a : arguments)
    (e : P.element)
  : Prop :=
       P.elementIsTask e
    /\ ASFailed e = agentStatusOf s a.

  (** The state transitions to a new state where the agent is idle. *)
  Definition transition
    (s : state)
    (a : arguments)
    (e : P.element)
  : state :=
    withAgentStatus s a ASIdle.

  Theorem preconditionsDecidableE : forall
    (s : state)
    (a : arguments)
    (e : P.element),
      {preconditions s a e}+{~preconditions s a e}.
  Proof.
    move => s a e.
    unfold preconditions.
    simpl in *.

    elim (P.elementIs e).
    - move => Ht.
      elim (agentFailedDec s e a) => [Hacc|Hneq].
      * left; intuition.
      * right; intuition.
    - move => Hb.
      right.
      move => [H0 H1].
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
    move => s a e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [H1 H2].

    unfold transition.
    unfold stateBarrierNeverExecuting in *.
    simpl in *.

    move => e1 a1 n Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      pose proof (P.elementIsNot0 e1 H1).
      contradiction.
    - rewrite <- statusOfIndependence.
      apply Hi0; auto.
  Qed.

  Lemma invariants1 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateBarrierNeverWaitingForAgent (transition s a e).
  Proof.
    move => s a e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [H1 H2].

    unfold transition.
    unfold stateBarrierNeverWaitingForAgent in *.
    simpl in *.

    move => e1 n Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      pose proof (P.elementIsNot0 e1 H1).
      contradiction.
    - rewrite <- statusOfIndependence.
      apply Hi1; auto.
  Qed.

  Lemma invariants2 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementNoDependenciesNeverWaiting (transition s a e).
  Proof.
    move => s a e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [H1 H2].

    unfold transition.
    unfold stateElementNoDependenciesNeverWaiting in *.
    simpl in *.

    move => e1 Hb.
    rewrite <- statusOfIndependence.
    apply (Hi2 _ Hb).
  Qed.

  Lemma invariants3 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementExecutingAgentStatus (transition s a e).
  Proof.
    move => s a0 e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 Hp1].

    unfold transition.
    unfold stateElementExecutingAgentStatus in *.
    simpl in *.

    move => e1 a1 m Hb.
    elim (P.agentEqDec a0 a1) => [HaL|HaR].
    - subst.
      rewrite <- statusOfIndependence in Hb.
      elim (Hi3 e1 a1 m Hb) => [HL|HR].
      * rewrite <- Hp1 in HL.
        contradict HL; discriminate.
      * rewrite <- Hp1 in HR.
        contradict HR; discriminate.
    - rewrite <- statusOfIndependence in Hb.
      elim (Hi3 e1 a1 m Hb) => [HL|HR].
      * left.
        rewrite <- withAgentStatusNotOf.
        intuition. auto.
      * right.
        rewrite <- withAgentStatusNotOf.
        intuition. auto.
  Qed.

  Lemma invariants4 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementTimeValid0 (transition s a e).
  Proof.
    move => s a e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 Hp1].

    unfold transition.
    unfold stateElementTimeValid0 in *.
    simpl in *.

    move => e1 m Hb.
    rewrite <- statusOfIndependence in Hb.
    apply (Hi4 e1 m Hb).
  Qed.

  Lemma invariants5 : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateElementTimeValid1 (transition s a e).
  Proof.
    move => s a0 e0.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => [Hp0 Hp1].

    unfold transition.
    unfold stateElementTimeValid1 in *.
    simpl in *.

    move => e1 a1 m Hb.
    rewrite <- statusOfIndependence in Hb.
    apply (Hi5 e1 a1 m Hb).
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
