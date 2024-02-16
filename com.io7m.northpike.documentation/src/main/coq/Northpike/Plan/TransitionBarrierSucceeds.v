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
    unit.

  Lemma readyDec : forall s e,
    {EReady = statusOf s e}+{~EReady  = statusOf s e}.
  Proof.
    move => s e.
    elim (statusOf s e).
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - left; constructor.
    - right; move => H; inversion H.
  Qed.

  (** The "barrier succeeds" precondition. This state transition can
      occur if:
      - The element _e_ is a barrier.
      - The status of the element is _EReady_.

      Barriers immediately succeed when their dependencies become ready.
  *)
  Definition preconditions
    (s : state)
    (a : arguments)
    (e : P.element)
  : Prop :=
       P.elementIsBarrier e
    /\ EReady = statusOf s e.

  (** The state transitions to a new state where the barrier has succeeded. *)
  Definition transition
    (s : state)
    (a : arguments)
    (e : P.element)
  : state :=
    withStatus s e ESuccess.

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
    - move => Hb.
      right.
      move => [H0 H1].
      pose proof (P.elementIsNot1 e H0) as H3.
      contradiction.
    - move => Ht.
      elim (readyDec s e) => [Hacc|Hneq].
      * left; intuition.
      * right; intuition.
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
    - subst; rewrite withStatusOf; discriminate.
    - rewrite <- withStatusNotOf.
      apply (Hi0 _ a1 n Hb).
      symmetry; auto.
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
    - subst; rewrite withStatusOf; discriminate.
    - rewrite <- withStatusNotOf.
      apply (Hi1 _ n Hb).
      symmetry; auto.
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
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst; rewrite withStatusOf; discriminate.
    - rewrite <- withStatusNotOf.
      apply (Hi2 _ Hb).
      symmetry; auto.
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

    move => e1 a1 n Hb.
    elim (P.elementEqDec e0 e1) => [HL|HR].
    - subst.
      rewrite withStatusOf in Hb.
      contradict Hb; discriminate.
    - rewrite <- withStatusNotOf in Hb.
      rewrite <- agentStatusOfIndependence.
      apply (Hi3 e1 a1 n Hb).
      symmetry; auto.
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
    elim (P.elementEqDec e0 e1) => [HeE|HeN].
    - subst.
      rewrite withStatusOf in Hb.
      contradict Hb; discriminate.
    - rewrite <- withStatusNotOf in Hb.
      apply (Hi4 e1 m Hb).
      auto.
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

    move => e1 a m Hb.
    elim (P.elementEqDec e0 e1) => [HeE|HeN].
    - subst.
      rewrite withStatusOf in Hb.
      contradict Hb; discriminate.
    - rewrite <- withStatusNotOf in Hb.
      apply (Hi5 e1 a m Hb).
      auto.
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
