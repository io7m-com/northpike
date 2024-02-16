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

  Definition arguments :=
    unit.

  Lemma waitingDependenciesDec : forall s e,
    {EWaitingForDependencies = statusOf s e}+{~EWaitingForDependencies = statusOf s e}.
  Proof.
    move => s e.
    elim (statusOf s e).
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - left; constructor.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
  Qed.

  (** The "waiting for dependencies" precondition. An element can be waiting for
      its dependencies if:
      - The status of the element is _EWaitingForDependencies_.
      - The element has at least one dependency that is in progress.
  *)
  Definition preconditions
    (s : state)
    (a : arguments)
    (e : P.element)
  : Prop :=
       EWaitingForDependencies = statusOf s e
    /\ List.Exists (fun f => statusInProgress (statusOf s f)) (P.elementDependencies e).

  (** For a given element _e_ and state _s_, the precondition is decidable. *)
  Theorem preconditionsDecidableE : forall
    (s : state)
    (a : arguments)
    (e : P.element),
      {preconditions s a e}+{~preconditions s a e}.
  Proof.
    move => s a e.
    unfold preconditions.

    have Hle : ({List.Exists (fun f : P.element => statusInProgress (statusOf s f)) (P.elementDependencies e)}
             + {~List.Exists (fun f : P.element => statusInProgress (statusOf s f)) (P.elementDependencies e)}). {
      eapply List.Exists_dec.
      move => x.
      elim (statusOf s x).
      - right; move => H; inversion H.
      - right; move => H; inversion H.
      - right; move => H; inversion H.
      - left; constructor.
      - left; constructor.
      - left; constructor.
      - left; constructor.
    }

    - elim Hle => [HleL|HleR].
      * elim (waitingDependenciesDec s e) => [HwdL|HwdR].
        ** left; auto.
        ** right; intro Hfalse; intuition.
      * elim (waitingDependenciesDec s e) => [HwdL|HwdR].
        ** right; intro Hfalse; intuition.
        ** right; intro Hfalse; intuition.
  Qed.

  (** For a given element state _s_, it is decidable whether there is an 
      element for which the precondition holds. *)
  Theorem preconditionsDecidable : forall
    (s : state)
    (a : arguments),
      {exists e, preconditions s a e}+{~exists e, preconditions s a e}.
  Proof.
    move => s a.
    apply (EFacts.elementDecidable _ (preconditionsDecidableE s a)).
  Qed.

  (** The state transitions to the same state. *)
  Definition transition
    (s : state)
    (a : arguments)
    (e : P.element)
  : state :=
    s.

  Theorem transitionInvariants : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateInvariants (transition s a e).
  Proof.
    intros s e Hinv Hpre.
    unfold preconditions.
    trivial.
  Qed.

End S.

Module Make
  (P     : Parameters.S)
  (Maps  : TotalMap.S)
  (State : State.S P Maps)
<: S P Maps State.
  Include S P Maps State.
End Make.
