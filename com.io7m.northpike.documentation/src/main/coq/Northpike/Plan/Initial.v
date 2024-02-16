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

Module Type S
  (P     : Parameters.S)
  (Maps  : TotalMap.S)
  (State : State.S P Maps).

  Import State.

  (** ** Initial State *)

  Fixpoint initialStateAgentsF
    (m  : AMaps.t agentStatus)
    (xs : list P.agent)
  : AMaps.t agentStatus :=
    match xs with
    | nil         => m
    | cons a rest => initialStateAgentsF (AMaps.put m a ASIdle) rest
    end.

  Definition initialStateAgents : AMaps.t agentStatus :=
    initialStateAgentsF (AMaps.init (fun x => ASIdle)) P.agents.

  Definition initialStateElement
    (e : P.element)
  : status :=
    match P.elementDependencies e with
    | nil => EReady
    | _   => EWaitingForDependencies
    end.

  Lemma initialStateElementChoice : forall e,
    EReady = initialStateElement e \/ EWaitingForDependencies = initialStateElement e.
  Proof.
    intros e.
    unfold initialStateElement.
    destruct (P.elementDependencies e); intuition.
  Qed.

  Fixpoint initialStateElementsF
    (m  : EMaps.t status)
    (xs : list P.element)
  : EMaps.t status :=
    match xs with
    | nil         => m
    | cons e rest => initialStateElementsF (EMaps.put m e (initialStateElement e)) rest
    end.

  Lemma initialStateElementsFNotIn : forall es e (m : EMaps.t status),
       ~List.In e es
    -> EMaps.get (initialStateElementsF m es) e = EMaps.get m e.
  Proof.
    move => es.
    elim : es.
    - move => e m Hnin.
      reflexivity.
    - move => e0 es Hind e1 m Hnin.
      simpl.
      rewrite List.not_in_cons in Hnin.
      destruct Hnin as [H0 H1].
      rewrite (Hind _ (EMaps.put m e0 (initialStateElement e0)) H1).
      rewrite <- EMaps.putRemains.
      * reflexivity.
      * auto.
  Qed.

  Lemma listNotEq : forall {A : Type} (xs : list A) (x y : A),
       List.In x xs
    -> ~List.In y xs
    -> x <> y.
  Proof.
    move => A xs.
    elim : xs.
    - move => x y Hin.
      inversion Hin.
    - move => x0 xs Hind x1 y Hin Hnin.
      rewrite List.not_in_cons in Hnin.
      destruct Hnin as [Hnin0 Hnin1].
      destruct Hin as [Hin0|Hin1].
      * subst.
        auto.
      * apply Hind.
        exact Hin1.
        exact Hnin1.
  Qed.

  Lemma initialStateElementsFInNoDup : forall es e (m : EMaps.t status),
       List.In e es
    -> List.NoDup es
    -> EMaps.get (initialStateElementsF m es) e = EMaps.get (EMaps.put m e (initialStateElement e)) e.
  Proof.
    move => es.
    elim : es.
    - move => e m Hnin Hnd.
      inversion Hnin.
    - move => e0 es Hind e1 m Hin Hnd.
      rewrite List.NoDup_cons_iff in Hnd.
      destruct Hnd as [Hnd0 Hnd1].
      destruct Hin as [Hin0|Hin1].
      * subst.
        rewrite (initialStateElementsFNotIn (EMaps.put m e1 (initialStateElement e1)) Hnd0).
        reflexivity.
      * pose proof (listNotEq Hin1 Hnd0) as Hneq.
        simpl.
        rewrite (Hind e1 (EMaps.put m e0 (initialStateElement e0)) Hin1 Hnd1).
        rewrite <- EMaps.putGet.
        apply (EMaps.putGet m e1 (initialStateElement e1)).
  Qed.

  Definition initialStateElements : EMaps.t status :=
    initialStateElementsF (EMaps.init initialStateElement) P.elements.

  Definition initialState : state :=
    State initialStateElements initialStateAgents.

  Lemma initialStateBarrierNeverExecuting : stateBarrierNeverExecuting initialState.
  Proof.
    unfold stateBarrierNeverExecuting.
    unfold initialState.
    unfold initialStateElements.
    unfold statusOf.

    pose proof P.elementsAreFinite as Hf.
    pose proof P.elementsUnique as Hu.

    induction P.elements as [|e0 es].
    - intro e.
      pose proof (Hf e) as Hfalse.
      inversion Hfalse.
    - intros e a n Hb.
      rewrite (initialStateElementsFInNoDup (EMaps.init initialStateElement) _ Hu).
      apply Hf.
      rewrite <- EMaps.putGet.
      elim : (initialStateElementChoice e);
        move => Heq;
        rewrite <- Heq; discriminate.
  Qed.

  Lemma initialStateBarrierNeverWaitingForAgent : stateBarrierNeverWaitingForAgent initialState.
  Proof.
    unfold stateBarrierNeverWaitingForAgent.
    unfold initialState.
    unfold initialStateElements.
    unfold statusOf.

    pose proof P.elementsAreFinite as Hf.
    pose proof P.elementsUnique as Hu.

    induction P.elements as [|e0 es].
    - intro e.
      pose proof (Hf e) as Hfalse.
      inversion Hfalse.
    - intros e n Hb.
      rewrite (initialStateElementsFInNoDup (EMaps.init initialStateElement) _ Hu).
      apply Hf.
      rewrite <- EMaps.putGet.
      elim : (initialStateElementChoice e);
        move => Heq;
        rewrite <- Heq; discriminate.
  Qed.

  Lemma initialStateElementNoDependenciesNeverWaiting : stateElementNoDependenciesNeverWaiting initialState.
  Proof.
    unfold stateElementNoDependenciesNeverWaiting.
    unfold initialState.
    unfold initialStateElements.
    unfold statusOf.

    pose proof P.elementsAreFinite as Hf.
    pose proof P.elementsUnique as Hu.

    induction P.elements as [|e0 es].
    - intro e.
      pose proof (Hf e) as Hfalse.
      inversion Hfalse.
    - intros e Hb.
      rewrite (initialStateElementsFInNoDup (EMaps.init initialStateElement) _ Hu).
      apply Hf.
      rewrite <- EMaps.putGet.
      unfold initialStateElement.
      destruct (P.elementDependencies e).
      * discriminate.
      * contradict Hb; discriminate.
  Qed.

  Lemma initialStateElementExecutingAgentStatus : stateElementExecutingAgentStatus initialState.
  Proof.
    unfold stateElementExecutingAgentStatus.
    unfold initialState.
    unfold initialStateElements.
    unfold statusOf.

    pose proof P.elementsAreFinite as Hf.
    pose proof P.elementsUnique as Hu.

    induction P.elements as [|e0 es].
    - intro e.
      pose proof (Hf e) as Hfalse.
      inversion Hfalse.
    - intros e a n Hb.
      rewrite (initialStateElementsFInNoDup (EMaps.init initialStateElement) _ Hu) in Hb.
      apply Hf.
     rewrite <- EMaps.putGet in Hb.
     unfold initialStateElement in Hb.
     destruct (P.elementDependencies e).
     * contradict Hb; discriminate.
     * contradict Hb; discriminate.
  Qed.

  Lemma initialStateElementTimeValid0 : stateElementTimeValid0 initialState.
  Proof.
    unfold stateElementTimeValid0.
    unfold initialState.
    unfold initialStateElements.
    unfold statusOf.

    pose proof P.elementsAreFinite as Hf.
    pose proof P.elementsUnique as Hu.

    induction P.elements as [|e0 es].
    - intro e.
      pose proof (Hf e) as Hfalse.
      inversion Hfalse.
    - intros e n Hb.
      rewrite (initialStateElementsFInNoDup (EMaps.init initialStateElement) _ Hu) in Hb.
      apply Hf.
     rewrite <- EMaps.putGet in Hb.
     unfold initialStateElement in Hb.
     destruct (P.elementDependencies e).
     * contradict Hb; discriminate.
     * contradict Hb; discriminate.
  Qed.

  Lemma initialStateElementTimeValid1 : stateElementTimeValid1 initialState.
  Proof.
    unfold stateElementTimeValid1.
    unfold initialState.
    unfold initialStateElements.
    unfold statusOf.

    pose proof P.elementsAreFinite as Hf.
    pose proof P.elementsUnique as Hu.

    induction P.elements as [|e0 es].
    - intro e.
      pose proof (Hf e) as Hfalse.
      inversion Hfalse.
    - intros e a n Hb.
      rewrite (initialStateElementsFInNoDup (EMaps.init initialStateElement) _ Hu) in Hb.
      apply Hf.
     rewrite <- EMaps.putGet in Hb.
     unfold initialStateElement in Hb.
     destruct (P.elementDependencies e).
     * contradict Hb; discriminate.
     * contradict Hb; discriminate.
  Qed.

  Theorem initialStateInvariants : stateInvariants initialState.
  Proof.
    pose proof initialStateBarrierNeverExecuting.
    pose proof initialStateBarrierNeverWaitingForAgent.
    pose proof initialStateElementNoDependenciesNeverWaiting.
    pose proof initialStateElementExecutingAgentStatus.
    pose proof initialStateElementTimeValid0.
    pose proof initialStateElementTimeValid1.
    constructor; auto.
  Qed. 

End S.

Module Make
  (P     : Parameters.S)
  (Maps  : TotalMap.S)
  (State : State.S P Maps)
<: S P Maps State.
  Include S P Maps State.
End Make.
