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
Require Import Northpike.Plan.Completion.
Require Import Northpike.Plan.TransitionWaitingDependencies.
Require Import Northpike.Plan.TransitionDependencyFailed.
Require Import Northpike.Plan.TransitionDependencyReady.
Require Import Northpike.Plan.TransitionAgentStart.
Require Import Northpike.Plan.TransitionAgentContinue.
Require Import Northpike.Plan.TransitionAgentTimedOut.
Require Import Northpike.Plan.TransitionAgentTaskAccepted.
Require Import Northpike.Plan.TransitionAgentTaskStarted.
Require Import Northpike.Plan.TransitionAgentTaskContinue.
Require Import Northpike.Plan.TransitionAgentTaskTimedOut.
Require Import Northpike.Plan.TransitionAgentTaskSucceeded.
Require Import Northpike.Plan.TransitionAgentTaskFailed.
Require Import Northpike.Plan.TransitionAgentTaskFinishedButTimedOut.
Require Import Northpike.Plan.TransitionAgentTaskSucceededIdle.
Require Import Northpike.Plan.TransitionAgentTaskFailedIdle.
Require Import Northpike.Plan.TransitionBarrierSucceeds.

Module Type S
  (P       : Plan.Parameters.S)
  (M       : TotalMap.S)
  (ST      : State.S P M)
  (C       : Completion.S P M ST)
  (TWD     : TransitionWaitingDependencies.S P M ST)
  (TDF     : TransitionDependencyFailed.S P M ST)
  (TDR     : TransitionDependencyReady.S P M ST)
  (TAS     : TransitionAgentStart.S P M ST)
  (TAC     : TransitionAgentContinue.S P M ST)
  (TATO    : TransitionAgentTimedOut.S P M ST)
  (TATA    : TransitionAgentTaskAccepted.S P M ST)
  (TATS    : TransitionAgentTaskStarted.S P M ST)
  (TATC    : TransitionAgentTaskContinue.S P M ST)
  (TATTO   : TransitionAgentTaskTimedOut.S P M ST)
  (TATSu   : TransitionAgentTaskSucceeded.S P M ST)
  (TATF    : TransitionAgentTaskFailed.S P M ST)
  (TATFBTO : TransitionAgentTaskFinishedButTimedOut.S P M ST)
  (TATSI   : TransitionAgentTaskSucceededIdle.S P M ST)
  (TATFI   : TransitionAgentTaskFailedIdle.S P M ST)
  (TBS     : TransitionBarrierSucceeds.S P M ST)
.

  Import ST.

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

  Lemma successDec : forall s e,
    {ESuccess = statusOf s e}+{~ESuccess = statusOf s e}.
  Proof.
    move => s e.
    elim (statusOf s e).
    - left; reflexivity.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
  Qed.

  Lemma failedDec : forall s e,
    {statusFailed (statusOf s e)}+{~statusFailed (statusOf s e)}.
  Proof.
    move => s e.
    elim (statusOf s e).
    - right; move => H; inversion H.
    - left; constructor.
    - left; constructor.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
  Qed.

  Lemma successOr : forall s e,
    ESuccess = statusOf s e \/ ESuccess <> statusOf s e.
  Proof.
    move => s e.
    elim (statusOf s e).
    - left; reflexivity.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
    - right; move => H; inversion H.
  Qed.

  Lemma  successChoice : forall s e,
       ESuccess <> statusOf s e
    -> statusFailed (statusOf s e) \/ statusInProgress (statusOf s e).
  Proof.
    move => s e Hneq.
    destruct (statusOf s e) eqn:Heq.
    - contradict Hneq; reflexivity.
    - left; constructor.
    - left; constructor.
    - right; constructor.
    - right; constructor.
    - right; constructor.
    - right; constructor.
  Qed.

  (** Elements waiting for dependencies can always make progress. *)
  Theorem preconditionsChoiceWaiting : forall (s : state),
      ~stateCompleted s
    -> stateInvariants s
    -> (forall (e : P.element),
       EWaitingForDependencies = statusOf s e
    -> (exists a, TWD.preconditions s a e)
    \/ (exists a, TDF.preconditions s a e)
    \/ (exists a, TDR.preconditions s a e)).
  Proof.
    move => s HnotComp.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => e Hwait.

    unfold TWD.preconditions.
    unfold TDF.preconditions.
    unfold TDR.preconditions.

    unfold TWD.arguments.
    unfold TDF.arguments.
    unfold TDR.arguments.

    destruct (P.elementDependencies e) as [|y ys] eqn:Hdep.
    - unfold stateElementNoDependenciesNeverWaiting in Hi2.
      pose proof (Hi2 e (eq_sym Hdep)) as Hcontra.
      intuition.
    - pose proof (
        @List.Forall_dec P.element (fun e => ESuccess = statusOf s e) (successDec s)
      ) as Hdec.
      elim (Hdec (P.elementDependencies e)).
      * move => Hfa.
        do 2 right.
        exists tt.
        split.
        ** auto.
        ** rewrite <- Hdep.
           exact Hfa.
      * move => Hnfa.
        rewrite <- List.Exists_Forall_neg in Hnfa.
        rewrite Hdep in Hnfa.
        rewrite List.Exists_cons in Hnfa.
        elim Hnfa => [Hsucc|Hex].
        ** elim (successChoice Hsucc) => [Hc0|Hc1].
           *** right; left.
               exists tt.
               constructor.
               **** auto.
               **** constructor; exact Hc0.
           *** left.
               exists tt.
               constructor.
               **** auto.
               **** constructor; exact Hc1.
        ** pose proof (@List.Exists_impl _ _ _ (fun e => @successChoice s e) ys Hex) as Hor0.
           pose proof (@List.Exists_or_inv _ _ _ ys Hor0) as Hor1.
           elim Hor1 => [Hor1L|Hor1R].
           *** right; left.
               exists tt.
               constructor.
               **** auto.
               **** apply List.Exists_cons_tl; auto.
           *** left.
               exists tt.
               constructor.
               **** auto.
               **** apply List.Exists_cons_tl; auto.
        ** apply (successOr s).
  Qed.

  (** Elements that are ready can always make progress. *)
  Theorem preconditionsChoiceReady : forall (s : state),
      ~stateCompleted s
    -> stateInvariants s
    -> (forall (e : P.element),
       EReady = statusOf s e
    -> (exists a, TBS.preconditions s a e)
    \/ (exists a, TAS.preconditions s a e)).
  Proof.
    move => s HnotComp.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => e Hread.

    unfold TBS.preconditions.
    unfold TAS.preconditions.

    unfold TBS.arguments.
    unfold TAS.arguments.

    elim (P.elementIs e) => [Ht|Hb].
    - right; exists tt; constructor; auto.
    - left; exists tt; constructor; auto.
  Qed.

  (** Elements waiting for agents can always make progress. *)
  Theorem preconditionsChoiceWaitingAgents : forall (s : state),
      ~stateCompleted s
    -> stateInvariants s
    -> (forall (e : P.element) (t : nat),
         EWaitingForAgent t = statusOf s e
      -> (exists a, TAC.preconditions s a e)
      \/ (exists a, TATA.preconditions s a e)
      \/ (exists a, TATO.preconditions s a e)
    ).
  Proof.
    move => s HnotComp.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => e t Hwait.

    elim (P.elementIs e) => [Ht|Hb].
    - elim (P.agents) => [|b bs].
      * elim (@EFacts.agentDecidableStrong _ (agentIdleDec s)) => [Ha|Hna].
        ** elim Ha => [x Hx].
           right; left.
           exists (t, x).
           constructor.
           exact Ht.
           simpl; intuition.
        ** elim (PeanoNat.Nat.eq_dec t 0) => [Ht0|Htn0].
           *** do 2 right.
               exists tt.
               rewrite Ht0 in Hwait.
               constructor; auto.
           *** left.
               exists t.
               constructor; auto.
      * auto.
    - unfold stateBarrierNeverWaitingForAgent in Hi1.
      pose proof (Hi1 e t Hb).
      intuition.
  Qed.

  (** Elements that are executing can always make progress. *)
  Theorem preconditionsChoiceExecuting : forall (s : state),
      ~stateCompleted s
    -> stateInvariants s
    -> (forall (e : P.element) (t : nat) (a : P.agent),
         EExecuting a t = statusOf s e
      -> (exists a, TATS.preconditions s a e)
      \/ (exists a, TATC.preconditions s a e)
      \/ (exists a, TATTO.preconditions s a e)
      \/ (exists a, TATS.preconditions s a e)
      \/ (exists a, TATF.preconditions s a e)
    ).
  Proof.
    move => s HnotComp.
    move => [Hi0 [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]].
    move => e t a Hexec.

    unfold stateBarrierNeverExecuting in Hi0.
    unfold stateElementExecutingAgentStatus in Hi3.
    elim (P.elementIs e) => [Ht|Hb].
    - elim (Hi3 e a t Hexec) => [HL|HR].
      * left.
        exists (t, a).
        constructor; auto.
      * right; left.
        exists (t, a).
        constructor; auto.
    - pose proof (Hi0 e a t Hb) as Hexec2.
      contradiction.
  Qed.

  Inductive transition (s : state) :=
    | TrWaitingDependencies :
      forall (e : P.element),
        TWD.preconditions s tt e ->
          transition s
    | TrDependencyFailed :
      forall (e : P.element),
        TDF.preconditions s tt e ->
          transition s
    | TrDependencyReady :
      forall (e : P.element),
        TDR.preconditions s tt e ->
          transition s
    | TrAgentStart :
      forall (e : P.element),
        TAS.preconditions s tt e ->
          transition s
    | TrAgentContinue :
      forall (e : P.element) (a : TAC.arguments),
        TAC.preconditions s a e ->
          transition s
    | TrAgentTimedOut :
      forall (e : P.element) (a : TATO.arguments),
        TATO.preconditions s a e ->
          transition s
    | TrAgentTaskAccepted :
      forall (e : P.element) (a : TATA.arguments),
        TATA.preconditions s a e ->
          transition s
    | TrAgentTaskStarted :
      forall (e : P.element) (a : TATS.arguments),
        TATS.preconditions s a e ->
          transition s
    | TrAgentTaskContinue :
      forall (e : P.element) (a : TATC.arguments),
        TATC.preconditions s a e ->
          transition s
    | TrAgentTaskTimedOut :
      forall (e : P.element) (a : TATTO.arguments),
        TATTO.preconditions s a e ->
          transition s
    | TrAgentTaskSucceeded :
      forall (e : P.element) (a : TATSu.arguments),
        TATSu.preconditions s a e ->
          transition s
    | TrAgentTaskFailed :
      forall (e : P.element) (a : TATF.arguments),
        TATF.preconditions s a e ->
          transition s
    | TrAgentTaskFinishedButTimedOut :
      forall (e : P.element) (a : TATFBTO.arguments),
        TATFBTO.preconditions s a e ->
          transition s
    | TrAgentTaskSucceededIdle :
      forall (e : P.element) (a : TATSI.arguments),
        TATSI.preconditions s a e ->
          transition s
    | TrAgentTaskFailedIdle :
      forall (e : P.element) (a : TATFI.arguments),
        TATFI.preconditions s a e ->
          transition s
    | TrBarrierSucceeds :
      forall (e : P.element) (a : TBS.arguments),
        TBS.preconditions s a e ->
          transition s
    .

  Definition exec
    (s : state)
    (t : transition s)
  : state :=
    match t with
    | @TrWaitingDependencies          _ e i   => TWD.transition s tt e
    | @TrDependencyFailed             _ e i   => TDF.transition s tt e
    | @TrDependencyReady              _ e i   => TDR.transition s tt e
    | @TrAgentStart                   _ e i   => TAS.transition s tt e
    | @TrAgentContinue                _ e a i => TAC.transition s a e
    | @TrAgentTimedOut                _ e a i => TATO.transition s a e
    | @TrAgentTaskAccepted            _ e a i => TATA.transition s a e
    | @TrAgentTaskStarted             _ e a i => TATS.transition s a e
    | @TrAgentTaskContinue            _ e a i => TATC.transition s a e
    | @TrAgentTaskTimedOut            _ e a i => TATTO.transition s a e
    | @TrAgentTaskSucceeded           _ e a i => TATSu.transition s a e
    | @TrAgentTaskFailed              _ e a i => TATF.transition s a e
    | @TrAgentTaskFinishedButTimedOut _ e a i => TATFBTO.transition s a e
    | @TrAgentTaskSucceededIdle       _ e a i => TATSI.transition s a e
    | @TrAgentTaskFailedIdle          _ e a i => TATFI.transition s a e
    | @TrBarrierSucceeds              _ e a i => TBS.transition s a e
    end.

  Theorem execInvariants : forall s t,
       stateInvariants s
    -> stateInvariants (@exec s t).
  Proof.
    move => s t Hinv.
    elim t.
    - move => e p; apply (TWD.transitionInvariants Hinv p).
    - move => e p; apply (TDF.transitionInvariants Hinv p).
    - move => e p; apply (TDR.transitionInvariants Hinv p).
    - move => e p; apply (TAS.transitionInvariants Hinv p).
    - move => e a p; apply (TAC.transitionInvariants Hinv p).
    - move => e a p; apply (TATO.transitionInvariants Hinv p).
    - move => e a p; apply (TATA.transitionInvariants Hinv p).
    - move => e a p; apply (TATS.transitionInvariants Hinv p).
    - move => e a p; apply (TATC.transitionInvariants Hinv p).
    - move => e a p; apply (TATTO.transitionInvariants Hinv p).
    - move => e a p; apply (TATSu.transitionInvariants Hinv p).
    - move => e a p; apply (TATF.transitionInvariants Hinv p).
    - move => e a p; apply (TATFBTO.transitionInvariants Hinv p).
    - move => e a p; apply (TATSI.transitionInvariants Hinv p).
    - move => e a p; apply (TATFI.transitionInvariants Hinv p).
    - move => e a p; apply (TBS.transitionInvariants Hinv p).
  Qed.

  Lemma mustBeProgress : forall s,
       ESuccess <> s
    -> ~statusFailed s
    -> statusInProgress s.
  Proof.
    move => s Hsucc Hfail.
    destruct (statusChoice s) as [H1|[H2|H3]].
    - contradiction.
    - contradiction.
    - auto.
  Qed.

  Lemma notFailureChoice : forall s,
       ~statusFailed s
    -> ESuccess = s \/ statusInProgress s.
  Proof.
    move => s Hnf.
    destruct (statusChoice s) as [H1|[H2|H3]].
    - auto.
    - contradiction.
    - auto.
  Qed.

  Lemma forAllNotFailure : forall s es,
       List.Exists (fun x : P.element => ESuccess <> statusOf s x) es
    -> List.Forall (fun x : P.element => ~ statusFailed (statusOf s x)) es
    -> List.Forall (fun x : P.element => ESuccess = statusOf s x \/ statusInProgress (statusOf s x)) es.
  Proof.
    move => s es Hex Hfa.
    induction es as [|y ys].
    - constructor.
    - pose proof (List.Forall_inv Hfa) as H0.
      simpl in H0.
      rewrite List.Exists_cons in Hex.
      elim Hex => [HexL|HexR].
      * pose proof (mustBeProgress HexL H0) as H1.
        constructor.
        ** auto.
        ** apply (
             @List.Forall_impl
             P.element
             (fun x => ~ statusFailed (statusOf s x))
             (fun x => ESuccess = statusOf s x \/ statusInProgress (statusOf s x))
           ).
           move => z Hnfz.
           apply (notFailureChoice Hnfz).
           apply (List.Forall_inv_tail Hfa).
      * constructor.
        ** apply (notFailureChoice H0).
        ** apply IHys.
           exact HexR.
           apply (List.Forall_inv_tail Hfa).
  Qed.

  Lemma existsInProgress : forall s,
        stateInvariants s
    -> ~stateCompleted s
    -> List.Exists (fun f => statusInProgress (statusOf s f)) P.elements.
  Proof.
    move => s Hinv HnoComp.
    destruct P.elements as [|y ys] eqn:Heq.
    - contradict HnoComp.
      unfold stateCompleted.
      unfold stateCompletedSuccessfully.
      left.
      rewrite Heq.
      constructor.
    - unfold stateCompleted in HnoComp.
      unfold stateCompletedSuccessfully in HnoComp.
      unfold stateCompletedFailed in HnoComp.

      pose proof (
        @List.Forall_dec
          P.element
          (fun e : P.element => ESuccess = statusOf s e)
          (successDec s)
          P.elements
      ) as H0.

      pose proof (
        @List.Exists_dec
          P.element
          (fun e : P.element => statusFailed (statusOf s e))
          P.elements
          (failedDec s)
      ) as H1.

      rewrite Heq in H0.
      rewrite Heq in H1.

      destruct H0 as [H0L|H0R].
      * contradict HnoComp.
        left; rewrite Heq; auto.
      * destruct H1 as [H1L|H1R].
        ** contradict HnoComp.
           right; rewrite Heq; auto.
        ** rewrite <- List.Forall_Exists_neg in H1R.
           pose proof (
             @List.neg_Forall_Exists_neg
             _
             _
             (y :: ys)
             (successDec s)
             H0R
           ) as H0Rex.
           simpl in H0Rex.
           rewrite List.Forall_forall in H1R.
           rewrite List.Exists_exists in H0Rex.
           destruct H0Rex as [x [Hx0 Hx1]].
           rewrite List.Exists_exists.
           exists x.
           constructor.
           *** exact Hx0.
           *** apply (mustBeProgress Hx1 (H1R x Hx0)).
  Qed.

  Theorem execProgress : forall s,
       stateInvariants s
    -> ST.stateCompleted s \/ exists t, stateInvariants (@exec s t).
  Proof.
    move => s.
    move => Hinv.
    elim (C.stateCompletedDec s) => [Hsc|Hnsc].
    - left; auto.
    - right.
      pose proof (existsInProgress Hinv Hnsc) as Hex.
      rewrite List.Exists_exists in Hex.
      destruct Hex as [x [Hx0 Hx1]].
      inversion Hx1.
      * elim : (preconditionsChoiceReady Hnsc Hinv H0).
        ** move => [a H].
           exists (TrBarrierSucceeds H).
           apply (execInvariants _ Hinv).
        ** move => [a H].
           exists (TrAgentStart H).
           apply (execInvariants _ Hinv).
      * elim : (preconditionsChoiceWaiting Hnsc Hinv H0).
        ** move => [a H].
           exists (TrWaitingDependencies H).
           apply (execInvariants _ Hinv).
        ** move => Hor.
           elim Hor.
           *** move => [a H].
               exists (TrDependencyFailed H).
               apply (execInvariants _ Hinv).
           *** move => [a H].
               exists (TrDependencyReady H).
               apply (execInvariants _ Hinv).
      * elim : (preconditionsChoiceWaitingAgents Hnsc Hinv H0).
        ** move => [a H].
           exists (TrAgentContinue H).
           apply (execInvariants _ Hinv).
        ** move => Hor.
           elim Hor.
           *** move => [a H].
               exists (TrAgentTaskAccepted H).
               apply (execInvariants _ Hinv).
           *** move => [a H].
               exists (TrAgentTimedOut H).
               apply (execInvariants _ Hinv).
      * elim : (preconditionsChoiceExecuting Hnsc Hinv H0).
        ** move => [v Hv].
           exists (TrAgentTaskStarted Hv).
           apply (execInvariants _ Hinv).
        ** move => Hor.
           elim Hor.
           *** move => [v Hv].
               exists (TrAgentTaskContinue Hv).
               apply (execInvariants _ Hinv).
           *** move => Hor2.
               elim Hor2.
               **** move => [v Hv].
                    exists (TrAgentTaskTimedOut Hv).
                    apply (execInvariants _ Hinv).
               **** move => Hor3.
                    elim Hor3.
                    ***** move => [v Hv].
                          exists (TrAgentTaskStarted Hv).
                          apply (execInvariants _ Hinv).
                    ***** move => [v Hv].
                          exists (TrAgentTaskFailed Hv).
                          apply (execInvariants _ Hinv).
  Qed.

End S.

