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

(** ** Plan Execution State
  Types and theorems relating to the state of a plan _P_.
 *)

Module Type S
  (P    : Parameters.S)
  (Maps : TotalMap.S).

  Module AgentKeys : TotalMap.KeyT with
    Definition t     := P.agent.
    Definition t     := P.agent.
    Definition eqDec := P.agentEqDec.
  End AgentKeys.

  Module ElementKeys : TotalMap.KeyT with
    Definition t     := P.element.
    Definition t     := P.element.
    Definition eqDec := P.elementEqDec.
  End ElementKeys.

  Module AMaps :=
    Maps AgentKeys.

  Module EMaps :=
    Maps ElementKeys.

  Module EFacts :=
    Facts P.

  (** The status of an execution element. *)
  Inductive status : Set :=
    | ESuccess                : status
    | EFailure                : status
    | EFailureTimedOut        : status
    | EWaitingForDependencies : status
    | EWaitingForAgent        : nat -> status
    | EReady                  : status
    | EExecuting              : P.agent -> nat -> status
    .

  (** The subset of status values that mean "in progress". *)
  Inductive statusInProgress : status -> Prop :=
    | IPReady                  : statusInProgress EReady
    | IPWaitingForDependencies : statusInProgress EWaitingForDependencies
    | IPWaitingForAgent        : forall n, statusInProgress (EWaitingForAgent n)
    | IPExecuting              : forall a n, statusInProgress (EExecuting a n)
    .

  (** The subset of status values that indicate failure. *)
  Inductive statusFailed : status -> Prop :=
    | IFailure         : statusFailed EFailure
    | IFailureTimedOut : statusFailed EFailureTimedOut
    .

  (** The subset of status values that indicate completion. *)
  Definition statusCompleted (s : status) : Prop :=
    statusFailed s \/ ESuccess = s.

  (** Status values may fall into one of three categories. *)
  Lemma statusChoice : forall s,
       ESuccess = s
    \/ statusFailed s
    \/ statusInProgress s.
  Proof.
    intros s.
    destruct s;
       (left; reflexivity)
    || (right; left; constructor)
    || (right; right; constructor).
  Qed.

  (** The status of an agent. **)
  Inductive agentStatus : Set :=
    | ASIdle          : agentStatus
    | ASAccepted      : P.element -> agentStatus
    | ASExecuting     : P.element -> agentStatus
    | ASFailed        : P.element -> agentStatus
    | ASSucceeded     : P.element -> agentStatus
    .

  (** The state of an executing plan. *)
  Inductive state : Set :=
    State : (EMaps.t status)
         -> (AMaps.t agentStatus)
         -> state.

  Definition statusOf
    (s : state)
    (e : P.element) 
  : status :=
    match s with
    | State es _ => EMaps.get es e
    end.

  Definition withStatus
    (s : state)
    (e : P.element)
    (x : status)
  : state :=
    match s with
    | State es aas => State (EMaps.put es e x) aas
    end.

  Definition agentStatusOf
    (s : state)
    (a : P.agent)
  : agentStatus :=
    match s with
    | State _ aes => AMaps.get aes a
    end.

  Definition withAgentStatus
    (s : state)
    (a : P.agent)
    (x : agentStatus)
  : state :=
    match s with
    | State es aes => State es (AMaps.put aes a x) 
    end.

  (** Identity for withStatus and statusOf. *)
  Lemma withStatusOf : forall s e x,
    statusOf (withStatus s e x) e = x.
  Proof.
    unfold statusOf, withStatus in *.
    intro s. intros.
    destruct s; rewrite <- EMaps.putGet; reflexivity.
  Qed.

  (** Well-behaved keys for withStatus and statusOf. *)
  Lemma withStatusNotOf : forall s e0 e1 x,
    e0 <> e1 -> statusOf s e0 = statusOf (withStatus s e1 x) e0.
  Proof.
    unfold statusOf, withStatus in *.
    intro s. intros.
    destruct s; rewrite <- EMaps.putRemains; auto.
  Qed.

  (** Identity for withStatus and statusOf. *)
  Lemma withStatusWithStatus : forall s e x0 x1,
    withStatus (withStatus s e x0) e x1 = withStatus s e x1.
  Proof.
    unfold statusOf, withStatus in *.
    intro s. intros.
    destruct s; rewrite <- EMaps.putPut; reflexivity.
  Qed.

  (** Identity for withAgentStatus and agentStatusOf. *)
  Lemma withAgentStatusOf : forall s e x,
    agentStatusOf (withAgentStatus s e x) e = x.
  Proof.
    unfold agentStatusOf, withAgentStatus in *.
    intro s. intros.
    destruct s; rewrite <- AMaps.putGet; reflexivity.
  Qed.

  (** Well-behaved keys for withAgentStatus and agentStatusOf. *)
  Lemma withAgentStatusNotOf : forall s e0 e1 x,
    e0 <> e1 -> agentStatusOf s e0 = agentStatusOf (withAgentStatus s e1 x) e0.
  Proof.
    unfold agentStatusOf, withAgentStatus in *.
    intro s. intros.
    destruct s; rewrite <- AMaps.putRemains; auto.
  Qed.

  (** withAgentStatus and statusOf are independent. *)
  Lemma statusOfIndependence : forall s e a x,
    statusOf s e = statusOf (withAgentStatus s a x) e.
  Proof.
    unfold statusOf, withStatus, withAgentStatus in *.
    intro s. intros.
    destruct s; reflexivity.
  Qed.

  (** withAgentStatus and statusOf are independent. *)
  Lemma agentStatusOfIndependence : forall s e a x,
    agentStatusOf s e = agentStatusOf (withStatus s a x) e.
  Proof.
    unfold statusOf, withStatus, withAgentStatus in *.
    intro s. intros.
    destruct s; reflexivity.
  Qed.

  (** ** State Invariants *)

  (** A barrier can never be in an executing state. *)
  Definition stateBarrierNeverExecuting (s : state) : Prop :=
    forall e a n,
         P.elementIsBarrier e
      -> EExecuting a n <> statusOf s e.

  (** A barrier can never be waiting for an agent. *)
  Definition stateBarrierNeverWaitingForAgent (s : state) : Prop :=
    forall e n,
         P.elementIsBarrier e 
      -> EWaitingForAgent n <> statusOf s e.

  (** An element with no dependencies can never be waiting for dependencies. *)
  Definition stateElementNoDependenciesNeverWaiting (s : state) : Prop :=
    forall e,
         nil = (P.elementDependencies e)
      -> EWaitingForDependencies <> statusOf s e.

  (** If an element is executing, the agent state must match. *)
  Definition stateElementExecutingAgentStatus (s : state) : Prop :=
    forall e a n,
         EExecuting a n = statusOf s e
      -> ASAccepted e = agentStatusOf s a \/ ASExecuting e = agentStatusOf s a.

  (** Element timeouts are in range. *)
  Definition stateElementTimeValid0 (s : state) : Prop :=
    forall e n,
         (EWaitingForAgent n) = statusOf s e
      -> n <= P.timeoutAgentWait.

  (** Element timeouts are in range. *)
  Definition stateElementTimeValid1 (s : state) : Prop :=
    forall e a n,
         (EExecuting a n) = statusOf s e
      -> n <= P.timeoutExecution.

  (** The set of invariants that must hold for any state. *)
  Definition stateInvariants (s : state) : Prop :=
       stateBarrierNeverExecuting s
    /\ stateBarrierNeverWaitingForAgent s
    /\ stateElementNoDependenciesNeverWaiting s
    /\ stateElementExecutingAgentStatus s
    /\ stateElementTimeValid0 s
    /\ stateElementTimeValid1 s.

  (** ** State Completion *)

  (** If all elements succeeded, the state is considered successfully completed. *)
  Definition stateCompletedSuccessfully (s : state) : Prop :=
    List.Forall (fun e => ESuccess = statusOf s e) P.elements.

  (** If any element failed, the state is considered failed. *)
  Definition stateCompletedFailed (s : state) : Prop :=
    List.Exists (fun e => statusFailed (statusOf s e)) P.elements.

  (** The state is completed iff it has succeeded or failed. *)
  Definition stateCompleted (s : state) : Prop :=
    stateCompletedSuccessfully s \/ stateCompletedFailed s.

End S.

Module Make
  (P    : Parameters.S)
  (Maps : TotalMap.S)
<: S P Maps.
  Include S P Maps.
End Make.
