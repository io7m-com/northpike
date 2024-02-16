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
  (P  : Plan.Parameters.S)
  (M  : TotalMap.S)
  (ST : State.S P M).

  Import ST.

  Lemma  successDec : forall s e,
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

  Theorem stateSucceededDec : forall s,
    {ST.stateCompletedSuccessfully s}+{~ST.stateCompletedSuccessfully s}.
  Proof.
    unfold stateCompletedSuccessfully.
    move => s.
    apply List.Forall_dec.
    apply successDec.
  Qed.

  Theorem stateFailedDec : forall s,
    {ST.stateCompletedFailed s}+{~ST.stateCompletedFailed s}.
  Proof.
    unfold stateCompletedFailed.
    move => s.
    apply List.Exists_dec.
    apply failedDec.
  Qed.

  Lemma successNot : forall s e,
    ESuccess = statusOf s e -> ~statusFailed (statusOf s e).
  Proof.
    move => s e Hsucc Hfalse.
    rewrite <- Hsucc in Hfalse.
    inversion Hfalse.
  Qed.

  Lemma failureNot : forall s e,
    statusFailed (statusOf s e) -> ~ESuccess = statusOf s e.
  Proof.
    move => s e Hfail Hfalse.
    rewrite <- Hfalse in Hfail.
    inversion Hfail.
  Qed.

  Lemma forallNotExists : forall
    (A   : Type)
    (P Q : A -> Prop) 
    (xs  : list A),
       (forall x, P x -> ~Q x)
    -> List.Exists P xs
    -> ~List.Forall Q xs.
  Proof.
    move => A P Q xs f Hex Hf.
    induction xs as [|y ys].
    - rewrite (@List.Exists_nil A P) in Hex.
      auto.
    - rewrite List.Exists_cons in Hex.
      destruct Hex as [HA|HB].
      * pose proof (List.Forall_inv Hf) as Qy.
        pose proof (f y HA) as Hcontra.
        contradiction.
      * apply (IHys HB (List.Forall_inv_tail Hf)).
  Qed.

  Lemma forallNotExistsSpecific : forall s xs,
    List.Exists (fun e : P.element => statusFailed (statusOf s e)) xs
    -> ~List.Forall (fun e : P.element => ESuccess = statusOf s e) xs.
  Proof.
    move => s xs Hex.
    eapply forallNotExists.
    apply failureNot.
    exact Hex.
  Qed.

  Theorem stateCompletedDec : forall s,
    {ST.stateCompleted s}+{~ST.stateCompleted s}.
  Proof.
    unfold stateCompleted.
    unfold stateCompletedSuccessfully.
    unfold stateCompletedFailed.

    move => s.
    elim (List.Forall_dec _ (successDec s) P.elements) => [HsL|HsR].
    - elim (@List.Exists_dec _ _ P.elements (failedDec s)) => [HeL|HeR].
      * pose proof (forallNotExistsSpecific HeL) as Hcontra.
        contradiction.
      * left; left; auto.
    - elim (@List.Exists_dec _ _ P.elements (failedDec s)) => [HeL|HeR].
      * left; right; auto.
      * right; intuition.
  Qed.

End S.

Module Make
  (P  : Parameters.S)
  (M  : TotalMap.S)
  (ST : State.S P M)
<: S P M ST.
  Include S P M ST.
End Make.
