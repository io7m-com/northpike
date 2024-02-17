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

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.

Module StringDecidable <: DecidableType.
  Definition t := string.
  Definition eq (s0 s1 : t) : Prop := s0 = s1.

  Theorem eq_equiv : Equivalence eq.
  Proof.
    constructor.
    - constructor.
    - unfold Symmetric.
      intros x.
      induction x as [|x xr].
      * induction y as [|y yr].
        ** auto.
        ** intros H.
           inversion H.
      * induction y as [|y yr].
        ** intros H.
           inversion H.
        ** intros H.
           assert (x = y) by congruence.
           assert (xr = yr) by congruence.
           subst.
           reflexivity.
    - unfold Transitive.
      intros x y z Hxy Hyz.
      rewrite Hxy.
      exact Hyz.
  Qed.

  Theorem eq_dec : forall (s0 s1 : t), {s0 = s1}+{s0 <> s1}.
  Proof.
    induction s0 as [|x xs].
    - destruct s1 as [|y ys].
      * left; auto.
      * right; discriminate.
    - destruct s1 as [|y ys].
      * right; discriminate.
      * destruct (IHxs ys) as [HL|HR].
        ** subst.
           destruct (Ascii.ascii_dec x y) as [HcL|HcR].
           *** subst; left; reflexivity.
           *** right; congruence.
        ** right; congruence.
  Qed.

End StringDecidable.

Module StringSets : MSetInterface.WSets :=
  MSetWeakList.Make StringDecidable.

Inductive exp : Set :=
  | EAnd               : exp -> exp -> exp
  | EFalse             : exp
  | EInteger           : Z -> exp
  | EIsEqual           : exp -> exp -> exp
  | ENot               : exp -> exp
  | EOr                : exp -> exp -> exp
  | EString            : string -> exp
  | EStringSetContains : string -> exp -> exp
  | ETrue              : exp
  | EVariableBoolean   : string -> exp
  | EVariableInteger   : string -> exp
  | EVariableString    : string -> exp
  | EVariableStringSet : string -> exp
  .

Inductive st : Set :=
  | SComment           : string -> st
  | SArgumentAdd       : string -> st
  | SEnvironmentClear  : st
  | SEnvironmentPass   : string -> st
  | SEnvironmentRemove : string -> st
  | SEnvironmentSet    : string -> string -> st
  | SIf                : exp -> list st -> list st -> st
  .

Inductive val : Type :=
  | VBoolean   : bool -> val
  | VInteger   : Z -> val
  | VString    : string -> val
  | VStringSet : StringSets.t -> val 
  .

Definition valEqb (v0 v1 : val) : bool :=
  match v0, v1 with
  | VBoolean   b0, VBoolean   b1 => Bool.eqb b0 b1
  | VInteger   z0, VInteger   z1 => Zeq_bool z0 z1
  | VString    s0, VString    s1 => String.eqb s0 s1
  | VStringSet s0, VStringSet s1 => StringSets.equal s0 s1
  | _, _                         => false
  end.

Inductive evalE : exp -> val -> Prop :=
  | EEAnd :
    forall (e0 e1 : exp) (v0 v1 : bool),
       evalE e0 (VBoolean v0)
    -> evalE e1 (VBoolean v1)
    -> evalE (EAnd e0 e1) (VBoolean (andb v0 v1))
  | EEFalse :
    evalE EFalse (VBoolean false)
  | EEInteger :
    forall (z : Z),
    evalE (EInteger z) (VInteger z)
  | EEIsEqual :
    forall (e0 e1 : exp) (v0 v1 : val),
       evalE e0 v0
    -> evalE e1 v1
    -> evalE (EIsEqual e0 e1) (VBoolean (valEqb v0 v1))
  | EENot :
    forall (e0 : exp) (v0 : bool),
       evalE e0 (VBoolean v0)
    -> evalE (ENot e0) (VBoolean (negb v0))
  | EEOr :
    forall (e0 e1 : exp) (v0 v1 : bool),
       evalE e0 (VBoolean v0)
    -> evalE e1 (VBoolean v1)
    -> evalE (EOr e0 e1) (VBoolean (orb v0 v1))
  | EEString :
    forall (s : string),
    evalE (EString s) (VString s)
  | EEStringSetContains :
    forall (e : exp) (v : val) (s : string) (b : bool),
       evalE e v
    -> evalE (EStringSetContains s e) (VBoolean b)
  | EETrue :
    evalE ETrue (VBoolean true)
  | EEVariableBoolean :
    forall (b : bool) (s : string),
    evalE (EVariableBoolean s) (VBoolean b)
  | EEVariableInteger :
    forall (z : Z) (s : string),
    evalE (EVariableInteger s) (VInteger z)
  | EEVariableString :
    forall (x : string) (s : string),
    evalE (EVariableString s) (VString x)
  | EEVariableStringSet :
    forall (x : StringSets.t) (s : string),
    evalE (EVariableStringSet s) (VStringSet x)
  .
