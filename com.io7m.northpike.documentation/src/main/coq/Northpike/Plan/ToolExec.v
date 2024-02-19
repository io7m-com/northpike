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

Module StringSets <: MSetInterface.WSets :=
  MSetWeakList.Make StringDecidable.

Inductive constant : Type :=
  | CBoolean   : bool -> constant
  | CInteger   : Z -> constant
  | CString    : string -> constant
  | CStringSet : StringSets.t -> constant
  .

Definition constantEqb (c0 c1 : constant) : bool :=
  match c0, c1 with
  | CBoolean x, CBoolean y => Bool.eqb x y
  | CInteger x, CInteger y => Zeq_bool x y
  | CString x,  CString y  => String.eqb x y
  | _, _                   => false
  end.

Inductive expression : Type :=
  | EConstant          : constant -> expression
  | EAnd               : expression -> expression -> expression
  | EIsEqual           : expression -> expression -> expression
  | ENot               : expression -> expression
  | EOr                : expression -> expression -> expression
  | EStringSetContains : string -> expression -> expression
  | EVariableBoolean   : string -> expression
  | EVariableInteger   : string -> expression
  | EVariableString    : string -> expression
  | EVariableStringSet : string -> expression
  .

Definition boolConst (b : bool) :=
  EConstant (CBoolean b).

Definition stringSetConst (s : StringSets.t) :=
  EConstant (CStringSet s).

Definition eFalse :=
  boolConst false.

Definition eTrue :=
  boolConst true.

Inductive type :=
  | TBoolean
  | TInteger
  | TString
  | TStringSet
  | TUnit
  .

Theorem typeEqDec : forall (t0 t1 : type),
  {t0 = t1}+{~t0 = t1}.
Proof. decide equality. Qed.

Inductive typeE : expression -> type -> Prop :=
  | ETConstantInteger :
    forall (z : Z),
    typeE (EConstant (CInteger z)) TInteger
  | ETConstantBoolean :
    forall (b : bool),
    typeE (EConstant (CBoolean b)) TBoolean
  | ETConstantString :
    forall (s : string),
    typeE (EConstant (CString s)) TString
  | ETConstantStringSet :
    forall (s : StringSets.t),
    typeE (EConstant (CStringSet s)) TStringSet
  | ETAnd :
    forall (e0 e1 : expression),
       typeE e0 TBoolean
    -> typeE e1 TBoolean
    -> typeE (EAnd e0 e1) TBoolean
  | ETIsEqual :
    forall (e0 e1 : expression) (t : type),
       typeE e0 t
    -> typeE e1 t
    -> typeE (EIsEqual e0 e1) TBoolean
  | ETNot :
    forall (e : expression),
       typeE e TBoolean
    -> typeE (ENot e) TBoolean
  | ETOr :
    forall (e0 e1 : expression),
       typeE e0 TBoolean
    -> typeE e1 TBoolean
    -> typeE (EOr e0 e1) TBoolean
  | ETVariableBoolean :
    forall (s : string),
    typeE (EVariableBoolean s) TBoolean
  | ETVariableInteger :
    forall (s : string),
    typeE (EVariableInteger s) TInteger
  | ETVariableString :
    forall (s : string),
    typeE (EVariableString s) TString
  | ETVariableStringSet :
    forall (s : string),
    typeE (EVariableStringSet s) TStringSet
  .

Inductive statement : Type :=
  | SComment           : string -> statement
  | SArgumentAdd       : string -> statement
  | SEnvironmentClear  : statement
  | SEnvironmentPass   : string -> statement
  | SEnvironmentRemove : string -> statement
  | SEnvironmentSet    : string -> string -> statement
  | SIf                : expression -> list statement -> list statement -> statement
  .

Inductive stepE : expression -> expression -> Prop :=
  (* And *)
  | SEAndConstant :
    forall (x y : bool),
    stepE (EAnd (boolConst x) (boolConst y)) (boolConst (andb x y))
  | SEAndStep0 :
    forall (e e' : expression) (c : constant),
       stepE e e'
    -> stepE (EAnd (EConstant c) e) (EAnd (EConstant c) e')
  | SEAndStep1 :
    forall (e0 e0' e1 : expression),
       stepE e0 e0'
    -> stepE (EAnd e0 e1) (EAnd e0' e1)

  (* IsEqual *)
  | SEIsEqualConstant :
    forall (c0 c1 : constant),
    stepE (EIsEqual (EConstant c0) (EConstant c1)) (boolConst (constantEqb c0 c1))
  | SEIsEqualStep1 :
    forall (e e' : expression) (c : constant),
       stepE e e'
    -> stepE (EIsEqual (EConstant c) e) (EIsEqual (EConstant c) e')
  | SEIsEqualStepL :
    forall (e0 e0' e1 : expression),
       stepE e0 e0'
    -> stepE (EIsEqual e0 e1) (EIsEqual e0' e1)

  (* Not *)
  | SENotConstant :
    forall (b : bool),
    stepE (ENot (boolConst b)) (boolConst (negb b))
  | SENotStep0 :
    forall (e e' : expression),
       stepE e e'
    -> stepE (ENot e) (ENot e')

  (* Or *)
  | SEOrConstant :
    forall (x y : bool),
    stepE (EOr (boolConst x) (boolConst y)) (boolConst (orb x y))
  | SEOrStep0 :
    forall (e e' e1 : expression) (c : constant),
       stepE e e'
    -> stepE (EOr (EConstant c) e) (EOr (EConstant c) e')
  | SEOrStep1 :
    forall (e0 e0' e1 : expression),
       stepE e0 e0'
    -> stepE (EOr e0 e1) (EOr e0' e1)

  (* StringSetContains *)
  | SEStringSetContainsConst0 :
    forall (s : string) (ss : StringSets.t),
    stepE (EStringSetContains s (stringSetConst ss)) (boolConst (StringSets.mem s ss))
  | SEStringSetStepL :
    forall (s : string) (e e' : expression),
       stepE e e'
    -> stepE (EStringSetContains s e) (EStringSetContains s e')
  .

Theorem stepEDeterministic : forall (e0 e1 e2: expression), 
     stepE e0 e1
  -> stepE e0 e2
  -> e1 = e2.
Proof.
  move => e0 e1 e2 He1 He2.
  generalize dependent e2.
  induction He1.
  - move => e2 He2.
    inversion He2.
    * subst; reflexivity.
    * subst; inversion H2.
    * subst; inversion H2.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H2).
      reflexivity.
    * subst.
      inversion H2.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H2).
      reflexivity.
  - move => e2 He2.
    inversion He2.
    * subst; reflexivity.
    * subst; inversion H2.
    * subst; inversion H2.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H2).
      reflexivity.
    * subst; inversion H2.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H2).
      reflexivity.
  - move => e2 He2.
    inversion He2.
    * subst; reflexivity.
    * subst; inversion H0.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H0).
      reflexivity.
  - move => e2 He2.
    inversion He2.
    * subst; reflexivity.
    * subst; inversion H2.
    * subst; inversion H2.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H2).
      reflexivity.
    * subst; inversion H2.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H2).
      reflexivity.
  - move => e2 He2.
    inversion He2.
    * subst; reflexivity.
    * subst; inversion H2.
  - move => e2 He2.
    inversion He2.
    * subst; inversion He1.
    * subst.
      rewrite (IHHe1 _ H2).
      reflexivity.
Qed.

Theorem typeDeterministic : forall (e : expression) (t0 t1 : type),
     typeE e t0
  -> typeE e t1
  -> t0 = t1.
Proof.
  move => e t0 t1 Ht0.
  induction Ht0.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
  - move => Ht1.
    inversion Ht1.
    subst.
    reflexivity.
Qed.

Theorem typeDeterministicInv : forall (e : expression) (t0 t1 : type),
     typeE e t0
  -> ~typeE e t1
  -> t0 <> t1.
Proof.
  move => e t0 t1 Ht0.
  induction Ht0.
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor; auto).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; apply (ETIsEqual Ht0_1 Ht0_2)).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor; auto).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor; auto).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor; auto).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor; auto).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor; auto).
  - move => Ht1.
    destruct t1; discriminate || (contradict Ht1; constructor; auto).
Qed.

Lemma typeEUnique : forall (e0 e1 : expression) (t : type),
      typeE e0 t
  -> ~typeE e1 t
  -> ~(exists u, typeE e1 t /\ u = t).
Proof.
  move => e0 e1 t Ht0.
  induction Ht0.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
  - move => Ht1.
    intro Hfalse; inversion Hfalse; intuition.
Qed.

Theorem typeEDecidable : forall (e : expression) (t : type), 
  {typeE e t}+{~typeE e t}.
Proof.
  induction e.
  - destruct c as [b|i|s|ss];
      destruct t; (left; constructor) || (right; intro Hf; inversion Hf).
  - destruct (IHe1 TBoolean) as [tl1|t1r].
    * destruct (IHe2 TBoolean) as [tl2|t2r].
      ** move => t.
         destruct t; (left; constructor) || (right; intro H; inversion H); auto.
      ** move => t.
         right.
         intros H.
         inversion H.
         subst.
         contradiction.
    * right.
      intros H.
      inversion H.
      subst.
      contradiction.
  - move => u.

Abort.

Inductive state : Set :=
  State : forall (arguments : list string), state.

Definition withArgument
  (st : state)
  (a  : string)
: state :=
  match st with
  | State args => State (List.app args (cons a nil))
  end.

Inductive stepS : state -> statement -> state -> Prop :=
  | SSComment :
    forall (st : state) (s : string),
      stepS st (SComment s) st
  | SSArgumentAdd :
    forall (st : state) (s : string),
      stepS st (SArgumentAdd s) (withArgument st s)
  .
