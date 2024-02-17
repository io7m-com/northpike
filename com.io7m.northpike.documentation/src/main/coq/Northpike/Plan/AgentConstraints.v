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

Require Coq.Strings.String.

Require Import Northpike.Plan.Parameters.

Module Type S
  (P : Parameters.S).

  Inductive agentMatchE : Set :=
    | AMAnything      : agentMatchE
    | AMIsSubsetOf    : list String.string -> agentMatchE
    | AMIsSupersetOf  : list String.string -> agentMatchE
    | AMIsOverlapping : list String.string -> agentMatchE
    | AMIsEqualTo     : list String.string -> agentMatchE
    | AMIsNotEqualTo  : list String.string -> agentMatchE
    .

  Definition isSubsetOf
    {A  : Type}
    (xs : list A)
    (ys : list A)
  : Prop :=
    forall x, List.In x xs -> List.In x ys.

  Theorem isSubsetOfReflexive : forall {A : Type} (xs : list A),
    isSubsetOf xs xs.
  Proof.
    unfold isSubsetOf.
    move => A xs.
    induction xs; auto.
  Qed.

  Theorem isSubsetOfTransitive : forall {A : Type} (xs ys zs : list A),
    isSubsetOf ys zs -> isSubsetOf xs ys -> isSubsetOf xs zs.
  Proof.
    unfold isSubsetOf.
    move => A xs ys zs.
    induction xs; auto.
  Qed.

  Definition isSupersetOf
    {A  : Type}
    (xs : list A)
    (ys : list A)
  : Prop :=
    forall x, List.In x ys -> List.In x xs.

  Theorem isSupersetOfReflexive : forall {A : Type} (xs : list A),
    isSupersetOf xs xs.
  Proof.
    unfold isSupersetOf.
    move => A xs.
    induction xs; auto.
  Qed.

  Theorem isSupersetOfTransitive : forall {A : Type} (xs ys zs : list A),
    isSupersetOf zs ys -> isSupersetOf ys xs -> isSupersetOf zs xs.
  Proof.
    unfold isSupersetOf.
    move => A xs ys zs.
    induction xs; auto.
  Qed.

  Theorem isSubsetSupersetInverse : forall {A : Type} (xs ys : list A),
    isSubsetOf xs ys <-> isSupersetOf ys xs.
  Proof.
    unfold isSubsetOf.
    unfold isSupersetOf.
    move => A xs ys.
    induction xs.
    - induction ys; split; auto.
    - induction ys; split; auto.
  Qed.

  Definition isOverlapping
    {A  : Type}
    (xs : list A)
    (ys : list A)
  : Prop :=
    exists x, List.In x xs -> List.In x ys.

  Inductive agentMatches (a : P.agent) : agentMatchE -> Prop :=
    | AMPAnything   : agentMatches a AMAnything
    | AMPIsSubsetOf :
      forall (xs : list String.string),
        isSubsetOf xs (P.agentLabels a)
        -> agentMatches a (AMIsSubsetOf xs)
    | AMPIsSupersetOf :
      forall (xs : list String.string),
        isSupersetOf xs (P.agentLabels a)
        -> agentMatches a (AMIsSupersetOf xs)
    | AMPIsOverlapping :
      forall (xs : list String.string),
        isOverlapping xs (P.agentLabels a)
        -> agentMatches a (AMIsOverlapping xs)
    | AMPIsEqualTo :
      forall (xs : list String.string),
        xs = (P.agentLabels a)
        -> agentMatches a (AMIsEqualTo xs)
    | AMPIsNotEqualTo :
      forall (xs : list String.string),
        xs <> (P.agentLabels a)
        -> agentMatches a (AMIsNotEqualTo xs).

End S.

Module Make (P : Parameters.S) <: S P.
  Include S P.
End Make.
