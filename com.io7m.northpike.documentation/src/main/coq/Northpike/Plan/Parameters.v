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

Require Coq.Lists.List.

Require Import Northpike.TotalMap.

(** The type of parameters for a plan. *)
Module Type S.

  (** Elements are opaque values with decidable equality. *)
  Parameter element : Set.
  Parameter elementEqDec : forall (e0 e1 : element),
    {e0 = e1}+{e0 <> e1}.

  (** An element has a list of dependencies. *)
  Parameter elementDependencies : element -> list element.

  (** The dependencies of an element are unique. *)
  Parameter elementDependenciesNoDup : forall e,
    List.NoDup (elementDependencies e).

  (** There is a list of known elements. *)
  Parameter elements : list element.

  (** The known elements are unique. *)
  Parameter elementsUnique : List.NoDup elements.

  (** In fact, every element is in the list of known elements. *)
  Parameter elementsAreFinite : forall e, List.In e elements.

  (** An element may either be a task or a barrier, and not both. *)
  Parameter elementIsTask : element -> Prop.
  Parameter elementIsBarrier : element -> Prop.

  Parameter elementIs : forall e,
    {elementIsTask e}+{elementIsBarrier e}.
  Parameter elementIsNot0 : forall e,
   elementIsTask e -> ~elementIsBarrier e.
  Parameter elementIsNot1 : forall e,
   elementIsBarrier e -> ~elementIsTask e.

  (** Agents are opaque values with decidable equality. *)
  Parameter agent : Set.
  Parameter agentEqDec : forall (e0 e1 : agent),
    {e0 = e1}+{e0 <> e1}.

  (** There is a list of known agents. *)
  Parameter agents : list agent.

  (** The known agents are unique. *)
  Parameter agentsUnique : List.NoDup agents.

  (** In fact, every agents is in the list of known agents. *)
  Parameter agentsAreFinite : forall a, List.In a agents.

  (** The maximum time that an element will wait for an agent. *)
  Parameter timeoutAgentWait : nat.

  (** The maximum time that an element will wait for execution to complete. *)
  Parameter timeoutExecution : nat.

End S.

Module Facts (P : S).

  Lemma elementDefinitelyNonexistent : forall (Q : P.element -> Prop),
       List.Forall (fun e => ~Q e) P.elements
    -> ~exists e, Q e.
  Proof.
    intros Q Hfa.
    pose proof P.elementsAreFinite as Hf.
    rewrite List.Forall_forall in Hfa.
    unfold not; intro Hfalse.
    destruct Hfalse as [x Hx].
    pose proof (Hfa x (Hf x)).
    contradiction.
  Qed.

  Lemma elementDefinitelyUninhabited0 : forall (Q : P.element -> Prop),
    nil = P.elements -> ~exists (e : P.element), Q e.
  Proof.
    intros Q Hnil.
    pose proof P.elementsAreFinite as Hf.
    unfold not; intro Hfalse.
    destruct Hfalse as [x Hx].
    pose proof (Hf x) as Hfx.
    rewrite <- Hnil in *.
    inversion Hfx.
  Qed.

  Lemma  elementDefinitelyInhabited : forall (Q : P.element -> Prop),
    List.Exists Q P.elements -> exists (e : P.element), Q e.
  Proof.
    intros Q Hex.
    pose proof P.elementsAreFinite as Hf.
    rewrite List.Exists_exists in Hex.
    destruct Hex as [x [Hx0 Hx1]].
    exists x; auto.
  Qed.

  Lemma elementDefinitelyUninhabited1 : forall (Q : P.element -> Prop),
    ~List.Exists Q P.elements -> ~exists (e : P.element), Q e.
  Proof.
    intros Q Hex.
    pose proof P.elementsAreFinite as Hf.
    rewrite <- List.Forall_Exists_neg in Hex.
    unfold not; intros Hfalse.
    destruct Hfalse as [x Hx].
    pose proof (Hf x) as Hin.
    rewrite List.Forall_forall in Hex.
    pose proof (Hex x Hin) as Hcontra.
    contradiction.
  Qed.

  Lemma elementDefinitelyUninhabited2 : forall (Q : P.element -> Prop),
    ~List.Exists Q P.elements -> forall e, ~Q e.
  Proof.
    intros Q Hex.
    pose proof P.elementsAreFinite as Hf.
    rewrite <- List.Forall_Exists_neg in Hex.
    intro e.
    rewrite List.Forall_forall in Hex.
    auto.
  Qed.

  Lemma elementDecidable : forall (Q : P.element -> Prop),
       (forall e, {Q e}+{~Q e})
    -> {exists x, Q x}+{~exists x, Q x}.
  Proof.
    intros Q Hdec.
    destruct (List.Exists_dec Q P.elements Hdec) as [HdL|HdR].
    - left; apply elementDefinitelyInhabited; auto.
    - right; apply elementDefinitelyUninhabited1; auto.
  Qed.

  Lemma elementDecidableStrong : forall (Q : P.element -> Prop),
       (forall e, {Q e}+{~Q e})
    -> {exists x, Q x}+{forall x, ~Q x}.
  Proof.
    intros Q Hdec.
    destruct (List.Exists_dec Q P.elements Hdec) as [HdL|HdR].
    - left; apply elementDefinitelyInhabited; auto.
    - right; apply elementDefinitelyUninhabited2; auto.
  Qed.

  Lemma agentDefinitelyNonexistent : forall (Q : P.agent -> Prop),
       List.Forall (fun e => ~Q e) P.agents
    -> ~exists e, Q e.
  Proof.
    intros Q Hfa.
    pose proof P.agentsAreFinite as Hf.
    rewrite List.Forall_forall in Hfa.
    unfold not; intro Hfalse.
    destruct Hfalse as [x Hx].
    pose proof (Hfa x (Hf x)).
    contradiction.
  Qed.

  Lemma agentDefinitelyUninhabited0 : forall (Q : P.agent -> Prop),
    nil = P.agents -> ~exists (e : P.agent), Q e.
  Proof.
    intros Q Hnil.
    pose proof P.agentsAreFinite as Hf.
    unfold not; intro Hfalse.
    destruct Hfalse as [x Hx].
    pose proof (Hf x) as Hfx.
    rewrite <- Hnil in *.
    inversion Hfx.
  Qed.

  Lemma agentDefinitelyInhabited : forall (Q : P.agent -> Prop),
    List.Exists Q P.agents -> exists (e : P.agent), Q e.
  Proof.
    intros Q Hex.
    pose proof P.agentsAreFinite as Hf.
    rewrite List.Exists_exists in Hex.
    destruct Hex as [x [Hx0 Hx1]].
    exists x; auto.
  Qed.

  Lemma agentDefinitelyUninhabited1 : forall (Q : P.agent -> Prop),
    ~List.Exists Q P.agents -> ~exists (e : P.agent), Q e.
  Proof.
    intros Q Hex.
    pose proof P.agentsAreFinite as Hf.
    rewrite <- List.Forall_Exists_neg in Hex.
    unfold not; intros Hfalse.
    destruct Hfalse as [x Hx].
    pose proof (Hf x) as Hin.
    rewrite List.Forall_forall in Hex.
    pose proof (Hex x Hin) as Hcontra.
    contradiction.
  Qed.

  Lemma agentDefinitelyUninhabited2 : forall (Q : P.agent -> Prop),
    ~List.Exists Q P.agents -> forall e, ~Q e.
  Proof.
    intros Q Hex.
    pose proof P.agentsAreFinite as Hf.
    rewrite <- List.Forall_Exists_neg in Hex.
    intro e.
    rewrite List.Forall_forall in Hex.
    auto.
  Qed.

  Lemma agentDecidable : forall (Q : P.agent -> Prop),
       (forall e, {Q e}+{~Q e})
    -> {exists x, Q x}+{~exists x, Q x}.
  Proof.
    intros Q Hdec.
    destruct (List.Exists_dec Q P.agents Hdec) as [HdL|HdR].
    - left; apply agentDefinitelyInhabited; auto.
    - right; apply agentDefinitelyUninhabited1; auto.
  Qed.

  Lemma agentDecidableStrong : forall (Q : P.agent -> Prop),
       (forall e, {Q e}+{~Q e})
    -> {exists x, Q x}+{forall x, ~Q x}.
  Proof.
    intros Q Hdec.
    destruct (List.Exists_dec Q P.agents Hdec) as [HdL|HdR].
    - left; apply agentDefinitelyInhabited; auto.
    - right; apply agentDefinitelyUninhabited2; auto.
  Qed.

  (** There may or may not be an agent. *)
  Lemma agentsMaybe : inhabited P.agent \/ ~inhabited P.agent.
  Proof.
    destruct P.agents as [|b bs] eqn:Hq.
    - right.
      unfold not.
      intros [a].
      pose proof (P.agentsAreFinite a) as Hf.
      rewrite Hq in Hf.
      inversion Hf.
    - left.
      constructor.
      exact b.
  Qed.

End Facts.
