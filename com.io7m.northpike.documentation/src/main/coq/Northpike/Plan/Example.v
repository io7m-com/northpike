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

Require Import Northpike.Plan.Parameters.
Require Import Northpike.TotalMap.

Require Import Coq.Lists.List.

Import ListNotations.

Module ExamplePlan : Plan.Parameters.S.

  Inductive e : Set :=
    | E1
    | E2
    | E3
    | E4
    | E5
    | E6
    .

  (** Elements are opaque values with decidable equality. *)
  Definition element := e.

  Theorem elementEqDec : forall e0 e1 : element,
    {e0 = e1}+{e0 <> e1}.
  Proof.
    destruct e0; destruct e1; decide equality.
  Qed.

  (** An element has a list of dependencies. *)
  Definition elementDependencies (e : element) : list element :=
    match e with
    | E6 => [E5; E4; E3]
    | E5 => [E2]
    | E4 => [E1]
    | E3 => []
    | E2 => []
    | E1 => []
    end.

  (** The dependencies of an element are unique. *)
  Theorem elementDependenciesNoDup : forall e,
    List.NoDup (elementDependencies e).
  Proof.
    unfold elementDependencies.
    destruct e0; (constructor || intuition).
    all: (simpl; intuition || constructor).
    contradict H0; discriminate.
    contradict H; discriminate.
    simpl; intuition; contradict H0; discriminate.
    constructor; intuition.
    constructor.
  Qed.

  (** There is a list of known elements. *)
  Definition elements :=
    [E1;E2;E3;E4;E5;E6].

  (** The known elements are unique. *)
  Theorem elementsUnique : List.NoDup elements.
  Proof.
    compute.

    assert (@NoDup element []) as H0 by constructor.

    assert (NoDup [E6]) as H6. {
      constructor.
      intuition.
      auto.
    }

    assert (NoDup [E5; E6]) as H5. {
      assert (~In E5 [E6]) as H.
      - compute.
        intros H; destruct H as [HL|HR].
        * contradict HL.
          congruence.
        * auto.
      - apply (NoDup_cons E5 H H6).
    }

    assert (NoDup [E4; E5; E6]) as H4. {
      constructor.
      - compute.
        intros [Hf0|[Hf1|Hf2]].
        contradict Hf0; congruence.
        contradict Hf1; congruence.
        intuition.
      - auto.
    }

    assert (NoDup [E3; E4; E5; E6]) as H3. {
      constructor.
      - compute.
        intros [Hf0|[Hf1|[Hf2|Hf3]]].
        contradict Hf0; congruence.
        contradict Hf1; congruence.
        contradict Hf2; congruence.
        intuition.
      - auto.
    }

    assert (NoDup [E2; E3; E4; E5; E6]) as H2. {
      constructor.
      - compute.
        intros [Hf0|[Hf1|[Hf2|[Hf3|Hf4]]]].
        contradict Hf0; congruence.
        contradict Hf1; congruence.
        contradict Hf2; congruence.
        contradict Hf3; congruence.
        intuition.
      - auto.
    }

    constructor.
    - compute.
      intros [Hf0|[Hf1|[Hf2|[Hf3|[Hf4|Hf5]]]]].
      contradict Hf0; congruence.
      contradict Hf1; congruence.
      contradict Hf2; congruence.
      contradict Hf3; congruence.
      contradict Hf4; congruence.
      intuition.
    - trivial.
  Qed.

  (** In fact, every element is in the list of known elements. *)
  Theorem elementsAreFinite : forall e, List.In e elements.
  Proof. compute; destruct e0; intuition. Qed.

  Definition tasks :=
    [E1;E2;E3;E4;E5].

  Definition barriers :=
    [E6].

  Definition elementIsTask (e : element) : Prop :=
    In e tasks.

  Definition elementIsBarrier (e : element) : Prop :=
    In e barriers.

  (** An element may either be a task or a barrier. *)
  Theorem elementIs : forall e, {elementIsTask e}+{elementIsBarrier e}.
  Proof. compute; destruct e0; intuition. Qed.

  Theorem elementIsNot0 : forall e,
    elementIsTask e -> ~elementIsBarrier e.
  Proof.
    compute.
    destruct e0; intuition; contradict H; discriminate.
  Qed.

  Theorem elementIsNot1 : forall e,
    elementIsBarrier e -> ~elementIsTask e.
  Proof.
    compute.
    destruct e0; intuition; contradict H1; discriminate.
  Qed.

  Inductive a : Set :=
    | A1
    | A2
    | A3
    .

  (** Agents are opaque values with decidable equality. *)
  Definition agent := a.
  Theorem agentEqDec : forall a0 a1 : agent,
    {a0 = a1}+{a0 <> a1}.
  Proof.
    destruct a0; destruct a1; decide equality.
  Qed.

  (** There is a list of known agents. *)
  Definition agents : list agent := [A1;A2;A3].

  (** The known agents are unique. *)
  Theorem agentsUnique : List.NoDup agents.
  Proof.
    compute.
    assert (NoDup [A3]) as H3. {
      constructor.
      intuition.
      constructor.
    }
    assert (NoDup [A2; A3]) as H2. {
      assert (~In A2 [A3]) as H.
      - compute.
        intros H; destruct H as [HL|HR].
        * contradict HL.
          congruence.
        * auto.
      - apply (NoDup_cons A2 H H3).
    }
    constructor.
    - compute.
      intros [Hf0|[Hf1|Hf2]].
      contradict Hf0; congruence.
      contradict Hf1; congruence.
      contradict Hf2; congruence.
    - trivial.
  Qed.

  (** In fact, every agent is in the list of known agents. *)
  Theorem agentsAreFinite : forall e, List.In e agents.
  Proof. compute; destruct e0; intuition. Qed.

  (** The maximum time that an element will wait for an agent. *)
  Definition timeoutAgentWait : nat := 5.

  (** The maximum time that an element will wait for execution to complete. *)
  Definition timeoutExecution : nat := 5.

End ExamplePlan.
