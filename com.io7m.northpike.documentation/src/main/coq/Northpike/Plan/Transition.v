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
Require Import Northpike.Plan.State.

Module Type S
  (P  : Plan.Parameters.S)
  (M  : TotalMap.S)
  (ST : State.S P M).

  Import ST.

  Parameter arguments : Set.

  (** The preconditions required for the state transition. *)
  Parameter preconditions : state -> arguments -> P.element -> Prop.

  (** For a given element _e_ and state _s_, the precondition is decidable. *)
  Parameter preconditionsDecidableE : forall
    (s : state)
    (a : arguments)
    (e : P.element),
      {preconditions s a e}+{~preconditions s a e}.

  (** For a given element state _s_, it is decidable whether there is an 
      element for which the precondition holds. *)
  Parameter preconditionsDecidable : forall
    (s : state)
    (a : arguments),
      {exists e, preconditions s a e}+{~exists e, preconditions s a e}.

  (** The state transition. *)
  Parameter transition : state -> arguments -> P.element -> state.

  (** The transition preserves state invariants. *)
  Parameter transitionInvariants : forall s a e,
       stateInvariants s
    -> preconditions s a e
    -> stateInvariants (transition s a e).

End S.
