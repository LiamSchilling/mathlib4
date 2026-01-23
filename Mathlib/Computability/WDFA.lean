/-
Copyright (c) 2020 William (Liam) Schilling. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William (Liam) Schilling
-/
module

public import Mathlib.Computability.DFA

/-!
# Weighted Deterministic Finite Automata and Deterministic Finite State Transducers

A Weighted Deterministic Finite Automaton (WDFA) is a state machine that
not only decides membership in a `Language`,
but also assigns `Semigroup`-valued weights by accumulating weight encountered
along the path uniquely determined by an input string.

In this sense, a WDFA recognizes a partial function from input strings to members of a `Semigroup`.
Deterministic Finite State Transducers (DFSTs),
which are well-known for recognizing string-to-string functions,
are easily formulated as a special case of WDFAs with weights as output strings.

As in `DFA`, the definition permits automata with infinite states, so
a `Fintype` instance must be supplied for true WDFAs.

## Main definitions

- `WDFA α σ γ`: automaton over an input alphabet `α` with states from `σ`
  assigning weights from `γ`
- `FST α σ γ`: automaton over an input alphabet `α` with states from `σ`
  assigning output strings from `List γ`
- `M.transduce x`: the function recognized by the WDFA `M`
-/

@[expose] public section

universe u v w

open Computability

/-- A WDFA is an underlying automaton (`auto`),
an initial weight (`outInitial`),
a weight for each state transition (`outStep`),
and a weight for each final state (`outFinal`). -/
structure WDFA (α : Type u) (σ : Type v) (γ : Type w) where
  /-- Underlying automaton. -/
  auto : DFA α σ
  /-- Initial weight. -/
  outInitial : γ
  /-- Transition weight. -/
  outStep : σ → α → γ
  /-- Final weight. -/
  outFinal : σ → γ

/-- A DFST is a special case of a WDFA with weights as output strings. -/
abbrev DFST (α : Type u) (σ : Type v) (γ : Type w) :=
  WDFA α σ (List γ)

namespace WDFA

variable {α : Type u} {σ : Type v} {γ : Type w} [Semigroup γ]
variable (M : WDFA α σ γ) [DecidablePred (· ∈ M.auto.accept)]

instance [Inhabited σ] [Inhabited γ] : Inhabited (WDFA α σ γ) :=
  ⟨default, default, fun _ _ => default, fun _ => default⟩

/-- Access the underlying transition function -/
abbrev step :=
  M.auto.step

/-- Access the underlying start state -/
abbrev start :=
  M.auto.start

/-- Access the underlying accepting states -/
abbrev accept :=
  M.auto.accept

/-- `M.evalFrom s y x` evaluates `M` with input `x` starting from the state `s`,
returning both the reached state and `y` with accumulated transition weight. -/
def evalFrom (s : σ) (y : γ) : List α → σ × γ :=
  List.foldl (fun (s, y) a => (M.step s a, y * M.outStep s a)) (s, y)

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`,
returning both the reached state and total accumulated weight. -/
def eval : List α → σ × γ
| x =>
  let (s, y) := M.evalFrom M.start M.outInitial x
  (s, y * M.outFinal s)

/-- `M.transduceFrom s y` is the partial function that
outputs `y` with accumulated transition weight from `s` when
the input string is accepted by the underlying automaton from `s` -/
def transduceFrom (s : σ) (y : γ) : List α → Option γ
| x =>
  let (s, y) := M.evalFrom s y x
  if s ∈ M.accept then some y else none

/-- `M.transduce` is the partial function that
outputs the total accumulated weight from `M.start` when
the input string is accepted by the underlying automaton -/
def transduce : List α → Option γ
| x =>
  let (s, y) := M.eval x
  if s ∈ M.accept then some y else none

end WDFA
