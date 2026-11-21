import Mathlib
import Formalism.LocalRingCardinality.Params

namespace GlobalTheory.IndefiniteRowSideFullHecke.InternalDirectSumCriteria
open Formalism.BasicNotions

universe u v

def PartsSum (R : Ranks) {FT : Type u} (M : ℕ → Type v) [∀ j, AddCommGroup (M j)] [∀ j, Module ℂ (M j)]
    (part : ∀ j, FT → Submodule ℂ (M j)) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → iSupIndep (part j) ∧ ⨆ π, part j π = ⊤

def PartsSumIn (R : Ranks) {FT : Type u} (A : ℕ → Type v) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    (M : ∀ j, Submodule ℂ (A j)) (part : ∀ j, FT → Submodule ℂ (A j)) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → iSupIndep (part j) ∧ ⨆ π, part j π = M j






end GlobalTheory.IndefiniteRowSideFullHecke.InternalDirectSumCriteria
