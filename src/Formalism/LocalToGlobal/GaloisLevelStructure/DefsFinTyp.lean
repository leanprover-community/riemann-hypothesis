module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP

namespace Formalism.L2.NG

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

structure FinTyp where
  S : Submodule ℂ (GAf L n → ℂ)
  stable : ∀ h, ∀ f ∈ S, rt L n h f ∈ S
  smooth : ∀ f ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ κ, Cong L n N κ → rt L n κ f = f
  ne : S ≠ ⊥
  irr : ∀ S' : Submodule ℂ (GAf L n → ℂ), S' ≤ S → (∀ h, ∀ f ∈ S', rt L n h f ∈ S') → S' = ⊥ ∨ S' = S

variable {L n}

def FinTyp.Iso (π π' : FinTyp L n) : Prop := IsoRep π.S π'.S

end Formalism.L2.NG
