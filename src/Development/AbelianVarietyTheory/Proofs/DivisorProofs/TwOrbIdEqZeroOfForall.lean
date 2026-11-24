module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.DZA.OrbSupp

open GlobalTheory.BCT

variable {G : Type} [Group G] [TopologicalSpace G]

theorem exists_twConj_ne_zero (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (h : twOrb θ K δ f ≠ 0) :
    ∃ x, f (x⁻¹ * δ * θ x) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold twOrb
  simp only [hc]
  simp [avg]

theorem twOrb_eq_zero_of_forall (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (h : ∀ x, f (x⁻¹ * δ * θ x) = 0) : twOrb θ K δ f = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := exists_twConj_ne_zero θ K δ f hne
  exact hx (h x)

theorem exists_conj_ne_zero (K : Subgroup G) (γ : G) (f : G → ℂ) (h : twOrb (MonoidHom.id G) K γ f ≠ 0) :
    ∃ x, f (x⁻¹ * γ * x) ≠ 0 :=
  exists_twConj_ne_zero (MonoidHom.id G) K γ f h

theorem twOrb_id_eq_zero_of_forall (K : Subgroup G) (γ : G) (f : G → ℂ) (h : ∀ x, f (x⁻¹ * γ * x) = 0) :
    twOrb (MonoidHom.id G) K γ f = 0 :=
  twOrb_eq_zero_of_forall (MonoidHom.id G) K γ f h

end GlobalTheory.DZA.OrbSupp
