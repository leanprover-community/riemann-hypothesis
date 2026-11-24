module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar

@[expose] public section

noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.VacDbl

theorem boxFun_mem_SB {R : Type} [TopologicalSpace R] [T2Space R] {κ κ' : Type} {φ₁ : (κ → R) → ℂ}
    {φ₂ : (κ' → R) → ℂ} (h₁ : φ₁ ∈ SB (κ → R)) (h₂ : φ₂ ∈ SB (κ' → R)) : boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → R) := by
  refine ⟨(h₁.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inl) (by fun_prop)).mul
    (h₂.1.comp_continuous (f := fun x : κ ⊕ κ' → R => x ∘ Sum.inr) (by fun_prop)), ?_⟩
  have hK : IsCompact ((fun p : (κ → R) × (κ' → R) => Sum.elim p.1 p.2) '' (tsupport φ₁ ×ˢ tsupport φ₂)) := by
    refine (IsCompact.prod h₁.2 h₂.2).image (continuous_pi ?_)
    rintro (i | i)
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_contra hne
  obtain ⟨e₁, e₂⟩ := mul_ne_zero_iff.1 hne
  refine hx ⟨(x ∘ Sum.inl, x ∘ Sum.inr), ⟨subset_tsupport _ e₁, subset_tsupport _ e₂⟩, ?_⟩
  funext i
  rcases i with i | i <;> rfl

section

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end

end GlobalTheory.CompanionTheory.VacDbl
