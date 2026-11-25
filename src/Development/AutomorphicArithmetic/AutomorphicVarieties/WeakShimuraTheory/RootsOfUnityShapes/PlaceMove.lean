module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open scoped Pointwise

private theorem exists_move {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A A' : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (hA' : A'.valuation ((l : ℕ) : Ω) < 1) :
    ∃ g : G ℚ Ω, ∀ x, g x ∈ A ↔ x ∈ A' := by
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver
    (Formalism.BasicNotions.Examples₂.LB.isPlaceOver_vQ A' hA')
    (Formalism.BasicNotions.Examples₂.LB.isPlaceOver_vQ A hA)
  refine ⟨σ, fun x => ?_⟩
  rw [← hσ, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem UpperTheory.V.Ws.Rq.placeMove :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F] (p : ℕ), p.Prime →
      ∀ A A' : ValuationSubring Ω, A.valuation (p : Ω) < 1 → A'.valuation (p : Ω) < 1 → ∃ g : G ℚ Ω, (∀ x, g x ∈ A ↔ x ∈ A') ∧
        (∀ s ∈ Dec (F := F) A, g⁻¹ * resQ F s * g ∈ Dec (F := ℚ) A') ∧ ∀ s ∈ Ine (F := F) A, g⁻¹ * resQ F s * g ∈ Ine (F := ℚ) A' := by
  intro Ω _ _ _ F _ p hp A A' hA hA'
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_move p A A' hA hA'
  have hL : UpperTheory.V.IsLift (RingEquiv.refl ℚ) (g : Ω ≃+* Ω) := fun x => by simp
  have hc : ∀ t : G ℚ Ω, UpperTheory.V.conjGal hL t = g⁻¹ * t * g := by
    intro t
    ext x
    rw [UpperTheory.V.conjGal_apply]
    rfl
  have hsm : ∀ s : G F Ω, resQ F s • A = s • A := by
    intro s
    ext x
    simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨g, hg, fun s hs => ?_, fun s hs => ?_⟩
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Dec hL hg
    rw [mem_Dec] at hs ⊢
    rw [hsm, hs]
  · rw [← hc]
    apply UpperTheory.V.conjGal_mem_Ine hL hg
    rw [mem_Ine] at hs ⊢
    obtain ⟨h1, h2⟩ := hs
    refine ⟨?_, h2⟩
    rw [MulAction.mem_stabilizer_iff] at h1 ⊢
    rw [hsm, h1]
