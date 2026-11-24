module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneAbs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IneCard
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrData
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC UpperTheory.V
open UpperTheory.V.W (Plc Lp resP)

theorem UpperTheory.isUnramifiedAt_totallyReal_of_inertia_le_restriction_range :
    ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω], (∀ (A : ValuationSubring Ω) (v : Plc (Lp L)), IsPlaceOver A v → Ine (F := Lp L) A ≤ (resP L Ω).range) → ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal := by
  intro L Ω _ _ _ _ _ _ h w
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let v : Plc (Lp L) := ⟨w.asIdeal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)), inferInstance, by
    exact Ideal.IsMaximal.ne_bot_of_isIntegral_int (Ideal.comap (algebraMap (𝓞 (Lp L)) (𝓞 L)) w.asIdeal)⟩
  have hv : IsPlaceOver A v := by
    intro x
    have h1 := hA (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    show _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ w.asIdeal
    rw [← h1, IsScalarTower.algebraMap_apply (Lp L) L Ω]
    rfl
  have hle := h A v hv
  have hbot : Ideal.inertia Gal(L/(Lp L)) w.asIdeal = ⊥ := by
    rw [← UpperTheory.V.CF.ineAbs (Lp L) L Ω A w hA, eq_bot_iff]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, rfl⟩ := hle hσ
    rw [Subgroup.mem_bot]
    ext x
    apply (algebraMap L Ω).injective
    rw [AlgEquiv.one_apply]
    show algebraMap L Ω ((AlgEquiv.restrictScalars (Lp L) τ).restrictNormal L x) = _
    rw [AlgEquiv.restrictNormal_commutes]
    exact τ.commutes x
  refine Ideal.ramificationIdx_eq_one_iff.mp ?_
  rw [← (UpperTheory.V.CF.ineCard).1 (Lp L) L w, hbot]
  simp
