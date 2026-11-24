module

import Development.WeilBound.CoreStatements.PlaceConnectedComponents.ArtinA
public import ReciprocityTheory.GaloisValuations.Global
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import ReciprocityTheory.GaloisValuations.GlobalB
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
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace CompanionTheory.FamInh

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]


omit [IsAlgClosure K Ω] in
theorem exists_place_between {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w ∧ w.asIdeal.LiesOver v.asIdeal := by
  apply PositivityTheory.FamInh.exists_place_between <;> assumption

theorem mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := K) A := by
  apply PositivityTheory.FamInh.mem_Ine_of_integral <;> assumption

variable [IsGalois K L]

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem coe_res_smul (σ : G K Ω) (x : 𝓞 L) :
    algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) := by
  apply PositivityTheory.FamInh.coe_res_smul <;> assumption

omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_restrictScalars (g : Ω ≃ₐ[L] Ω) : AlgEquiv.restrictNormalHom L (g.restrictScalars K : G K Ω) = 1 := by
  apply PositivityTheory.FamInh.res_restrictScalars <;> assumption

variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_mem_stabilizer (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  apply PositivityTheory.FamInh.res_mem_stabilizer <;> assumption

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem val_int_le_one (A : ValuationSubring Ω) (x : 𝓞 L) : A.valuation (algebraMap L Ω (x : L)) ≤ 1 := by
  apply PositivityTheory.FamInh.val_int_le_one <;> assumption

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_mem_inertia (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Ine (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ w.asIdeal.inertia (L ≃ₐ[K] L) := by
  apply PositivityTheory.FamInh.res_mem_inertia <;> assumption

omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem res_isArithFrobAt {v : HeightOneSpectrum (𝓞 K)} (hw : IsPlaceOver A w) [h : w.asIdeal.LiesOver v.asIdeal]
    {σ : G K Ω} (hσ : IsFrob (F := K) A (normV v) σ) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom L σ) w.asIdeal := by
  apply PositivityTheory.FamInh.res_isArithFrobAt (v := v) <;> assumption

theorem exists_lift_dec (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L}
    (hτ : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :
    ∃ σ ∈ Dec (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  apply PositivityTheory.FamInh.exists_lift_dec <;> assumption

def intAut (L : Type) [Field L] [NumberField L] [Algebra L Ω] (σ : G K Ω) : IntCl L Ω ≃+* IntCl L Ω where
  toFun b := ⟨σ b, ((isIntegral_int_of_isIntegral b.2).map (σ.toAlgHom.restrictScalars ℤ)).tower_top⟩
  invFun b := ⟨σ.symm b, ((isIntegral_int_of_isIntegral b.2).map (σ.symm.toAlgHom.restrictScalars ℤ)).tower_top⟩
  left_inv b := Subtype.ext (σ.symm_apply_apply _)
  right_inv b := Subtype.ext (σ.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul σ _ _)
  map_add' a b := Subtype.ext (map_add σ _ _)

theorem exists_lift_ine (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L} (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[K] L)) :
    ∃ σ ∈ Ine (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  apply PositivityTheory.FamInh.exists_lift_ine <;> assumption


omit [IsAlgClosure K Ω] [IsAlgClosure L Ω] in
theorem inertia_eq_bot_iff (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ ↔ w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  apply PositivityTheory.FamInh.inertia_eq_bot_iff v w <;> assumption

end CompanionTheory.FamInh

end
