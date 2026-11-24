module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN.LevelGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def act (T : Tower Ω ε) : SL(2, ℤ) →* (T.K ≃ₐ[Ω] T.K) where
  toFun γ := T.sl (ofSL γ⁻¹)
  map_one' := by ext f; simp [T.sl_one]
  map_mul' γ δ := by
    ext f
    rw [AlgEquiv.mul_apply, mul_inv_rev, map_mul, T.sl_mul]

theorem act_apply (T : Tower Ω ε) (γ : SL(2, ℤ)) (f : T.K) : act T γ f = T.sl (ofSL γ⁻¹) f := rfl

theorem sl_fix (T : Tower Ω ε) (γ : SL(2, ℤ)) :
    ∀ x ∈ IntermediateField.adjoin Ω {T.jK}, T.sl (ofSL γ) x = x := by
  have hle : IntermediateField.adjoin Ω {T.jK} ≤ IntermediateField.fixedField (act T).range := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro σ ⟨δ, rfl⟩
    exact T.j_inv _
  intro x hx
  have := (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) (act T γ⁻¹) ⟨γ⁻¹, rfl⟩
  rwa [act_apply, inv_inv] at this

def lvl (T : Tower Ω ε) (M : ℕ) : IntermediateField (IntermediateField.adjoin Ω {T.jK}) T.K where
  carrier := {f | ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f}
  mul_mem' {a b} ha hb γ hγ := by rw [map_mul, ha γ hγ, hb γ hγ]
  one_mem' γ _ := map_one _
  add_mem' {a b} ha hb γ hγ := by rw [map_add (f := _), ha γ hγ, hb γ hγ]
  zero_mem' γ _ := map_zero _
  algebraMap_mem' c γ _ := by
    rw [IntermediateField.algebraMap_apply]
    exact sl_fix T γ _ c.2
  inv_mem' x hx γ hγ := by rw [map_inv₀, hx γ hγ]

theorem act_mem_lvl (T : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) {f : T.K} (hf : f ∈ lvl T M) :
    act T γ f ∈ lvl T M := by
  intro δ hδ
  have hc : γ⁻¹ * δ * γ⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ⁻¹
  have e : γ⁻¹ * δ = (γ⁻¹ * δ * γ⁻¹⁻¹) * γ⁻¹ := by group
  rw [act_apply, ← T.sl_mul, ← map_mul, e, map_mul, T.sl_mul, hf _ hc]

def rho (T : Tower Ω ε) (M : ℕ) :
    SL(2, ℤ) →* (lvl T M ≃ₐ[IntermediateField.adjoin Ω {T.jK}] lvl T M) where
  toFun γ :=
    { toFun := fun x => ⟨act T γ x, act_mem_lvl T M γ x.2⟩
      invFun := fun x => ⟨act T γ⁻¹ x, act_mem_lvl T M γ⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (by
        show act T γ⁻¹ (act T γ x) = x
        rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply])
      right_inv := fun x => Subtype.ext (by
        show act T γ (act T γ⁻¹ x) = x
        rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (act T γ) (x : T.K) y)
      map_add' := fun x y => Subtype.ext (map_add (act T γ) (x : T.K) y)
      commutes' := fun c => Subtype.ext (by
        show act T γ (c : T.K) = (c : T.K)
        rw [act_apply]
        exact sl_fix T _ _ c.2) }
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by
    show act T 1 x = x
    rw [map_one, AlgEquiv.one_apply])
  map_mul' γ δ := AlgEquiv.ext fun x => Subtype.ext (by
    show act T (γ * δ) x = act T γ (act T δ x)
    rw [map_mul, AlgEquiv.mul_apply])

theorem rho_val (T : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) (x : lvl T M) :
    ((rho T M γ x : lvl T M) : T.K) = T.sl (ofSL γ⁻¹) x := rfl

theorem gamma_le_ker (T : Tower Ω ε) (M : ℕ) : CongruenceSubgroup.Gamma M ≤ (rho T M).ker := by
  intro γ hγ
  rw [MonoidHom.mem_ker]
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  show T.sl (ofSL γ⁻¹) x = x
  exact x.2 _ (inv_mem hγ)

theorem finite_range (T : Tower Ω ε) (M : ℕ) (hM : 0 < M) : Finite (rho T M).range := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M).FiniteIndex := by
    show (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))).ker.FiniteIndex
    exact Subgroup.finiteIndex_ker _
  haveI : (rho T M).ker.FiniteIndex := Subgroup.finiteIndex_of_le (gamma_le_ker T M)
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (rho T M)).toEquiv

end GlobalTheory.FN.LevelGal
