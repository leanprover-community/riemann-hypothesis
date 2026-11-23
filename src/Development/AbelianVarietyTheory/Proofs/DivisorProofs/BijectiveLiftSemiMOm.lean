module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open TensorProduct GlobalTheory.CechDR GlobalTheory.DeRham

namespace GlobalTheory.FormsBaseChange

theorem bijective_liftSemi_iff {R R' B B' M N : Type} [CommRing R] [CommRing R'] [CommRing B]
    [CommRing B'] [Algebra R R'] [Algebra R B] [Algebra R' B'] [Algebra B B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R R' B'] [Algebra.IsPushout R R' B B']
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    [AddCommGroup N] [Module B N] [Module B' N] [Module R' N] [IsScalarTower B B' N]
    [IsScalarTower R' B' N] (φ : M →ₗ[B] N) (g : M →ₛₗ[algebraMap R R'] N) (e : ∀ x, g x = φ x) :
    Function.Bijective (liftSemi g) ↔ IsBaseChange B' φ := by
  have hc : (liftSemi g : R' ⊗[R] M → N) =
      φ.liftBaseChange B' ∘ (Algebra.IsPushout.cancelBaseChange R R' B B' M).symm := by
    funext z
    induction z with
    | add x y hx hy => simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul s m => simp [e]
  rw [hc, Function.Bijective.of_comp_iff _ (LinearEquiv.bijective _)]
  constructor
  · intro H
    exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ H) fun x ↦ by simp
  · intro H
    have : (φ.liftBaseChange B' : B' ⊗[B] M → N) = H.equiv := by
      funext z
      induction z with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s m => simp
    rw [this]
    exact H.equiv.bijective

theorem bijective_liftSemi_mOm (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (B B' : Type)
    [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] (α : B →+* B')
    (h : SemiHom (algebraMap R R') α) (f : B →ₛₗ[algebraMap R R'] B') (hf : ∀ b, f b = α b)
    (h0 : Function.Bijective (liftSemi f)) (h1 : Function.Bijective (liftSemi h.m1)) (j : ℕ) :
    Function.Bijective (liftSemi (h.mOm j)) := by
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra R B' := ((algebraMap R' B').comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower R B B' := .of_algebraMap_eq fun r ↦ (h.map_algebraMap r).symm
  haveI : Algebra.IsPushout R R' B B' :=
    ⟨IsBaseChange.of_equiv (LinearEquiv.ofBijective _ h0) fun x ↦ by
      change liftSemi f (1 ⊗ₜ x) = α x
      rw [liftSemi_tmul, one_smul, hf]⟩
  let φ : Ω[B⁄R] →ₗ[B] Ω[B'⁄R'] :=
    { toFun := h.m1
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.oneFormMap_smul_semilinear, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  have hφ : IsBaseChange B' φ := (bijective_liftSemi_iff φ h.m1 fun _ ↦ rfl).1 h1
  refine (bijective_liftSemi_iff _ (h.mOm j) ?_).2 (GlobalTheory.TopForm.isBaseChange_exteriorPower hφ j)
  let ψ : Om R B j →ₗ[B] Om R' B' j :=
    { toFun := h.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ by
        rw [h.mOm_smul, RingHom.id_apply, ← algebraMap_smul B' b]; rfl }
  suffices H : ψ = _ from fun x ↦ LinearMap.congr_fun H x
  apply exteriorPower.linearMap_ext
  ext1 v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
  refine Subtype.ext ?_
  change h.mDR (exteriorPower.ιMulti B j v : DR R B) = _
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext k
  exact h.mDR_ι _

end GlobalTheory.FormsBaseChange
