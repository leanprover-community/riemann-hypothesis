module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

variable {F : Type} [Field F] {d : ℕ}

theorem extZero_toLin_injective :
    Function.Injective fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := fun _ _ h => Units.ext (Matrix.toLin'.injective h)

theorem extZero_isUnit_iff (g : Module.End F (Fin d → F)) :
    IsUnit g ↔ ∃ x : GL (Fin d) F, Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := LinearMap.isUnit_toMatrix'_iff.mpr h
    exact ⟨u, by rw [hu, Matrix.toLin'_toMatrix']⟩
  · rintro ⟨x, rfl⟩
    exact Matrix.isUnit_toLin'_iff.mpr x.isUnit

theorem extZero_toLin (χ : GL (Fin d) F → ℂ) (x : GL (Fin d) F) :
    extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x := by
  unfold extZero
  have hs : {y : GL (Fin d) F | Matrix.toLin' (y : Matrix (Fin d) (Fin d) F) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)} = {x} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact extZero_toLin_injective.eq_iff
  rw [hs, finsum_mem_singleton]

theorem extZero_of_not_isUnit (χ : GL (Fin d) F → ℂ) (g : Module.End F (Fin d → F))
    (hg : ¬ IsUnit g) : extZero χ g = 0 := by
  unfold extZero
  have hs : {x : GL (Fin d) F | Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) = g} = ∅ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro rfl
    exact hg ((extZero_isUnit_iff _).mpr ⟨x, rfl⟩)
  rw [hs, finsum_mem_empty]

theorem ipGL_eq_finsum_GL (φ φ' : Module.End F (Fin d → F) → ℂ) :
    ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) *
      star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) := by
  unfold ipGL
  have hs : {g : Module.End F (Fin d → F) | IsUnit g} =
      Set.range fun x : GL (Fin d) F => Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    ext g
    exact extZero_isUnit_iff g
  rw [hs, finsum_mem_range extZero_toLin_injective]

theorem isClassFn_extZero (χ : GL (Fin d) F → ℂ)
    (hχ : ∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) : IsClassFn (extZero χ) := by
  intro e g

  let Φ : GL (Fin d) F ≃* (Module.End F (Fin d → F))ˣ :=
    Units.mapEquiv (Matrix.toLinAlgEquiv' (R := F) (n := Fin d)).toMulEquiv
  have hcoe : ∀ x : GL (Fin d) F, ((Φ x : (Module.End F (Fin d → F))ˣ) : Module.End F (Fin d → F)) =
      Matrix.toLin' (x : Matrix (Fin d) (Fin d) F) := by
    intro x
    refine LinearMap.ext fun v => ?_
    change Matrix.toLinAlgEquiv' (x : Matrix (Fin d) (Fin d) F) v = _
    rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

  let E : (Module.End F (Fin d → F))ˣ :=
    ⟨e.toLinearMap, e.symm.toLinearMap, LinearMap.ext fun v => e.apply_symm_apply v,
      LinearMap.ext fun v => e.symm_apply_apply v⟩
  have hconj : ∀ f : Module.End F (Fin d → F),
      e.conj f = (E : Module.End F (Fin d → F)) * f * ((E⁻¹ : (Module.End F (Fin d → F))ˣ) :
        Module.End F (Fin d → F)) := by
    intro f
    exact LinearMap.ext fun v => rfl
  by_cases hg : IsUnit g
  · obtain ⟨y, rfl⟩ := (extZero_isUnit_iff g).mp hg
    have hy : e.conj (Matrix.toLin' (y : Matrix (Fin d) (Fin d) F)) =
        Matrix.toLin' ((Φ.symm E * y * (Φ.symm E)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
      rw [← hcoe (Φ.symm E * y * (Φ.symm E)⁻¹), map_mul, map_mul, map_inv, Φ.apply_symm_apply, Units.val_mul, Units.val_mul,
        hcoe y, hconj]
    rw [hy, extZero_toLin, extZero_toLin]
    simpa using hχ y (Φ.symm E)⁻¹
  · have hg' : ¬ IsUnit (e.conj g) := by
      rw [hconj, Units.isUnit_mul_units, Units.isUnit_units_mul]
      exact hg
    rw [extZero_of_not_isUnit χ _ hg', extZero_of_not_isUnit χ _ hg]

theorem extZero_spec : ∀ (F : Type) [Field F] [Finite F] (d : ℕ) (χ : GL (Fin d) F → ℂ), (∀ x : GL (Fin d) F, extZero χ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) = χ x) ∧ (∀ g, ¬ IsUnit g → extZero χ g = 0) ∧ (∀ φ φ' : Module.End F (Fin d → F) → ℂ, ipGL φ φ' = ∑ᶠ x : GL (Fin d) F, φ (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)) * star (φ' (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F)))) ∧ ((∀ g x : GL (Fin d) F, χ (x⁻¹ * g * x) = χ g) → IsClassFn (extZero χ)) := by
  intro F _ _ d χ
  exact ⟨fun x => extZero_toLin χ x, fun g hg => extZero_of_not_isUnit χ g hg,
    fun φ φ' => ipGL_eq_finsum_GL φ φ', fun h => isClassFn_extZero χ h⟩

end GlobalTheory.CuspGL
