module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

namespace GlobalTheory.PtCover

theorem exists_faithfullyFlat_pow_eq :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ n : ℕ, 0 < n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D') (ψ : D →ₐ[R] D') (z : Pt A D'),
        (ψ : D →+* D').FaithfullyFlat ∧ (z ^ n : Pt A D') = spOver ψ ≫ x := by
  intro R _ A _ hA n hn D _ _ x
  obtain ⟨hf, hfl⟩ := AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA n hn
  have hs := AbelianLimit.surjective_pow A hA n hn
  let m : A.left ⟶ A.left := ((𝟙 A) ^ n : A ⟶ A).left
  have : IsFinite m := hf
  have : Flat m := hfl
  have : Surjective m := hs
  let x₀ : Spec (CommRingCat.of D) ⟶ A.left := x.left
  let Y := Limits.pullback x₀ m
  have : IsAffine Y := isAffine_of_isAffineHom (Limits.pullback.fst x₀ m)
  let q : Spec Γ(Y, ⊤) ⟶ Spec (CommRingCat.of D) := Y.isoSpec.inv ≫ Limits.pullback.fst x₀ m
  let φ : CommRingCat.of D ⟶ Γ(Y, ⊤) := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 (by
    rw [hφ]; exact ⟨inferInstance, inferInstance⟩)
  letI : Algebra R Γ(Y, ⊤) := (φ.hom.comp (algebraMap R D)).toAlgebra
  let ψ : D →ₐ[R] Γ(Y, ⊤) := { φ.hom with commutes' := fun _ ↦ rfl }
  have hψ : (spOver ψ).left = q := hφ
  have hc : (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) ≫ m = (spOver ψ ≫ x).left := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Over.comp_left, hψ]
  let z : Pt A Γ(Y, ⊤) := Over.homMk (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) (by
    rw [← Over.w (spOver ψ ≫ x), ← hc]
    simp only [Category.assoc]
    rw [Over.w ((𝟙 A) ^ n : A ⟶ A)])
  refine ⟨Γ(Y, ⊤), inferInstance, inferInstance, ψ, z, hff, ?_⟩
  rw [← Category.comp_id z, ← MonObj.comp_pow]
  exact Over.OverMorphism.ext hc

end GlobalTheory.PtCover
