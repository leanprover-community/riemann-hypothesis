module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobius
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem finsum_GL_toLin' {F : Type} [Field F] (m : ℕ) (f : Module.End F (Fin m → F) → ℂ) :
    ∑ᶠ x : GL (Fin m) F, f (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F)) =
      ∑ᶠ g ∈ {g : Module.End F (Fin m → F) | IsUnit g}, f g := by
  rw [← finsum_mem_univ]
  refine finsum_mem_eq_of_bijOn
    (fun x : GL (Fin m) F => (Matrix.toLin' (x : Matrix (Fin m) (Fin m) F) : Module.End F (Fin m → F)))
    ⟨?_, ?_, ?_⟩ (fun _ _ => rfl)
  · intro x _
    exact (Units.isUnit x).map (Matrix.toLinAlgEquiv' (R := F) (n := Fin m))
  · intro x _ y _ h
    exact Units.ext (Matrix.toLin'.injective h)
  · intro g hg
    have h : IsUnit ((Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).symm g) := IsUnit.map _ hg
    refine ⟨h.unit, Set.mem_univ _, ?_⟩
    exact (Matrix.toLinAlgEquiv' (R := F) (n := Fin m)).apply_symm_apply g

theorem finsum_cusp_mul_star_chG : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k l : ℕ, 0 < m → ∑ᶠ x, cusp θ m k x * star (chG (rootSum θ l) m x) = (-1) ^ (m - 1) * (Nat.card (GL (Fin m) F) : ℂ) * (((Finset.range m).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ m - 1)])).card : ℂ) := by
  intro F _ _ θ hθ m k l hm
  have hr : Module.finrank F (Fin m → F) = m := by simp
  have h := ipGL_psi_rootSum F (Fin m → F) θ hθ (by rw [hr]; exact hm) k l
  rw [hr, ipGL, ← finsum_GL_toLin', glCard] at h
  rw [mul_assoc, ← h, mul_finsum]
  refine finsum_congr fun x => ?_
  simp only [cusp, psiG, chG, Matrix.charpoly_toLin', mul_assoc]

end GlobalTheory.Shin
