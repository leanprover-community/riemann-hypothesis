module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HomId
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

section SlopeTestRemainingChoices
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible

private def UpperTheory.V.Cj.H.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add (f := _), AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

private theorem UpperTheory.V.Cj.H.wigner_homomorphism : UpperTheory.V.Cj.H.WigHom := by
  intro E _ _ _ a M _ _ _ _ L α z hlie hretr
  refine ⟨fun ω h0 h1 Y => ?_, fun q ω h0 h1 => ?_⟩
  · have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
      intro X
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by
        simp only [Z]
        rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z := by
        have h : X = (hp (toL X)).1 + Z := by
          rw [hp_val]; simp only [Z]; module
        exact congrArg toL h
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add (f := _), LinearMap.add_apply, h4, h0 Z hZ Y]
      simp
    rw [← hretr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := UpperTheory.V.Cj.H.altFlip (ω.curryLeft ∘ₗ hp)
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => by
          have h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y =
              (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y) := by noncomm_ring
          exact congrArg toL h
        map_smul' := fun c X => by
          have h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y) := by
            rw [smul_sub, mul_smul_comm, smul_mul_assoc]
          exact congrArg toL h }
    refine ⟨α.compAlternatingMap F, fun Y => ?_⟩
    let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
      (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
    have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
      hlie _ _ _ fun X => (sub_add_cancel _ _).symm

    rw [dCo_apply, ← hretr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← h3]
      rfl
    · rw [LinearMap.sum_apply]
      exact homId E a M L q ω h1 h0 (Matrix.of X) Y

end SlopeTestRemainingChoices

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.wigHom :
    UpperTheory.V.Cj.H.WigHom :=
  UpperTheory.V.Cj.H.wigner_homomorphism
