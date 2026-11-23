module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

namespace UpperTheory.Gal.Int.Div

open GlobalTheory.BlockSum (blockRep)

theorem coverIn_of : CoverIn := by
  intro Γ k _ _ a d r ρ ⟨m, B, hB, hg⟩
  let n := Fintype.card (Σ _ : Fin m, Fin a)
  let e : (Σ _ : Fin m, Fin a) ≃ Fin n := Fintype.equivFin _
  let σ : Fin n ≃ Fin a × Fin m := e.symm.trans ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))
  refine ⟨m, n, e, B.submatrix σ id, ?_, fun g => ?_⟩
  · have h := Matrix.rank_submatrix B σ (Equiv.refl _)
    simpa [hB] using h
  · have key : ((blockRep (a := fun _ : Fin m => a) e fun _ => r) g : Matrix (Fin n) (Fin n) k) =
        (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k)).submatrix σ σ := by
      rw [GlobalTheory.BlockSum.blockRep_val]
      ext i j
      obtain ⟨⟨x, u⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨y, v⟩, rfl⟩ := e.surjective j
      simp [σ, Matrix.blockDiagonal'_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [key]
    have h1 : B.submatrix σ id = B.submatrix σ (Equiv.refl _) := rfl
    have h2 : (ρ g : Matrix (Fin d) (Fin d) k) = (ρ g : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl _) (Equiv.refl _) := by simp
    rw [h1, Matrix.submatrix_mul_equiv, hg g, h2, Matrix.submatrix_mul_equiv]
    simp

end UpperTheory.Gal.Int.Div
