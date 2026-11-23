module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.AdmEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.CasXi
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.ConjugateCuspidalReps.IsConjRepRefl

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H
open scoped ComplexOrder

theorem UpperTheory.V.Cj.H.casB :
    UpperTheory.V.Cj.H.CasB := by
  intro E _ _ _ a n e he Ξ r
  obtain ⟨c, hc⟩ := casXi E a n e he Ξ (-r)
  obtain ⟨G, hG, hadj⟩ := admEx E a Ξ
  have hell : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), ell E a (toL (star X)) = ell E a (toL X) := fun X => by
    show (∑ w : InfinitePlace E, ∑ i, ((star X) i i w).re) / _ = (∑ w : InfinitePlace E, ∑ i, (X i i w).re) / _
    simp [Matrix.star_apply]
  have hS : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X))ᴴ * G = G * shift Ξ.dmat (-r) (toL (star X)) := fun X => by
    rw [shift_apply, shift_apply, hell, conjTranspose_add, add_mul, mul_add, hadj, conjTranspose_smul,
      conjTranspose_one, star_trivial (_ : ℝ), smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  have hQ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E),
      (shift Ξ.dmat (-r) (toL X) * shift Ξ.dmat (-r) (toL X))ᴴ * G =
        G * (shift Ξ.dmat (-r) (toL (star X)) * shift Ξ.dmat (-r) (toL (star X))) := fun X => by
    rw [conjTranspose_mul, mul_assoc, hS, ← mul_assoc, hS, mul_assoc]
  have h : (cas (shift Ξ.dmat (-r)) e)ᴴ * G = G * cas (shift Ξ.dmat (-r)) e := by
    unfold cas
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : star (e j).1 = (e j).1 := (e j).2
    have h2 : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
      rw [star_smul, h1]; simp
    have h3 : toL (-(Complex.I • (e j).1)) = -toL (Complex.I • (e j).1) := rfl
    rw [conjTranspose_sub, sub_mul, hQ, hQ, h1, h2, h3, map_neg, neg_mul_neg, mul_sub]
  rw [hc, conjTranspose_smul, conjTranspose_one, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  refine ⟨c.re, ?_⟩
  unfold HasCas
  rw [hc]
  ext i j
  have hi := congrFun (congrFun h i) i
  have hp : G i i ≠ 0 := (hG.diag_pos (i := i)).ne'
  simp only [Matrix.smul_apply, smul_eq_mul] at hi
  have hs : star c = c := mul_right_cancel₀ hp hi
  rw [← Complex.conj_eq_iff_re.1 hs]
  simp
