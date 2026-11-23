module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

private lemma detShift_eq_add_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c)
    (hn : 0 < n) : lam'.detShift = lam.detShift + c := by
  simp only [DomWeight.detShift, dif_pos hn, h]

private lemma natW_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    lam'.natW = lam.natW := by
  funext i
  simp only [DomWeight.natW, detShift_eq_add_of_weight_shift n c lam lam' h (Fin.pos i), h]
  congr 1
  ring

private lemma nablaSq_eq_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    nablaSq ℂ n lam' = nablaSq ℂ n lam := by
  simp only [nablaSq, natW_eq_of_weight_shift n c lam lam' h]

private lemma detPow_detShift_of_weight_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) (g : U n) :
    detPow ℂ n (unitaryIncl n g) lam'.detShift =
      ((detU n g ^ c : ℂˣ) : ℂ) * detPow ℂ n (unitaryIncl n g) lam.detShift := by
  have hdet : Matrix.GeneralLinearGroup.det (unitaryIncl n g) = detU n g := by
    ext
    simp [detU, unitaryIncl_coe]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : detU 0 g = 1 := by
      ext
      simp [detU]
    simp [h1, DomWeight.detShift, detPow]
  · simp only [detPow, detShift_eq_add_of_weight_shift n c lam lam' h hn, hdet, zpow_add, Units.val_mul]
    ring

theorem iso_twist_det_irr_shift (n : ℕ) (c : ℤ) (lam lam' : DomWeight n) (h : ∀ i, lam'.w i = lam.w i + c) :
    Iso (twist (detU n ^ c) (irr n lam)) (irr n lam') := by
  refine ⟨LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm, fun g x => ?_⟩
  apply Subtype.ext
  change ((detU n ^ c) g : ℂ) • (sqRep ℂ n lam (unitaryIncl n g) x : MvPolynomial (Fin n × Fin n) ℂ) =
    (sqRep ℂ n lam' (unitaryIncl n g) (LinearEquiv.ofEq _ _ (nablaSq_eq_of_weight_shift n c lam lam' h).symm x) :
      MvPolynomial (Fin n × Fin n) ℂ)
  have hz : (detU n ^ c) g = detU n g ^ c := rfl
  rw [sqRep_coe, sqRep_coe, hz]
  simp only [sqAct, LinearEquiv.coe_ofEq_apply, detPow_detShift_of_weight_shift n c lam lam' h g, mul_smul]

end GlobalTheory.OneFunctional
