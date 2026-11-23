module

public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.MultiCentre
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Summand
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock

@[expose] public section

open MeasureTheory NumberField GlobalTheory.CuspRep GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.functional_qdet_eq_aeval_shifted_polynomial :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (j : A) (l : A →ₗ[ℂ] ℂ) (p : Polynomial ℂ),
          (∀ i k, Commute (X i k) j) → (∀ (c : ℂ) (a : A), l (Formalism.REAL.qdet (fun i k => X i k - if i = k then j else 0) c * a) = p.eval c * l a) →
          ∀ v : ℂ, l (Formalism.REAL.qdet X v) = l (Polynomial.aeval j (p.comp (Polynomial.X + Polynomial.C v))) := by
  intro A _ _ n X j l p hc h v
  classical
  let B : Subalgebra ℂ A := Subalgebra.centralizer ℂ {j}
  have hB : ∀ i k, (X i k - if i = k then j else 0) ∈ B := fun i k => by
    rintro _ rfl
    refine (Commute.sub_left (hc i k) ?_).symm
    split_ifs
    · exact Commute.refl _
    · exact Commute.zero_left _
  let X' : Fin n → Fin n → B := fun i k => ⟨_, hB i k⟩
  let Q : Polynomial B := Formalism.REAL.qdet (fun i k => Polynomial.C (X' i k) + if i = k then Polynomial.X else 0) v
  have hev : ∀ (b : A) (hb : ∀ a : B, Commute (B.val a) b), Q.eval₂ (B.val : B →+* A) b =
      Formalism.REAL.qdet (fun i k => (X i k - if i = k then j else 0) + if i = k then b else 0) v := fun b hb => by
    have := UpperTheory.V.Fb.map_qdet (Polynomial.eval₂AlgHom B.val b hb)
      (fun i k => Polynomial.C (X' i k) + if i = k then Polynomial.X else 0) v
    refine Eq.trans ?_ (this.trans ?_)
    · rfl
    · congr 1
      funext i k
      rw [map_add (f := _), apply_ite (Polynomial.eval₂AlgHom B.val b hb), map_zero]
      congr 1
      · exact Polynomial.eval₂_C _ _
      · congr 1
        exact Polynomial.eval₂_X _ _
  have h1 : Q.eval₂ (B.val : B →+* A) j = Formalism.REAL.qdet X v := by
    rw [hev j (fun a => (a.2 j rfl).symm)]
    simp
  set q := p.comp (Polynomial.X + Polynomial.C v) with hq
  have h2 : ∀ (a : A) (k : ℕ), l ((Q.coeff k : A) * a) = q.coeff k * l a := fun a k => by
    have e : (∑ m ∈ Q.support, Polynomial.monomial m (l ((Q.coeff m : A) * a))) = q * Polynomial.C (l a) := by
      refine Polynomial.funext fun c => ?_
      have := h (v + c) a

      rw [← GlobalTheory.CuspRep.qdet_shift, ← hev _ (fun a => (Algebra.commutes c _).symm), Polynomial.eval₂_eq_sum, Polynomial.sum,
      Finset.sum_mul, map_sum] at this
      rw [Polynomial.eval_mul, Polynomial.eval_C, hq, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C, add_comm c v, ← this, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Polynomial.eval_monomial, ← map_pow, mul_assoc, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul,
        mul_comm]
      rfl
    have e2 := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r k) e
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Polynomial.coeff_mul_C, Finset.sum_ite_eq'] at e2
    rw [← e2]
    split_ifs with hk
    · rfl
    · rw [Polynomial.notMem_support_iff.1 hk]
      simp
  let N := max Q.natDegree q.natDegree + 1

  rw [← h1, Polynomial.eval₂_eq_sum_range' _ (show Q.natDegree < N from Nat.lt_succ_of_le (le_max_left _ _)),
  Polynomial.aeval_eq_sum_range' (show q.natDegree < N from Nat.lt_succ_of_le (le_max_right _ _)), map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, smul_eq_mul]
  exact h2 _ m
