module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LFunctionMinors.FintypeColChoice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MvPolynomial Finset Matrix

noncomputable section

namespace PI.WwMainW

open PI.WwMain PI.WwMain.KM

theorem block (hCB : CBSorted) {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (z : Lt × Fin N0 × Fin N1 → ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) (s : Lt) (p : ℕ) :
    Matrix.det (Matrix.of fun i j : Fin p => ∑ a : Fin N0,
        C (∑ b : Fin N1, z (s, a, b) * y' s b (j : ℕ)) *
          (X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) =
      ∑ J : Fin p ↪o Fin N1, C (Matrix.det (Matrix.of fun i j : Fin p => y' s (J i) (j : ℕ))) *
        chi l N0 N1 z (minorXZ N0 N1 s p J) := by
  unfold chi minorXZ
  calc _ = ((Matrix.of (fun (i : Fin p) (b : Fin N1) => (∑ a : Fin N0,
          (X (s, (i : ℕ), a) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]) * C (z (s, a, b)) :
            MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) :
            Matrix (Fin p) (Fin N1) (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) *
        (Matrix.of (fun (b : Fin N1) (j : Fin p) =>
          (C (y' s b (j : ℕ)) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l])) :
            Matrix (Fin N1) (Fin p) (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))).det := by
        congr 1
        refine Matrix.ext fun i j => ?_

        simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, map_mul, Finset.sum_mul]
        first
          | (rw [Finset.sum_comm]
             exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)
          | exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
          | (rw [Finset.sum_comm]; ring)
    _ = _ := hCB _ _ _ _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun J _ => ?_
        refine (mul_comm _ _).trans ?_
        congr 1
        · rw [RingHom.map_det]
          congr 1
          try (refine Matrix.ext fun i j => ?_; simp [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply])
        · rw [RingHom.map_det]
          congr 1
          try (refine Matrix.ext fun i k => ?_; simp [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
            map_sum, MvPolynomial.eval₂Hom_X'])

theorem deXCB_of (hCB : CBSorted) : DeXCB := by
  unfold DeXCB
  intro Lt _ _ l _ N0 N1 nu z y'
  unfold DeX minY Gxz
  simp only [block hCB l N0 N1 z y', map_prod, ← Finset.prod_mul_distrib]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  first
    | rfl
    | (congr 1)
    | exact Finset.sum_congr (Subsingleton.elim _ _) fun _ _ => rfl

end PI.WwMainW
