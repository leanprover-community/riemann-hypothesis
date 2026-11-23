module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Perfect

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.LinDesc

theorem charpoly_companion_separable : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F),
    A.IsGen τ p → (companion p).charpoly.Separable := by
  intro F E _ _ _ _ hU A r τ p hG
  haveI : CharZero F := hU.charZero
  set P := (companion p).charpoly with hP
  have hmon : P.Monic := Matrix.charpoly_monic _
  have hdeg : P.natDegree = r := simp [hP, Matrix.charpoly_natDegree_eq_dim]
  have hroot : Polynomial.aeval τ P = 0 := by
    apply Algebra.leftMulMatrix_injective (bas A hG)
    rw [map_zero, ← Polynomial.aeval_algHom_apply, leftMul_tau A hG]
    exact Matrix.aeval_self_charpoly _
  have hsmall : ∀ Q : Polynomial F, Q.natDegree < r → Polynomial.aeval τ Q = 0 → Q = 0 := by
    intro Q hQ h0
    rw [Polynomial.aeval_eq_sum_range' hQ] at h0
    rw [← Fin.sum_univ_eq_sum_range (fun i => Q.coeff i • τ ^ i) r] at h0
    have := Fintype.linearIndependent_iff.mp hG.1 (fun i => Q.coeff i) h0
    ext n
    by_cases hn : n < r
    · simpa using this ⟨n, hn⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  rw [PerfectField.separable_iff_squarefree]
  intro q hq
  obtain ⟨s, hs⟩ := hq
  by_contra hqu
  have hP0 : P ≠ 0 := hmon.ne_zero
  have hq0 : q ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact hP0 hs
  have hqdeg : 0 < q.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_ne_zero_of_nonunit hq0 hqu)
  have hQ0 : q * s ≠ 0 := mul_ne_zero hq0 hs0
  have hdegQ : (q * s).natDegree < r := by
    have : P.natDegree = q.natDegree + (q * s).natDegree := by
      rw [hs, mul_assoc, Polynomial.natDegree_mul hq0 hQ0]
    omega
  apply hQ0
  apply hsmall _ hdegQ
  have hnil : IsNilpotent (Polynomial.aeval τ (q * s)) := ⟨2, by
    rw [pow_two, ← map_mul]
    have : q * s * (q * s) = P * s := by rw [hs]; ring
    rw [this, map_mul, hroot, zero_mul]⟩
  exact hnil.eq_zero

end GlobalTheory.JR.LinDesc
