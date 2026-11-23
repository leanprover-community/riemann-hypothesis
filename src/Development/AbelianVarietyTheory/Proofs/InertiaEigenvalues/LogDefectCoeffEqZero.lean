module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
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
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.LogU

namespace GlobalTheory.LogU

open MvPolynomial

theorem logDefect_coeff_eq_zero : ∀ (n i j : ℕ), i + j < n →
    AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  intro n i j hij
  let J : Ideal (MvPolynomial (Fin 2) ℚ) := MvPolynomial.idealOfVars (Fin 2) ℚ
  let q : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ ⧸ J ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin 2) ℚ ⧸ J ^ n) := fun m hm => by
    have hu : IsUnit ((m : ℚ)) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hu.map (q.comp MvPolynomial.C)
  have hI : (J.map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]; exact Ideal.map_quotient_self _
  have hXJ : ∀ k, (X k : MvPolynomial (Fin 2) ℚ) ∈ J := fun k =>
    Ideal.subset_span (Set.mem_range_self k)
  have key := GlobalTheory.MemLoc.LogAdd.trunc_add hR n _ hI (q (X 0)) (q (X 1))
    (Ideal.mem_map_of_mem q (hXJ 0)) (Ideal.mem_map_of_mem q (hXJ 1))
  have h0 : MvPolynomial.aeval ![q (X 0), q (X 1)] (logDefect n) = 0 := by
    refine (aeval_logDefect n (q (X 0)) (q (X 1))).trans ?_
    simp only [truncLogF]; rw [key]; ring
  have hcomp : q.comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.aeval (R := ℤ) ![q (X 0), q (X 1)]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro k; fin_cases k <;> simp
  have hφ : q (MvPolynomial.map (Int.castRingHom ℚ) (logDefect n)) = 0 := by
    have := RingHom.congr_fun hcomp (logDefect n)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, h0]
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff'] at hφ
  have hd : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree < n := by
    first
      | simpa [Finsupp.degree_single] using hij
      | simpa [Finsupp.degree, Finsupp.support_single_ne_zero] using hij
  have := hφ _ hd
  rw [MvPolynomial.coeff_map] at this
  simpa using this

end GlobalTheory.LogU
