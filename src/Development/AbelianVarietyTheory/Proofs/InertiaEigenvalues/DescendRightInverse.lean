module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow
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
import Mathlib.Geometry.Euclidean.Volume.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem GlobalTheory.BKLim.descend_rightInverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (M : ℕ), ∃ r : ℕ, ∀ (d d' n : ℕ) (R : Matrix (Fin d) (Fin d') (bk.S)) (a : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, (l : Ainf l) ^ n ∣ (R.map bk.ev * a - τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j) → ∃ G : Matrix (Fin d') (Fin d) (bk.S), (∀ i j, (l : bk.S) ^ n ∣ (R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) := by
  intro l _ K bk τ hτ M
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.BSP.pow_l_mem_span_coeff l K bk τ hτ ι TB M
  obtain ⟨t, ht⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  refine ⟨r, fun d d' n R a h => ?_⟩
  refine ⟨∑ k ∈ t.support, t k • (a.map (TB.c k)), fun i j => ?_⟩
  have hl : ∀ k (y : Ainf l), TB.c k ((l : Ainf l) ^ n * y) = (l : bk.S) ^ n * TB.c k y := by
    intro k y
    have e : (l : Ainf l) ^ n = bk.ev ((l : bk.S) ^ n) := by rw [map_pow, map_natCast]
    rw [e, TB.c_mul]
  obtain ⟨y, hy⟩ := h i j
  rw [Matrix.sub_apply] at hy
  have hy' := sub_eq_iff_eq_add.1 hy
  have hG : (R * ∑ k ∈ t.support, t k • (a.map (TB.c k))) i j = ∑ k ∈ t.support, t k * TB.c k ((R.map bk.ev * a) i j) := by

    simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Finset.mul_sum, map_sum, TB.c_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [Matrix.sub_apply, hG, hy']
  simp only [map_add (f := _), hl, mul_add, Finset.sum_add_distrib]
  refine ⟨∑ k ∈ t.support, t k * TB.c k y, ?_⟩
  rw [← ht]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Finsupp.sum, Finset.mul_sum]
    rw [add_sub_cancel_right]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, map_zero, mul_zero, Finset.sum_const_zero,
      add_zero, sub_zero, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
