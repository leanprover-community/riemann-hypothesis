module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.TiedMu

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem zeta_pow (AI : LocAinf l P) (k n : ℕ) : AI.ζ (n + k) ^ l ^ n = AI.ζ k := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, Nat.add_right_comm, AI.ζ_succ, ih]

theorem untilt_eps (AI : LocAinf l P) : AI.ε.untilt = 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
  have h := zeta_pow AI 0 n
  rw [add_zero, AI.ζ_zero] at h
  rw [h]

theorem locAinf_untilt_epsOne_eq_zeta (AI : LocAinf l P) : AI.ε1.untilt = AI.ζ 1 := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
  refine ⟨AI.ζ (n + 1), ?_, ?_⟩
  · refine (AI.ε_coeff (n + 1)).symm.trans ?_
    have h : AI.ε = AI.ε1 ^ l := by rw [LocAinf.ε1, frobeniusEquiv_symm_pow_p]
    rw [h]
    exact Perfection.coeff_pow_p _ _
  · rw [zeta_pow AI 1 n]

theorem eps_ne_one (AI : LocAinf l P) : AI.ε ≠ 1 := by
  intro h
  apply AI.ζ_one
  rw [← locAinf_untilt_epsOne_eq_zeta, LocAinf.ε1, h, map_one, map_one]

theorem eps_pow_ne_one (AI : LocAinf l P) (j : ℕ) : AI.ε ^ l ^ j ≠ 1 := by
  induction j with
  | zero => simpa using eps_ne_one AI
  | succ j ih =>
    intro h
    apply ih
    apply (frobeniusEquiv (OCb l) l).injective
    rw [frobeniusEquiv_apply, frobeniusEquiv_apply, frobenius_def, frobenius_def, ← pow_mul,
      ← pow_succ, h, one_pow]

theorem eps_root_pow (AI : LocAinf l P) (s : ℕ) : AI.εroot s ^ l ^ s = AI.ε := by
  induction s with
  | zero => simp [LocAinf.εroot]
  | succ s ih =>
    rw [LocAinf.εroot, Function.iterate_succ_apply', pow_succ', pow_mul, frobeniusEquiv_symm_pow_p]
    exact ih

theorem isUnit_aB (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    IsUnit (Per.aB l (Per.tm e - 1)) :=
  GlobalTheory.CrisLoc.unit_of_root_aB l e he hne

theorem isUnit_of_aB {AI : LocAinf l P} (T : LocTied l P AI) (a : Ainf l) (h : IsUnit (Per.aB l a)) :
    IsUnit (AI.ιA a) := by
  rw [← T.ιA] at h
  have h' := h.map T.eB.symm
  rwa [RingEquiv.symm_apply_apply] at h'

theorem tied_mu_units : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ s : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) ∧ (∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1))) ∧ IsUnit (AI.ιA AI.ξ) ∧ ∀ z : ℤ_[l], AI.ιA (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℚ_[l] P.R.B (z : ℚ_[l]) := by
  intro l _ P AI T
  have hj : ∀ j : ℕ, IsUnit (AI.ιA (WittVector.teichmuller l (AI.ε ^ l ^ j) - 1)) := fun j =>
    isUnit_of_aB T _ (isUnit_aB (AI.ε ^ l ^ j)
      (by rw [map_pow, untilt_eps, one_pow]) (eps_pow_ne_one AI j))
  have hμ : IsUnit (AI.ιA AI.μ) := by simpa [LocAinf.μ] using hj 0
  refine ⟨fun s => ?_, hj, ?_, fun z => ?_⟩
  · have h := geom_sum_mul (WittVector.teichmuller l (AI.εroot s)) (l ^ s)
    rw [← map_pow, eps_root_pow] at h
    rw [LocAinf.μ, ← h, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · rw [AI.μ_eq, map_mul] at hμ
    exact isUnit_of_mul_isUnit_right hμ
  · apply T.eB.injective
    rw [T.ιA, T.zB]
    exact GlobalTheory.RingIface.aB_algebraMap_padicInt l z

end GlobalTheory.TiedMu
