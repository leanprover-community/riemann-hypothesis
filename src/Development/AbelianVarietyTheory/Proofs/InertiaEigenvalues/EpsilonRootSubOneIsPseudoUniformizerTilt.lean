module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology



noncomputable section

namespace GlobalTheory.WeakClosed.TiltUnif

theorem εroot_sub_pow' {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (j : ℕ) :
    (AI.εroot j - 1) ^ l ^ j = AI.ε - 1 := by
  have h : AI.εroot j ^ l ^ j = AI.ε := by
    induction j with
    | zero => simp [LocAinf.εroot]
    | succ j ih =>
      rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
      exact ih
  rw [sub_pow_char_pow, h, one_pow]

theorem coeff_pow_pow' {l : ℕ} [Fact l.Prime] (x : OCb l) (k : ℕ) :
    PreTilt.coeff k (x ^ l ^ k) = PreTilt.coeff 0 x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_mul, map_pow, PreTilt.coeff_pow_p, ih]

theorem eq_zero_of_forall_dvd {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ)
    (b : OCb l) (hb : ∀ m : ℕ, (AI.εroot s - 1) ^ m ∣ b) : b = 0 := by
  have h0 : PreTilt.coeff 0 (AI.ε - 1) = 0 := by
    rw [map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one, sub_self]
  refine Perfection.ext fun k => ?_
  obtain ⟨c, hc⟩ := hb (l ^ s * l ^ k)
  change PreTilt.coeff k b = PreTilt.coeff k 0
  rw [hc, map_mul, pow_mul, εroot_sub_pow', coeff_pow_pow', h0, zero_mul, map_zero]

theorem main {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    ¬ IsUnit (AI.εroot s - 1) ∧ ∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ (AI.εroot s - 1) ^ m := by
  refine ⟨fun h => ?_, fun a ha => ?_⟩
  · have h1 := (h.pow (l ^ s)).map (PreTilt.coeff 0)
    rw [εroot_sub_pow', map_sub, AI.ε_coeff, AI.ζ_zero, map_one, map_one, sub_self] at h1
    haveI : Nontrivial (ModP (OC l) l) := CharP.nontrivial_of_char_ne_one (Fact.out : l.Prime).ne_one
    exact not_isUnit_zero h1
  · by_contra h
    exact ha (eq_zero_of_forall_dvd AI s a fun m =>
      (ValuationRing.dvd_total _ _).resolve_right fun h' => h ⟨m, h'⟩)

end GlobalTheory.WeakClosed.TiltUnif
