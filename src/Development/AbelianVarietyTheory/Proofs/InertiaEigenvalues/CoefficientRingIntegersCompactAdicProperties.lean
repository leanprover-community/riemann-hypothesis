module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralOfBounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.NumberTheory.Padics.RingHoms
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
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.GoodCoeff

section Open

variable {l : ℕ} [Fact l.Prime] {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
  [IsModuleTopology ℚ_[l] LL]

theorem continuous_algebraMap_padic : Continuous (algebraMap ℚ_[l] LL) := by
  haveI := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  have h : (algebraMap ℚ_[l] LL : ℚ_[l] → LL) = fun c => c • (1 : LL) :=
    funext Algebra.algebraMap_eq_smul_one
  rw [h]
  exact continuous_id.smul continuous_const

theorem padicInt_mem (A : Subring LL) (hA : IsOpen (A : Set LL)) (u : ℤ_[l]) :
    algebraMap ℚ_[l] LL (u : ℚ_[l]) ∈ A := by
  have hU : IsOpen ((algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL)) :=
    hA.preimage continuous_algebraMap_padic
  have h0 : (0 : ℚ_[l]) ∈ (algebraMap ℚ_[l] LL) ⁻¹' (A : Set LL) := by
    simp [A.zero_mem]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (Padic.norm_p_lt_one (p := l))
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : (u : ℚ_[l]) = ((u.appr n : ℕ) : ℚ_[l]) + (w : ℚ_[l]) * (l : ℚ_[l]) ^ n := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hw
    push_cast at this
    linear_combination -this
  have h1 : algebraMap ℚ_[l] LL ((w : ℚ_[l]) * (l : ℚ_[l]) ^ n) ∈ A := by
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
    calc ‖(w : ℚ_[l])‖ * ‖(l : ℚ_[l])‖ ^ n ≤ 1 * ‖(l : ℚ_[l])‖ ^ n :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one w) (by positivity)
      _ < ε := by rwa [one_mul]
  rw [hu, map_add (f := _), map_natCast]
  exact A.add_mem (natCast_mem A _) h1

end Open

theorem good_coeff_integers : ∀ (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → (∀ x : LL, x ∈ Set.range (algebraMap O LL) ↔ RingHom.IsIntegralElem ((algebraMap ℚ_[l] LL).comp (algebraMap ℤ_[l] ℚ_[l])) x) ∧ IsCompact (Set.range (algebraMap O LL)) ∧ (∀ n : ℕ, Finite (O ⧸ Ideal.span {((l : ℕ) : O) ^ n})) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : O)}) O := by
  first
  | exact @_root_.GlobalTheory.PowerImageOpen.main
  | exact _root_.GlobalTheory.PowerImageOpen.main
  | (apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerImageOpen.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerImageOpen.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerImageOpen.main ..)

end GlobalTheory.GoodCoeff
