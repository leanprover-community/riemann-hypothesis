module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Formalism.LocalToGlobal.IndefiniteReal.DatumF

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.NonarchShell

theorem exists_compact_shell_nsmul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (V : Set (Fin N → v.adicCompletion F)), V ∈ nhds 0 →
      ∃ K : Set (Fin N → v.adicCompletion F), IsCompact K ∧ (0 : Fin N → v.adicCompletion F) ∉ K ∧
        ∀ t, t ∉ V → ∃ n : ℕ, n • t ∈ K := by
  intro F _ _ v N V hV
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : ‖(q : v.adicCompletion F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)
    rwa [map_natCast, map_natCast] at this
  have hqne : (q : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)) q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)
  have hqpos : 0 < ‖(q : v.adicCompletion F)‖ := norm_pos_iff.2 hqne
  have hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖ := by
    intro m t
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  refine ⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [mem_closedBall_zero_iff] using ht.2
  · intro h
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.2 (mul_pos hr hqpos))
  · intro t ht
    have htr : r ≤ ‖t‖ := by
      by_contra hlt
      exact ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))
    have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr htr
    have hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr htpos) hq1
      exact ⟨k, (lt_div_iff₀ htpos).1 hk⟩
    classical
    set k := Nat.find hex with hkdef
    have hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hk
      exact absurd htr (not_le.2 hk)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r :=
      Nat.find_min hex (by omega)
    have hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ := by
      rw [hsm, Nat.cast_pow, norm_pow]
    refine ⟨q ^ k, ?_, ?_⟩
    · show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖
      rw [hnorm, hj, pow_succ]
      have := not_lt.1 hjmin
      nlinarith
    · show ‖(q ^ k) • t‖ ≤ r
      rw [hnorm]; exact hk.le

end GlobalTheory.NonarchShell
