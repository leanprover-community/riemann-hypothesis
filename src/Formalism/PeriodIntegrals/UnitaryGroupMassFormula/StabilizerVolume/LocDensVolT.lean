module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolT
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

theorem eq_one_of_pow (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, 1 / 2 < (z ^ (2 ^ k)).re) : z = 1 := by
  apply PI.VolStabSW.VolAAW.eq_one_of_pow <;> assumption

variable {F : Type} [Field F] [NumberField F]

theorem psiV_nsmul (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : Fv F v) :
    psiV F ψ v (n • y) = psiV F ψ v y ^ n := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero, psiV]
    have : pairA F 0 (singleV F v 0) = 0 := by
      have h := singleV_add (F := F) v 0 0
      rw [add_zero] at h
      have h0 : singleV F v 0 = 0 := by
        have := congrArg (fun x => x - singleV F v 0) h
        exact (by simpa using this : (0 : Af F) = singleV F v 0).symm
      rw [h0]
      rfl
    rw [this, AddChar.map_zero_eq_one]
  | succ n ih => rw [succ_nsmul, psiV_add, ih, pow_succ]

theorem ev_triv (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∀ᶠ v in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v y = 1 := by
  apply PI.VolStabSW.VolAAW.ev_triv <;> assumption

def CondExact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F

theorem condAA_of (hE : CondExact) : CondAA := by
  intro F _ _ ψ hψ
  filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2
  intro t
  refine ⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩

end VolAAW

end PI.VolStabS
