module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

noncomputable section

namespace GlobalTheory.Mem.NrmCompl

open NumberField IsDedekindDomain

variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

def nrmAbs : AbsoluteValue (P.adicCompletion L) ℝ := NormedField.toAbsoluteValue (P.adicCompletion L)

theorem nrmAbs_eq_toNNReal (x : P.adicCompletion L) :
    nrmAbs P x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero P) (Valued.v x) :=
  FinitePlace.norm_def (v := P) x

theorem nrmAbs_eq_zpow {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by
  have hv : Valued.v x ≠ 0 := by simpa using hx
  rw [nrmAbs_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hv]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨_, (WithZero.exp_log hv).symm⟩
  simp only [hn, WithZero.log_exp]
  push_cast
  rfl

theorem nrmAbs_of_valuation_eq_exp {x : P.adicCompletion L} {n : ℤ} (h : Valued.v x = WithZero.exp n) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ n := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  rw [nrmAbs_eq_zpow P hx, h, WithZero.log_exp]

theorem nrmAbs_eq_one_iff (x : P.adicCompletion L) : nrmAbs P x = 1 ↔ Valued.v x = 1 := by
  rw [nrmAbs_eq_toNNReal, ← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal P).ne'

end GlobalTheory.Mem.NrmCompl
