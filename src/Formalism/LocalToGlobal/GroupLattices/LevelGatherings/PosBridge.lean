module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
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

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField Formalism.MainNotions.G Formalism.FrobeniusOrbits

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cc_sq (e : Formalism.HC.Frame) : e.cc * e.cc = 1 := by
  simp [Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0, Prod.ext_iff]

theorem cc_pow (e : Formalism.HC.Frame) (s : ℕ) : e.cc ^ s = if s % 2 = 1 then e.cc else 1 := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [if_neg (by omega), one_mul, if_pos (by omega)]
    · rw [if_pos h, cc_sq, if_neg (by omega)]

theorem embLL_mem_alg (D : D7) (z : D.what₂.LL) : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic z).algHom D.what₂.embLL.toRatAlgHom

theorem emb_conj_pow (D : D7) (g : D.R.GG) (s : ℕ) (x : D.host.E) :
    D.host.emb (g * D.R.cc ^ s) x = D.host.emb g (if s % 2 = 1 then D.host.conj x else x) := by
  rw [emb_mul, cc_pow]
  split_ifs
  · rfl
  · simp [Formalism.BasicNotions.Host.sigmaOf]

end Formalism.L2.G
