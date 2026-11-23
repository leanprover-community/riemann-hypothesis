module

public import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open PowerSeries

universe u

namespace Formalism.LT.LTL

open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP

section Near

variable {K : Type u} [NormedField K] {ι : Type*}

def Near (k : ℕ) (A B : MvPowerSeries ι K) : Prop := Low k A ∧ Low k B ∧ Low (k + 1) (A - B)

end Near

section Master

variable {K : Type u} [NormedField K] {ι : Type*}

end Master

section Cong

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

lemma norm_finsum_le' {α : Type*} {g : α → K} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ n, ‖g n‖ ≤ C) :
    ‖∑ᶠ n, g n‖ ≤ C := by
  classical
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum g hfin]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hC (fun i _ => hg i)
  · rw [finsum_of_infinite_support hfin]
    simpa using hC

def Cong (c : K) (A B : MvPowerSeries ι K) : Prop :=
  IntegralMv A ∧ IntegralMv B ∧ DivByMv c (A - B)

end Cong

section FrobPi

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

end FrobPi

section Defect

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

end Defect

section Constr

variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type*}

variable [Fintype ι] [DecidableEq ι]

variable {p q : ℕ} {π : K} {e e' : PowerSeries K} {a : ι → K}

end Constr

end Formalism.LT.LTL

namespace Formalism.LT

open Formalism.G Formalism.LT.LTL

end Formalism.LT
