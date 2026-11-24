module

public import Formalism.FormalGroupWitt.SubstInjectiveV
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
import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.FG

open Formalism.G

namespace PadicFrobeniusSquare

theorem padicInt_norm_le_p {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) (hy : PadicInt.toZMod y = 0) :
    ‖y‖ ≤ ‖(p : ℤ_[p])‖ := by
  have h1 : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := hy
  rw [PadicInt.ker_toZMod] at h1
  have h2 : ‖y‖ < 1 := PadicInt.mem_nonunits.1 ((IsLocalRing.mem_maximalIdeal _).1 h1)
  obtain ⟨z, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h2
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)

end PadicFrobeniusSquare

theorem frobenius_lift_padic_square : Formalism.FG.FrobLiftPadicSq := by
  intro l _
  refine ⟨Fact.out, ⟨2, two_pos, rfl⟩, Padic.norm_p_lt_one, ?_⟩
  intro a ha
  have hz : ∀ z : ZMod l, z ^ l ^ 2 = z := fun z => by
    rw [pow_two, pow_mul, ZMod.pow_card, ZMod.pow_card]
  let y : ℤ_[l] := ⟨a, ha⟩
  have h := PadicFrobeniusSquare.padicInt_norm_le_p (y - y ^ l ^ 2) (by rw [map_sub, map_pow, hz, sub_self])
  rw [PadicInt.norm_def, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_natCast] at h
  show ‖a - a ^ l ^ 2‖ ≤ ‖(l : ℚ_[l])‖
  exact h

end Formalism.FG
