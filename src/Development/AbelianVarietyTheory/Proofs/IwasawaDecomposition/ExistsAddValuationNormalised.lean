module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddValuation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem _root_.GlobalTheory.MemLoc.exists_addValuation_normalised : ∀ (l : ℕ) [Fact l.Prime], ∀ LL : _root_.Formalism.BasicNotions.Loc.FinExt l,
    ∃ v : AddValuation ↥LL.1 (WithTop ℚ), v (l : ↥LL.1) = 1 ∧
      ∀ x : ↥LL.1, 0 ≤ v x ↔ x ∈ _root_.Formalism.BasicNotions.Loc.OL LL := by
  intro l _ LL
  have hprime : l.Prime := Fact.out
  have hnorm : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl0 : 0 < ‖(l : PadicAlgCl l)‖ := by
    rw [hnorm]
    exact inv_pos.2 (Nat.cast_pos.2 hprime.pos)
  have hl1 : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [hnorm]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hprime.one_lt)
  have hL : Real.log ‖(l : PadicAlgCl l)‖ < 0 := Real.log_neg hl0 hl1
  obtain ⟨v, hv⟩ := _root_.GlobalTheory.PadicVal.exists_addValuation (l : PadicAlgCl l) hl0 hl1
  refine ⟨v.comap LL.1.val.toRingHom, ?_, fun x => ?_⟩
  · have hcast : ((l : ↥LL.1) : PadicAlgCl l) = l := by simp
    show v ((l : ↥LL.1) : PadicAlgCl l) = 1
    rw [hcast]
    obtain ⟨q, hvq, hlog⟩ := hv _ (norm_pos_iff.1 hl0)
    have hq : q = 1 := Rat.cast_injective (by
      have := mul_right_cancel₀ hL.ne (hlog.symm.trans (one_mul _).symm)
      simpa using this)
    rw [hvq, hq]
    rfl
  · show 0 ≤ v (x : PadicAlgCl l) ↔ x ∈ integralClosure ℤ_[l] LL.1
    rw [_root_.GlobalTheory.mem_integralClosure_padicInt_iff]
    by_cases hx : (x : PadicAlgCl l) = 0
    · simp [hx]
    obtain ⟨q, hvq, hlog⟩ := hv _ hx
    rw [hvq, WithTop.coe_nonneg, ← Real.log_nonpos_iff (norm_nonneg _), hlog]
    constructor
    · intro h
      exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast h) hL.le
    · intro h
      have h' : (0 : ℝ) ≤ q := (mul_le_mul_right_of_neg hL).1 (by simpa using h)
      exact_mod_cast h'

end GlobalTheory.MemLoc
