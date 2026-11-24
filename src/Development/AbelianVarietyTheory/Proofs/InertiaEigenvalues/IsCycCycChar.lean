module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

noncomputable def cycChar (l : ℕ) [Fact l.Prime] : GQ l →* ℚ_[l]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom).comp
    ((cyclotomicCharacter (Om l) l).comp (MulSemiringAction.toRingAut (GQ l) (Om l)))

theorem _root_.GlobalTheory.Cyc.isCyc_cycChar (l : ℕ) [Fact l.Prime] :
    _root_.GlobalTheory.Cyc.IsCyc (_root_.GlobalTheory.Cyc.cycChar l) := by
  intro g m ζ h
  set x : ℤ_[l] := (cyclotomicCharacter (_root_.Formalism.BasicNotions.Loc.Om l) l (MulSemiringAction.toRingAut _ _ g) : ℤ_[l])
    with hx
  refine ⟨(PadicInt.toZModPow m x).val, ?_, ?_⟩
  · have hmem : x - ((PadicInt.toZModPow m x).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ m} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
        sub_self]
    have h2 : ‖((x - ((PadicInt.toZModPow m x).val : ℤ_[l]) : ℤ_[l]) : ℚ_[l])‖ ≤
        (l : ℝ) ^ (-(m : ℤ)) :=
      (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hmem
    have h3 : ((_root_.GlobalTheory.Cyc.cycChar l g : ℚ_[l]ˣ) : ℚ_[l]) = (x : ℚ_[l]) := rfl
    rw [h3]
    rw [PadicInt.coe_sub, PadicInt.coe_natCast] at h2
    exact h2
  · exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut _ _ g) ζ h

theorem _root_.GlobalTheory.Cyc.exists_isCyc :
    ∀ (l : ℕ) [Fact l.Prime], ∃ χ : _root_.Formalism.BasicNotions.Loc.GQ l →* ℚ_[l]ˣ, _root_.GlobalTheory.Cyc.IsCyc χ :=
  fun l _ => ⟨_root_.GlobalTheory.Cyc.cycChar l, _root_.GlobalTheory.Cyc.isCyc_cycChar l⟩

end GlobalTheory.Cyc
