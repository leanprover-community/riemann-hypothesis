module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineIndex
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
public import Mathlib.GroupTheory.FiniteAbelian.Basic
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

theorem UpperTheory.Reformulated.B.Gub1.proof.{u_1, u_2} :
    ∀ (E : Type u_1) (W : Type u_2) [inst : Field E] [inst_1 : NumberField E] [inst_2 : AddCommGroup W]
      [inst_3 : _root_.Module E W], GroundTheory.Heights₂.Heights.FiniteCovolume.LineIndexNeZero.Statement E W := by
  intro E W _ _ _ _ La x hL _ _
  have hfg : (La ⊓ (Submodule.span E {x}).toAddSubgroup).FG :=
    (Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule _)).1
      (((Submodule.fg_iff_addSubgroup_fg (AddSubgroup.toIntSubmodule La)).2 hL.fg).of_le
        (AddSubgroup.toIntSubmodule.monotone inf_le_left))
  have := (AddGroup.fg_iff_addSubgroup_fg _).2 hfg
  refine @AddSubgroup.index_ne_zero_of_finite _ _ _ (AddCommGroup.finite_of_fg_isAddTorsion _ ?_)
  rintro ⟨y, hy', hy⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨n, hn, hc⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
    (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine isOfFinAddOrder_iff_zsmul_eq_zero.2 ⟨n, hn, (QuotientAddGroup.eq_zero_iff (n • _)).2 ?_⟩
  exact ⟨⟨n • c, hc⟩, smul_assoc n c x⟩
