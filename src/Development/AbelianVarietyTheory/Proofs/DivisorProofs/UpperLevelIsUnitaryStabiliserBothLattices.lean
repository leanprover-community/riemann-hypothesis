module

public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigStatementPfA

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.UpperStab

theorem upper_isUStab (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C]
    (M : TwoLevels E r U C) (c : C) :
    ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  rintro β ⟨u, hu, γ, hγ, rfl⟩
  have hs := (M.comp c).Γ_stab γ hγ
  have hh : ∀ x y, herm (M.comp c).Gm (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
      (Matrix.mulVec ((γ * M.tr u c : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) y) = herm (M.comp c).Gm x y := by
    intro x y
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs.1, M.comp_Gm c, M.tr_herm]
  refine ⟨⟨hh, fun v => ?_⟩, ⟨hh, fun v => ?_⟩⟩
  · have h1 := M.tr_L' u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact M.Γ_L' c γ hγ _
  · have h1 := M.tr_Λ u c v
    rw [hu] at h1
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, h1]
    exact hs.2 _

end GlobalTheory.UpperStab
