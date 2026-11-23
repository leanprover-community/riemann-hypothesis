module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRep

theorem repOp : CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp := by
  intro _ hConc hBasic hOp S R _ _ I J ρ X n x a hRep
  obtain ⟨α, hα, hmk⟩ := (hConc S I X n a).2.1 x hRep
  have hcl : Sec.map (J.d n (n + 1)) (ρ.app X n a) = 0 := by
    rw [ρ.comm X n (n + 1) a, (hBasic S I X n).2.1 x a hRep (n + 1), map_zero]
  obtain ⟨β, hβ⟩ := (hConc R J X n (ρ.app X n a)).1 hcl
  have himg : ρ.IsImage α.1 β.1 := by
    intro p s h U y
    cases p with
    | zero =>
      have hs : n = s := by omega
      subst hs
      rw [hβ.1 U y, hα.1 U y]
      exact ρ.nat y n a
    | succ p =>
      rw [hβ.2 p s h U y, hα.2 p s h U y, map_zero]
  refine ⟨β, ?_, ?_⟩
  · rw [← hOp S R I J ρ (sch.obj X) n α β himg, hmk]
  · rw [hβ.1 X (𝟙 X)]
    change ((J.X n).obj.map (𝟙 (op X))).hom (ρ.app X n a) = ρ.app X n a
    rw [CategoryTheory.Functor.map_id]
    rfl

end GlobalTheory.CompanionTheory.EdgeRep
