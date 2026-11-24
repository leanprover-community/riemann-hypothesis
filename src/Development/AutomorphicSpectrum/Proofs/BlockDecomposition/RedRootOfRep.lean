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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeMap

theorem redRoot_of_rep : CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.RepOp → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RedRoot := by
  intro hRoot hOp hConc inOp inRed Q q _ _ hq i X ζ ξ hξ
  have h1 : Rep (rootClass i ζ) (resGen i ζ) := (hRoot Q i X ζ).2
  have h2 : Rep (rootClass i ξ) (resGen i ξ) := (hRoot q i X ξ).2
  have h3 := hOp inOp _ _ _ _ (redMap Q q i) X 0 (rootClass i ζ) _ h1
  rw [inRed Q q hq i X ζ ξ hξ] at h3
  exact (hConc (ZMod q) _ X 0 (resGen i ξ)).2.2 _ _ h3 h2

end GlobalTheory.CompanionTheory.EdgeMap
