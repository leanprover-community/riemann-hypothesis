module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopSubLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopBasisChange
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualTopStacked
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedDegree
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField

noncomputable section

theorem DualTopSubLattice.proof (hBasis : DualTopBasisChange.Statement)
    (hStacked : DualTopStacked.Statement) (hDeg : DualStackedDegree.Statement) :
    DualTopSubLattice.Statement := by
  intro K _ _ i F F' T T' _ _ _ _ b hb b' hb' II hi hII hle
  have hcard : Fintype.card T = Fintype.card T' := by
    rw [DualTopStackedExistence.card_eq_of_bijective b hb, DualTopStackedExistence.card_eq_of_bijective b' hb']
  obtain ⟨b₁, b₁', a, hab⟩ := DualTopStackedExistence.exists_stacked hle b b' hcard
  have hb₁ := DualEmbBijective.proof K i F T' b₁
  have hb₁' := DualEmbBijective.proof K i F' T' b₁'

  have h1 : II Unit (dualBlocks T') (dualIdeal b') i (fun _ => dualLine F'.withStdMetric b' hb') =
      II Unit (dualBlocks T') (dualIdeal b₁') i (fun _ => dualLine F'.withStdMetric b₁' hb₁') :=
    hBasis K i F'.withStdMetric T' T' b₁' hb₁' b' hb' II hi hII
  have h2 : II Unit (dualBlocks T') (dualIdeal b₁) i (fun _ => dualLine F.withStdMetric b₁ hb₁) =
      II Unit (dualBlocks T) (dualIdeal b) i (fun _ => dualLine F.withStdMetric b hb) :=
    hBasis K i F.withStdMetric T T' b hb b₁ hb₁ II hi hII

  have h3 := hStacked K i F F' T' b₁ hb₁ b₁' hb₁' a II hi hII hle hab
  have h4 := hDeg K i F F' T' b₁ b₁' a hle hab
  rw [h1, h3, h2, h4]

end

end GroundTheory.Heights₂.Heights
