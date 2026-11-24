module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem GrassHeightBound.proof (hArith : GrassArithVar.Statement) (hRoot : RootArithVar.Statement)
    (hSemi : FsLineSemipositive.Statement) (hNef : NefOfNonneg.Statement)
    (hConj : FsConjInvariant.Statement) (hLe : GrassLeRoot.Statement) (hHt : RootHeight.Statement)
    (hDense : RootDense.Statement) : GrassHeightBound.Statement := by
  intro hZ2 f j m hf II hII
  refine hZ2 (Fin f) (plBlocks f j m) (grassIdeal f j m) ⊥ (f * j * m) (fsMulti (plBlocks f j m))
    (grassConst f j m) (rootFamily f j m) II hII (hArith f j m hf) bot_le (hSemi _ _ _)
    (hNef _ _ _ _ fun _ => ?_) (hConj _ _) ?_ (hDense f j m)
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · rintro W ⟨ζ, hζ, rfl⟩
    exact ⟨hRoot f j m ζ hf hζ, hLe f j m ζ, hHt f j m ζ hf hζ II hII⟩

end GroundTheory.Heights₂.Heights
