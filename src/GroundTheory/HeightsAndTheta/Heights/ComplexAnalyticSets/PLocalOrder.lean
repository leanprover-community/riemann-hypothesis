module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem LocalOrder.proof (hL : SliceLength.Statement) (hS : SliceBranches.Statement)
    (hC : CurveBranchLength.Statement) : LocalOrder.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨U, hUo, hUd, hU⟩ := hL n d J W u hJ hdim hu hW
  obtain ⟨q, _, L, ⟨hrad, hlen⟩, c, hccov, hcdisj, hcord⟩ :=
    hS n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U
      (fun q => {L | IsRadicalAt (sliceIdeal J L q) q ∧
        localMult (J ⊔ Ideal.span {linForm u}) W =
          localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))})
      hUo hUd hU
  rw [hlen]
  exact hC n (sliceIdeal J L q) u q m c ord hrad hccov hcdisj hcord

end GroundTheory.Heights₂.Heights
