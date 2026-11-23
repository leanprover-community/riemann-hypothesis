module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueFibreDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocResidueAdjoin
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocResidueDeg
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
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

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem SemilocResidueDeg.proof (hDim : SemilocResidueFibreDim.Statement) (hAdj : SemilocResidueAdjoin.Statement) :
    SemilocResidueDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W hv hP' hZ hs hsP hW W' hW' _ G' J' hJ
  have hrel : ∀ k', ∃ i, (X ⟨k', i⟩ : MRing ι') ∉ W' := hW'.1.2.2
  choose i' hi' using hrel
  have hfib : IsProjVarF (fibreIdeal κ G') 0 := hDim K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G'
  have hz : ∀ k : FibreBlock κ, G'.x' ⟨k.1, i' k.1⟩ ≠ 0 := by
    intro k h0
    apply hi' k.1
    rw [← G'.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
    exact h0
  have hj : IsChart (fibreIdeal κ G') (fun k => i' k.1) := by
    intro k hk
    apply hz k
    rw [fibreIdeal, RingHom.mem_ker, aeval_X] at hk
    exact hk
  refine ⟨_, hAdj K ι K' ι' κ v P' n s α W hv hP' hZ hs hsP hW W' hW' G' i' hi', ?_⟩
  rw [hJ.1 _ Fin.elim0 _ hfib hj]
  exact congrArg _ (ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G'.Φ G'.Φ' (fun q => G'.x' ⟨q.1.1, q.2⟩)
    (fun k => i' k.1) hz hfib.1.2.1).symm

end GroundTheory.Heights₂.Heights.Inter
