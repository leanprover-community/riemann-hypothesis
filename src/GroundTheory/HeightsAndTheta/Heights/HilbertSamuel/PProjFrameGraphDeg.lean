module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibrePt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameFibreDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraphDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
public import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameGraphDeg.proof
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hPt : ProjFrameFibrePt.Statement) (hDeg : ProjFrameFibreDeg.Statement) : ProjFrameGraphDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF
  have : (coordIdeal ℤ x).IsPrime := hP.2.1.1
  have := ProjFrameGraph.graphIdeal_isPrime (ι₂ := GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x)
    (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
  let G := Inter.genFibreOf (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
    (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e)))
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr)
  have hch := ProjFrameGraph.isChart_fibreChart G (e 0).2 (ProjFrameGraph.frame_ne_zero hF 0)
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ (hPt D Ω κ x e hP hF G) hch, hDeg D Ω κ x e hP hF G _ hch]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
