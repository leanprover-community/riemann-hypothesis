module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionToProjectiveBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockMetricChange
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageTop
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockImageGenDeg
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem ReductionToProjectiveBlock.proof (hRP : ReductionToProjective.Statement)
    (hMC : BlockMetricChange.Statement) (hIm : BlockImageDatum.Statement) (hTop : BlockImageTop.Statement)
    (hGD : BlockImageGenDeg.Statement) : ReductionToProjectiveBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  obtain ⟨d₀, r, M, N, d', hy, hk, hB, hmet, hchi⟩ := hIm D K ι Ω d

  have h1 := hMC D K ι Ω I d d₀ hI hy hk

  have h2 := (hRP D Ω (Fin r) I d' hI).2

  have hdeg : d₀.A.a = unitDeg d.k₀ := hk ▸ d₀.deg
  have htop : I K ι (mCoordIdeal d₀.y) (D + 1) (fun _ => d₀.A) = top I d'.x d'.m D := by
    rw [hy]
    exact hTop D K ι Ω (Fin r) I d.y d.k₀ d₀.A M N d'.x d'.m hI d.arith d.birat d'.arith hB hdeg
      d₀.semipos.1 d'.smooth hmet

  have hg : genDeg (ι := GlobalTheory (Fin r)) (coordIdeal ℤ d'.x) D 1 = genDeg (mCoordIdeal d.y) D d.A.a := by
    rw [d.deg]
    exact hGD D K ι Ω (Fin r) d.y d.k₀ M N d'.x d.arith d.birat hB
  rw [hg] at h2
  refine (h2.sub h1).congr_left fun n => ?_
  simp only [hsDefect, hchi n, htop]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
