module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsBilinear
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegrePartition
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChart
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre)

theorem StokesStatement.of_found (hBil : PtsBilinear.Statement) (hPart : SegrePartition.Statement)
    (hChart : SegreChart.Statement) (hSV : StokesOnVariety.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by
  classical
  intro K _ ι _ P n L B B' hP hL hB hB' hB0 hB'0
  have hw := isDegZeroSmooth_log hB hB0
  have hw' := isDegZeroSmooth_log hB' hB'0
  have hne : ∀ k, Nonempty (ι k) := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    exact ⟨i⟩
  obtain ⟨δ, hδ, ρ, hρs, hρ1, hρ0⟩ := hPart K ι hne

  have hpiece : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρs i).mul hw

  have key : ∀ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
        (fun z => ρ i z * Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
        (fun z => Real.log (B'.h z)) := by
    intro i
    obtain ⟨m, Js, U, V, Φ, hJ, hU, h1, h2⟩ := hChart K ι P n L (fun z => ρ i z * Real.log (B.h z))
      (fun z => Real.log (B'.h z)) i δ hP hL (hpiece i) hw' hδ
      (fun z hz => by simp only [hρ0 i z hz, zero_mul])
    rw [h1, h2]
    refine Finset.sum_congr rfl fun J hJs => ?_
    obtain ⟨hJp, hJd, hUs, hVs, hΦs⟩ := hJ J hJs
    exact hSV m n J U V Φ hJp hJd hUs hVs hΦs (Or.inl hU)
  have hsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) := by
    funext z
    rw [← Finset.sum_mul, hρ1 z, one_mul]
  obtain ⟨hA, hC⟩ := hBil K ι P n L _ (fun i z => ρ i z * Real.log (B.h z))
    (fun z => Real.log (B'.h z)) hP hL hpiece hw'
  calc ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (fun z => Real.log (B.h z))
      = ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ∑ i, ρ i z * Real.log (B.h z)) := by rw [← hsum]
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L))
          (fun z => ρ i z * Real.log (B.h z)) := hA
    _ = ∑ i, ptsIntegral P (Fin.cons (fun z => ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := Finset.sum_congr rfl fun i _ => key i
    _ = ptsIntegral P (Fin.cons (fun z => ∑ i, ρ i z * Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := hC.symm
    _ = ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L))
          (fun z => Real.log (B'.h z)) := by rw [← hsum]

end GroundTheory.Heights₂.Heights
