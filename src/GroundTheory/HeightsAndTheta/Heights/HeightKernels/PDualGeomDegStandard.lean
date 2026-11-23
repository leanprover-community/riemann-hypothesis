module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ScaledExample
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualGeomDegCharts
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassGeomDegChart
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

theorem DualGeomDegStandard.proof (hD : DualGeomDegCharts.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualGeomDegStandard.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  have hterm : ∀ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ) =
      chartMass (1 : Matrix (Fin (i - 1 + 1)) (Fin (i - 1 + 1)) ℂ) := fun σ =>
    hM _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
  rw [e1, hE, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_const, Finset.card_univ,
    Embeddings.card K ℂ, nsmul_eq_mul]

end GroundTheory.Heights₂.Heights
