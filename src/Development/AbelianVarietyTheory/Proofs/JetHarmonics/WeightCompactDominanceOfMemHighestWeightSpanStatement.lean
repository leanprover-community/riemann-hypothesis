module

public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.RealPlaceAnalysis.StatementKT
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpan
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.weight_compactDominance_of_mem_highestWeightSpan : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (E : Fin k → Fin k → Module.End ℂ W) (Λ μ : Fin k → ℝ) (x v : W), Formalism.REAL.GlRel E → Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E → Formalism.REAL.KHighest (PI.UpqRep.allPos k) E Λ x → v ∈ Formalism.REAL.kSpan (PI.UpqRep.allPos k) E x → v ≠ 0 → Formalism.REAL.IsWeight E μ v → PI.UpqRep.CDom (PI.UpqRep.allPos k) μ Λ := by
  first | exact @GlobalTheory.weight_cdom_of_mem_kSpan | exact GlobalTheory.weight_cdom_of_mem_kSpan | (intros; apply GlobalTheory.weight_cdom_of_mem_kSpan <;> assumption)
