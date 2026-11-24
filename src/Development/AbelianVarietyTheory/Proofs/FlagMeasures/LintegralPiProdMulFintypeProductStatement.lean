module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralPiProdMulFintypeProduct
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lintegral_pi_prod_mul_fintype_product : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  first | exact @GlobalTheory.StabUnfold.lintegral_pi_prod_mul | exact GlobalTheory.StabUnfold.lintegral_pi_prod_mul | (intros; apply GlobalTheory.StabUnfold.lintegral_pi_prod_mul <;> assumption)
