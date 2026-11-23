module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousGaussSp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsDistSectionMulBlock
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.ptSq_add_hsDist_comparable_hsDist_mul : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (j : UpqT P' Q' → UpqT P Q), IsBlockEmb e j → ∀ t : ℝ, 1 < t → ∃ δ : ℝ, 0 < δ ∧ ∀ (y : Sp P Q) (a : UpqT P Q), ptSq e y < δ → act a (baseVec e) = y → (∀ b, ‖UpqT.mat a (e none) (e (some b))‖ = ‖y (e (some b))‖) → (∀ i b, ‖(UpqT.mat a - 1) (e (some i)) (e (some b))‖ = ‖y (e (some i))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖) → ∀ g : UpqT P' Q', ptSq e y + hsDist g ≤ t * hsDist (a * j g) ∧ hsDist (a * j g) ≤ t * (ptSq e y + hsDist g) := by
  first | exact @GlobalTheory.SectionHsCompare.hsDist_section_mul_block | exact GlobalTheory.SectionHsCompare.hsDist_section_mul_block | (intros; apply GlobalTheory.SectionHsCompare.hsDist_section_mul_block <;> assumption)
