module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelOperatorRowFrequencyColumnTranslate
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.exists_kernelOperator_rowFrequency_columnTranslate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), (ρ : ℕ) + 1 < n → ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z × (Fin n → Cinf E) → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∃ T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T' ∧ ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ z, ∀ g ∈ levSetInf E n (ρ + 1), T' W z g = T W (z, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) g := by
  first | exact @GlobalTheory.JSW.MirCinf.exists_kerOpInf_rowFreq_colGL | exact GlobalTheory.JSW.MirCinf.exists_kerOpInf_rowFreq_colGL | (intros; apply GlobalTheory.JSW.MirCinf.exists_kerOpInf_rowFreq_colGL <;> assumption)
