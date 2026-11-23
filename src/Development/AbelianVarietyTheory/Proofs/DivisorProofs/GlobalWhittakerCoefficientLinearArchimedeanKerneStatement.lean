module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerne
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem _root_.GlobalTheory.T.globalWhittakerCoefficient_linear_archimedeanKernel : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ), Continuous F → Continuous G → (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) → (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) → (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧ ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  first | exact @GlobalTheory.JSW.WhitAlg.whit_linear_kerInf | exact GlobalTheory.JSW.WhitAlg.whit_linear_kerInf | (intros; apply GlobalTheory.JSW.WhitAlg.whit_linear_kerInf <;> assumption)
