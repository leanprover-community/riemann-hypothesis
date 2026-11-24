module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslateTaylorSecondOrder
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst

@[expose] public section

open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

theorem _root_.GlobalTheory.T.schwartz_translate_taylor_second_order : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (f : 𝓢(X, ℂ)) (k n : ℕ), ∃ C : ℝ, ∀ a : X, ‖a‖ ≤ 1 → SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-a) f - f - LineDeriv.lineDerivOpCLM ℂ 𝓢(X, ℂ) a f) ≤ C * ‖a‖ ^ 2 := by
  first | exact @GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | exact GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le | (intros; apply GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_lineDeriv_le <;> assumption)
