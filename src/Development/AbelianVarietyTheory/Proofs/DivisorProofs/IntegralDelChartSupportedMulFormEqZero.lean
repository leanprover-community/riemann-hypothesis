module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelFnMulEqZeroOfIsForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

set_option autoImplicit false

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

theorem integral_del_fn_mul_eq_zero : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.del (A.fn χ * γ)) = 0 := by
  intro M _ _ _ _ _ _ n A γ χ i hγ hχ hs
  exact integral_del_fn_mul_eq_zero_of_isForm A γ χ i hγ hχ hs
    (GlobalTheory.T.holAtlas_isForm_del A _ (FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ))

end GlobalTheory.CxForm.LocStokes
