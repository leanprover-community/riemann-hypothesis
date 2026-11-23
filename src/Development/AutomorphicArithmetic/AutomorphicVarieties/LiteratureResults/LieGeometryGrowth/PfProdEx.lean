module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_conj_mul (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (f x) * h x) g = fun y => Complex.conjCLE (chart f g y) * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

end

theorem UpperTheory.V.Lit.Geo.Pf.prodEx :
    UpperTheory.V.Lit.Geo.Pf.ProdEx := by
  intro E _ _ _ a φ ψ
  refine ⟨⟨fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x, fun g => ?_⟩, fun _ => rfl, fun X g => ?_⟩
  · rw [chart_conj_mul]
    exact (Complex.conjCLE.contDiff.comp_contDiffOn (φ.2 g)).mul (ψ.2 g)
  · have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
      simpa using chart_val f g 1
    change fderiv ℝ (chart (fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x) g) (oneL E a) X =
      starRingEnd ℂ (fderiv ℝ (chart φ.1 g) (oneL E a) X) * ψ.1 g +
        starRingEnd ℂ (φ.1 g) * fderiv ℝ (chart ψ.1 g) (oneL E a) X
    have h1 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (oneL E a)
      (differentiableAt_chart φ.2 g).hasFDerivAt).fun_mul (differentiableAt_chart ψ.2 g).hasFDerivAt
    rw [chart_conj_mul]
    refine (congrArg (fun L => L X) h1.fderiv).trans ?_
    simp [hv, mul_comm, add_comm]
