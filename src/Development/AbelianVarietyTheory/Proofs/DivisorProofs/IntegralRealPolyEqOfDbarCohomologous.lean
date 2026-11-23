module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCohomologousEvenFormsAlgebraClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem integral_evalF_of_dbarCoh : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (ι : Type) (w w' : ι → A.Pt → Ev n), (∀ i, DbarCoh A (w i) (w' i)) → ∀ P : MvPolynomial ι ℝ, A.integral (evalF A w P) = A.integral (evalF A w' P) := by
  intro M _ _ _ _ _ _ n A ι w w' hw P
  obtain ⟨hD1, -, hDalg⟩ := dbarCoh_algebra M n A
  obtain ⟨-, hc, -, -, -⟩ := GlobalTheory.formCalculus M n A
  obtain ⟨hfin, hadd, -, -⟩ := GlobalTheory.LineForm.wInt_props M n A
  have key : DbarCoh A (fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ)))
      (fun x => aeval (fun i => w' i x) (P.map (algebraMap ℝ ℂ))) := by
    induction P using MvPolynomial.induction_on with
    | C a =>
      have h := (hDalg (a : ℂ) 1 1 1 1 hD1 hD1).1
      convert h using 1 <;> funext x <;> simp [Algebra.algebraMap_eq_smul_one]
    | add p q hp hq =>
      have h := (hDalg 1 _ _ _ _ hp hq).2.1
      convert h using 1 <;> funext x <;> simp
    | mul_X p i hp =>
      have h := (hDalg 1 _ _ _ _ hp (hw i)).2.2
      convert h using 1 <;> funext x <;> simp
  obtain ⟨-, hf', -, -, u, hu, eu⟩ := key
  have e1 : evalF A w P = evalF A w' P + A.dbar u := by
    show fld A _ = fld A _ + _
    rw [← eu]
    abel
  have hdu : A.IsForm (A.dbar u) := (hc 1 u u hu hu).2.2.2.2.1
  have int1 : ∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part α ε) := fun α h ε => by
    haveI := hfin α h ε
    exact integrable_const 1
  calc A.integral (evalF A w P) = wInt A (fun _ => 1) (evalF A w' P + A.dbar u) := by rw [wInt_one, e1]
    _ = wInt A (fun _ => 1) (evalF A w' P) + wInt A (fun _ => 1) (A.dbar u) :=
      (hadd _ _ _ hf' hdu (int1 _ hf') (int1 _ hdu)).2
    _ = A.integral (evalF A w' P) := by
      rw [wInt_one, wInt_one, (GlobalTheory.CxFormStokesBoth.stokes M n A u hu).2, add_zero]

end GlobalTheory.ChernCalc
