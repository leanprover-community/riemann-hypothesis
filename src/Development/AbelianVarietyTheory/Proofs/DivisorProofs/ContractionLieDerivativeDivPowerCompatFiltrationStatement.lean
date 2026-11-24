module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltration
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

theorem _root_.GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ x ∈ rel R δ, ctr v x ∈ rel R δ ∧ lie v x ∈ rel R δ) ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ n, (∀ x ∈ filDR R δ n, ctr v x ∈ filDR R δ n) ∧ (∀ x ∈ filDR R δ (n + 1), dDR R B x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), lie v x ∈ filDR R δ n := by
  first | exact @GlobalTheory.PDForm.ctr_lie_rel_filDR | exact GlobalTheory.PDForm.ctr_lie_rel_filDR | (intros; apply GlobalTheory.PDForm.ctr_lie_rel_filDR <;> assumption)
