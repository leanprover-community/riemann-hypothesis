module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivPairingEqZeroOfIsHeat
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

@[expose] public section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.polyDeriv_aeval_pairings_eq_zero_of_isHeat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) (n N : ℕ) (D : CM Ψ N N → CM Ψ n N → CM Ψ n N → ℂ), IsHeat Ψ D → (∀ Z ∈ Hn Ψ N, D Z 0 0 = 0) → ∀ Z ∈ Hn Ψ N, ∀ s : MvPolynomial (Ψ × Fin N × Fin N) ℂ, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.aeval (fun v : Ψ × Fin N × Fin N => ∑ k, (MvPolynomial.X (v.1, false, k, v.2.1) * MvPolynomial.X (v.1, true, k, v.2.2) : MvPolynomial (Ψ × Bool × Fin n × Fin N) ℂ)) s) (fun v => (Pi.single v 1 : Ψ × Bool × Fin n × Fin N → ℂ)) (fun w : Ψ × Bool × Fin n × Fin N → ℂ => D Z (fun τ => Matrix.of fun k a => w (τ, false, k, a)) (fun τ => Matrix.of fun k a => w (τ, true, k, a))) 0 = 0 := by
  first | exact @GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | exact GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat | (intros; apply GlobalTheory.SW.polyDeriv_pairing_eq_zero_of_isHeat <;> assumption)
