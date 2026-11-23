module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSC
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRamifiedEigenLiftsOfChartDirections
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem _root_.GlobalTheory.T.exists_ramified_eigen_lifts_of_chart_directions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsGalois ℚ E → ∀ (p a m : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ¬ p ∣ m → (NumberField.discr E).natAbs = p ^ a * m → (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsPrime → (p : 𝓞 E) ∈ 𝔭 → ∃ x ∈ 𝔭, H.bar x ∉ 𝔭) → ∀ e : ℕ, 0 < e → letI := io.toAlgebra; ∃ (π : Type) (_ : Fintype π) (_ : DecidableEq π) (cc : (E →+* ℂ) → π) (s : (E →+* ℂ) → Bool), (∀ τ, cc (ComplexEmbedding.conjugate τ) = cc τ ∧ s (ComplexEmbedding.conjugate τ) ≠ s τ) ∧ ∃ (φ : Lt1 Dw → Fin (chD C.ch) → T.V) (ψ : Lt1 Dw → Fin (chD C.ch) → T.Fr), (∀ ℓ i, (((-((vV T.V (p : T.Fr) : ℝ) / e * ((a : ℝ) / Module.finrank ℚ E))) : ℝ) : EReal) ≤ nval T.V e (ψ ℓ i)) ∧ (∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 ≠ ComplexEmbedding.conjugate ℓ.1 → ∑ i, (algebraMap T.V T.Fr (φ ℓ' i) + ψ ℓ' i - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ') i) * C.ch.uvec ℓ i = 0) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (0, ψ ℓ)) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) ∧ TB.OppositePairVanishing T.Fr (fun ℓ : Lt1 Dw => cc ℓ.1) (fun ℓ => s ℓ.1) (fun ℓ => (C.ch.uvec ℓ, fun i => algebraMap T.V T.Fr (φ ℓ i) - (TB.sg1 T.Fr C.ch.h).mulVec (C.ch.uvec ℓ) i)) (fun ℓ => (0, ψ ℓ)) := by
  first | exact @GlobalTheory.PlaceInt.exists_ramified_eigenLifts | exact GlobalTheory.PlaceInt.exists_ramified_eigenLifts | (intros; apply GlobalTheory.PlaceInt.exists_ramified_eigenLifts <;> assumption)
