module

public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralTypesAndDirections
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

theorem _root_.GlobalTheory.T.exists_integral_types_and_directions' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (ϖ : T.V), Irreducible ϖ → ∀ (g : ℕ), g.Prime → ¬ IsUnit ((g : ℕ) : T.V) → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup → ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → letI := io.toAlgebra; ∃ (σ : (E →+* ℂ) → 𝓞 E →+* TWO.Ov v) (e : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v), (∀ τ a, (σ τ a : F) = algebraMap T.Fr F (io (embK c τ a))) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.V F (C.uvecT ℓ i)) ∧ (∀ ℓ i, (e ℓ i : F) = algebraMap T.Fr F (C.ch.uvec ℓ i)) ∧ (∀ (a : 𝓞 E) ℓ, (dAct F C.ch.B a).mulVec (fun i => (e ℓ i : F)) = (σ ℓ.1 a : F) • fun i => (e ℓ i : F)) ∧ (∀ τ a, (0 < v (σ τ a : F) → σ τ a ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ (¬ 0 < v (σ τ a : F) → IsUnit (σ τ a))) ∧ (∀ τ a, σ (ComplexEmbedding.conjugate τ) a = σ τ (star a)) ∧ (open Classical in ∃ lam : Lt1 Dw → Fin (chD C.ch) → TWO.Ov v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) ∧ (open Classical in ∃ ε : (E →+* ℂ) → 𝓞 E, ∀ τ τ', σ τ' (ε τ) - (if τ = τ' then 1 else 0) ∈ Ideal.span {((g : ℕ) : TWO.Ov v)}) ∧ ¬ IsUnit ((g : ℕ) : TWO.Ov v) := by
  first | exact @GlobalTheory.PowGerm.exists_integral_types_and_directions | exact GlobalTheory.PowGerm.exists_integral_types_and_directions | (intros; apply GlobalTheory.PowGerm.exists_integral_types_and_directions <;> assumption)
