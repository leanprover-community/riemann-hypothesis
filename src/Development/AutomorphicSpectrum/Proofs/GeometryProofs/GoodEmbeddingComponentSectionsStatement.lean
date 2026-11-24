module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodEmbeddingComponentSections
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.DefiniteFormStabilizerFiniteAwayFromP
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall

@[expose] public section

open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem _root_.GlobalTheory.T.good_embedding_component_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (Z : Comp Xo c) (k : (U σ).Comp), Over (U σ) (e Z) k → ∀ (a : WZ E) (N : ℕ) (g : Fin (N + 1) → Rul Xo c), (∀ j, g j ∈ GlobalTheory.CompanionTheory.Ar.Rec.secZ Xo c a) → BirOn h Z g → ∀ (φ : Om Z →ₐ[c.F] CAt σ) (x₀ y : ((U σ).X k).dom) (y₁ : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y₁ → FrBor t ((U σ).un k x₀) y₁ → ∀ w : ℂ, w ≠ 0 → (∀ j, rdU (U σ) (g j) k y.1 = w * toC (φ (evC h Z (g j)))) → ∃ t' : Ix Dw → (CAt σ)ˣ, FrBor t' ((U σ).un k x₀) ((U σ).un k y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings | exact GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings | (intros; apply GlobalTheory.CompanionTheory.Ar.SameFlag.frBor_of_proportional_readings <;> assumption)
