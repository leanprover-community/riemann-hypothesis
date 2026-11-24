module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralFrameSubalgebraRelay
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


theorem _root_.GlobalTheory.T.integral_frame_subalgebra_relay : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntAll Xo c → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e₀ : ℕ), OverLa la T.V io e₀ → T.FinRes → ∀ y : IntFr Xo c T io, letI := io.toAlgebra; ∀ (S : Type) [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) (ψ : S →ₐ[c.F] T.Fr) (z₀ : FrPt Xo c T.Fr) (t₀ : Ix Dw → T.Frˣ), FrMap ψ w z₀ → FrBor t₀ z₀ y.1 → ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →ₐ[c.F] T.Fr, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV T.V (ψ' s - ψ s)) → ∀ z' : FrPt Xo c T.Fr, FrMap ψ' w z' → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (e' : ℕ) (y' : IntFr Xo c T' io'), OverLa la T'.V io' e' ∧ y'.IsAlg ∧ letI := io'.toAlgebra; ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (z'' : FrPt Xo c T'.Fr) (t' : Ix Dw → T'.Frˣ), FrMap φ z' z'' ∧ FrBor t' z'' y'.1 ∧ (∀ x : T.Fr, x ≠ 0 → vV T'.V (φ x) * (e₀ : ℤ) = (e' : ℤ) * vV T.V x) ∧ ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), vV T'.V ((t' (some ⟨τ, i⟩) : T'.Frˣ) : T'.Fr) * (e₀ : ℤ) = (e' : ℤ) * vV T.V ((t₀ (some ⟨τ, i⟩) : T.Frˣ) : T.Fr) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay | exact GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.integral_frame_subalgebra_relay <;> assumption)
