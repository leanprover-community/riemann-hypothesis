module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBound
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.cusp_correspondence_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] [CharZero L] (z : Sp L ⟶ 𝔐.X), ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* L), 𝔐.LabVal z id σ ∧ (∀ σ', 𝔐.LabVal z id σ' → σ' = σ) ∧ Function.Bijective σ ∧ (∀ s, Function.Injective (σ s)) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E ∧ ∀ e : L →+* ℂ, IsCMFam (fun τ => e.comp (σ (.inl τ))) ∧ IsCMFam (fun τ => e.comp (σ (.inr τ))) ∧ ∀ τ, e.comp (σ (.inr τ)) = (starRingEnd ℂ).comp (e.comp (σ (.inl τ))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal | exact GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal <;> assumption)
