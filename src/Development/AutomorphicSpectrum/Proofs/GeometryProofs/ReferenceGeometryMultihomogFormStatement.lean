module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ReferenceGeometryMultihomogForm
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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GapN

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.ExRefEff

theorem _root_.GlobalTheory.T.reference_geometry_multihomog_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β₀ : O →+* c.F) (Y : Model Xo c β₀) (G : RefGeo Y), ∃ (β : MRing G.J) (dβ : G.K → ℕ), IsMultiHomog β dβ ∧ β ∉ mCoordIdeal G.y ∧ MvPolynomial.aeval G.y β ≠ 0 ∧ MvPolynomial.aeval G.y β ∈ chartLat G.y (fun κ => (dβ κ : ℤ)) 1 ∧ ∀ p : Cpt G.𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre G.𝔐.ξ r p) → p.1 ∉ abLocus G.𝔐.t.G → ∀ cc : ∀ k, G.J k, InChart G.𝔐.ξ (fun c' : ∀ k, G.J k => ∏ k, G.y ⟨k, c' k⟩) cc p → ¬ unitAt G.𝔐.ξ p (MvPolynomial.aeval G.y β * ∏ k, G.y ⟨k, cc k⟩ ^ (-((1 : ℕ) * (dβ k : ℤ)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | exact GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form | (intros; apply GlobalTheory.CompanionTheory.Ar.ExRefEff.BdForm.bd_form <;> assumption)
