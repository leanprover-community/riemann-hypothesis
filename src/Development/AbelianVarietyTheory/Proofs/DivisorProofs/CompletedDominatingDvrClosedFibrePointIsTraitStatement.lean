module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTrait
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.completed_dominating_dvr_closedFibre_point_is_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  first | exact @GlobalTheory.Mum.trait_at_closed_point | exact GlobalTheory.Mum.trait_at_closed_point | (intros; apply GlobalTheory.Mum.trait_at_closed_point <;> assumption)
