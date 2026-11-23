module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNeighbourhoodFinitePieceIsolatedPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoFinitePieceFlatConnectedChartStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_flat_chart_etale_of_quasiFiniteAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, IsClosed ({x} : Set U.left) → U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → (∃ O : U.left.Opens, x ∈ O ∧ ∀ u ∈ O, τ u = τ x → u = x) → ∃ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h ∧ p ∈ W ∧ pullback.fst τ h p = x ∧ Etale (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxc hxm hinj hsurj hqf
  have hτf : LocallyOfFiniteType τ := by
    have : LocallyOfFiniteType (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUf
    exact locallyOfFiniteType_of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have hτs : IsSeparated τ := by
    have : IsSeparated (τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R)) := by rw [hτ]; exact hUs
    exact IsSeparated.of_comp τ (𝔸(Fin g; Sp R) ↘ Sp R)
  have : IsNoetherianRing R := hR.1
  have hA : IsLocallyNoetherian 𝔸(Fin g; Sp R) := LocallyOfFiniteType.isLocallyNoetherian (𝔸(Fin g; Sp R) ↘ Sp R)
  obtain ⟨T, h, W, p, het, hcon, hpW, hpx, hfin, hone, hgeo⟩ := GlobalTheory.T.exists_etale_neighbourhood_finite_piece_isolated_point _ _ τ hA hτf hτs x hqf
  have hiso := GlobalTheory.T.isIso_finite_piece_flat_connected_chart R hR S X π U a b g τ c hπp hπs hπΓ hUf hUs ha haΓ hτ hc1 hc2 hc x hxm hinj hsurj
    T h W p inferInstance hcon hpW hpx hfin hone hgeo
  exact ⟨T, h, W, p, inferInstance, hpW, hpx, inferInstance⟩
