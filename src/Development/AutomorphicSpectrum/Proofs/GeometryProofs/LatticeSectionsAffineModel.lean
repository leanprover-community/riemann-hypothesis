module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalLieModelExtendsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFrames.Chart

open GlobalTheory.CompanionTheory.Ar.LieVB GlobalTheory.CompanionTheory.Ar.LieTangent

theorem ring_eq' {X : Scheme.{0}} {R : Type} [CommRing R] (x : Sp R ⟶ X) [Mono x] (z : Sp ℂ ⟶ X)
    (ψ : R →+* X.presheaf.stalk (centre z)) (hψ : spMap ψ ≫ x = X.fromSpecStalk (centre z)) (f : R →+* ℂ)
    (hf : spMap f ≫ x = z) : (Scheme.stalkClosedPointTo z).hom.comp ψ = f := by
  have h1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) ≫ x = spMap f ≫ x := by
    have e1 : spMap ((Scheme.stalkClosedPointTo z).hom.comp ψ) =
        spMap (Scheme.stalkClosedPointTo z).hom ≫ spMap ψ := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e1, Category.assoc, hψ, hf]
    exact spec_centre z
  exact congrArg (fun g => g.hom) (Spec.map_injective ((cancel_mono x).1 h1))

theorem exists_chart_values : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) (N : X.Opens) (J : Type) [Finite J] (c : J → E), p.1 ∈ N → (∀ i, c i ∈ M.lat p) → ∃ (A : X.Opens) (hA : IsAffineOpen A) (EB : Type) (_ : AddCommGroup EB) (_ : Module Γ(X, A) EB) (MB : LieModel G hA.fromSpec EB) (e : J → EB), p.1 ∈ A ∧ A ≤ N ∧ ∀ (y : Sp ℂ ⟶ X) (f : Γ(X, A) →+* ℂ), genPt ξ ⤳ centre y → y = spMap f ≫ hA.fromSpec → ∀ (i : J) (w : epsAt y ⟶ G), w.left = spMap (dualMap f) ≫ (MB.pt (e i)).left → M.ValAt y (c i) w := by
  intro X G _ _ _ Ω _ ξ E _ _ M p N J _ c hpN hc
  obtain ⟨R, _, x, _, F, _, _, MR, e, hpx, hxN, hext⟩ := GlobalTheory.T.local_lie_model_extends X G Ω ξ E M p N J c hpN hc
  obtain ⟨_, ⟨A, hA, rfl⟩, hpA, hAx⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hpx x.opensRange.isOpen
  replace hA : IsAffineOpen A := hA
  have hrange : Set.range hA.fromSpec ⊆ Set.range x := by
    rw [hA.range_fromSpec]
    exact hAx
  obtain ⟨a, ha⟩ : ∃ a : R →+* Γ(X, A), spMap a ≫ x = hA.fromSpec :=
    ⟨(Spec.preimage (IsOpenImmersion.lift x hA.fromSpec hrange)).hom, by
      change Spec.map (CommRingCat.ofHom (Spec.preimage (IsOpenImmersion.lift x _ hrange)).hom) ≫ x = _
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  obtain ⟨EB, iEB, mEB, ⟨MB⟩⟩ := lieModel_exists X G Γ(X, A) hA.fromSpec
  have hex : ∀ i, ∃ b, MB.pt b = epsBase a ha ≫ MR.pt (e i) := fun i =>
    MB.onto _ (isTanAt_base a ha (MR.tan _))
  choose eB heB using hex
  refine ⟨A, hA, EB, iEB, mEB, MB, eB, hpA, fun t ht => hxN (hAx ht), ?_⟩
  intro y f hg hy i w hw
  let q : Cpt ξ := ⟨centre y, hg⟩
  have hqr : q.1 ∈ x.opensRange := by
    refine hrange ⟨spMap f (IsLocalRing.closedPoint ℂ), ?_⟩
    change _ = centre y
    simp only [centre, hy, Scheme.Hom.comp_apply]
    rfl
  have hqx : (X.fromSpecStalk q.1) (IsLocalRing.closedPoint (X.presheaf.stalk q.1)) ∈ x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hqr
  obtain ⟨ψ, hψ⟩ := exists_lift (A := X.presheaf.stalk q.1) x (X.fromSpecStalk q.1) hqx
  have hring : (Scheme.stalkClosedPointTo y).hom.comp ψ = f.comp a := by
    refine ring_eq' x y ψ hψ _ ?_
    have e2 : spMap (f.comp a) = spMap f ≫ spMap a := by
      simp only [spMap, ← Spec.map_comp]; rfl
    rw [e2, Category.assoc, ha, hy]
  let vq : epsAt (R := X.presheaf.stalk q.1) (X.fromSpecStalk q.1) ⟶ G := epsBase ψ hψ ≫ MR.pt (e i)
  refine ⟨hg, vq, hext q ψ hψ i vq rfl, ?_⟩
  rw [hw, heB]
  change spMap (dualMap f) ≫ spMap (dualMap a) ≫ (MR.pt (e i)).left =
    spMap (dualMap (Scheme.stalkClosedPointTo y).hom) ≫ spMap (dualMap ψ) ≫ (MR.pt (e i)).left
  rw [← Category.assoc, ← Category.assoc, spMap_dual_comp, spMap_dual_comp, hring]

end GlobalTheory.CompanionTheory.Ar.LocFrames.Chart
