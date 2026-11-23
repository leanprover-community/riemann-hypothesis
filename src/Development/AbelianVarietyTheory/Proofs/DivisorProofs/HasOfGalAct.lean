module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenCubicalTrivialisationDescendedClosedTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationCompleteLocalEvenOnTorusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationPullbackInjectiveLocStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoGenericFibreDescendFiniteExtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDegDataIsoOfGaloisDescendedGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleDescendsAlongGaloisExtensionStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem has_of_galAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → Has D := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hgal D D' hD A' G' _ _ hS' U' a G _ _ β hS pb hinv
  obtain ⟨A, gen, κ, hgen, hκ, hLA⟩ := GlobalTheory.T.polarised_generic_fibre_descends_galois R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv
  obtain ⟨P, hP⟩ := GlobalTheory.T.uniformisationBundle_descends_along_galoisExtension R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv
  have hAP := GlobalTheory.T.lineBundleIso_genericFibre_descend_finite_ext R hR R' ρ hfin G' G β hS' hS pb A gen κ hgen hκ U'.LG.L U'.LG.isLB hLA P hP
  have hev := GlobalTheory.T.evenCubicalTrivialisation_descended_closedTorus R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv P hP
  obtain ⟨D₁, U₁, hLG, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R hR G P hS hev A gen hgen hAP
  have hP₁ : LBIso U'.LG.L (U₁.LG.L.pull β) := by rw [hLG]; exact hP
  have h₁ := GlobalTheory.T.nonempty_degData_iso_of_galoisDescendedGroup R hR R' ρ hfin hgal D D' hD A' G' hS' U' a G β hS pb hinv A D₁ U₁ hP₁
  exact GlobalTheory.T.hasSemiAbelianUniformisation_pullback_injective_local R R (RingHom.id R) hR.1 hR.1 Function.injective_id inferInstance D₁ D h₁
    ⟨G, inferInstance, inferInstance, A, hS, ⟨U₁⟩⟩

end GlobalTheory.Mum
