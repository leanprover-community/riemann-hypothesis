module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreFinitelyGeneratedExtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedSpaceOfFinGenSubfieldBaseChangesStatement
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

theorem GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ hA M K _ κ
  obtain ⟨hN, -, hIC, -⟩ := hA
  haveI := hN
  haveI := hIC
  obtain ⟨hbij, hsurj⟩ := Modif.appTop_bijective_surjective R M
  haveI := M.proper
  haveI := hsurj
  have hcomp : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      spMap ψ ≫ spMap (residue R) = spMap (ψ.comp (residue R)) := fun ψ => by
    rw [← Spec.map_comp]; rfl
  have pc : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) [PreconnectedSpace X], PreconnectedSpace Y :=
    fun h _ => ⟨by rw [← h.surjective.range_eq, ← Set.image_univ]; exact isPreconnected_univ.image _ h.continuous.continuousOn⟩
  let f := pullback.snd M.π (spMap (residue R))
  have e : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      pullback f (spMap ψ) ≅ pullback M.π (spMap (ψ.comp (residue R))) := fun ψ =>
    pullbackLeftPullbackSndIso M.π (spMap (residue R)) (spMap ψ) ≪≫ pullback.congrHom rfl (hcomp ψ)
  have hP : PreconnectedSpace (pullback f (spMap κ) : Scheme.{0}) := by
    refine GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges (ResidueField R) _ f inferInstance inferInstance K κ fun L hL n c hc => ?_
    have hc' := GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext R M.S M.π inferInstance hsurj hbij K κ L hL n c hc
    exact @pc _ _ _ _ (Scheme.homeoOfIso (e _)).symm hc'.toPreconnectedSpace
  haveI : PreconnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) :=
    pc (Scheme.homeoOfIso (e κ))
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd M.π (spMap (κ.comp (residue R)))).surjective q
  exact ConnectedSpace.mk ⟨z⟩
