module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledCoverUnitaryPELTypeFiniteExtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionExtensionToUniformisedSemiAbeliaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPELTypeFactorDegDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfFiniteExtTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationOfLabelledCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedOfDegDataFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isSemiAbelian_of_isGrpPullback' {S T : Scheme.{0}} {f : T ⟶ S} {G : Over S} [GrpObj G] {G' : Over T} [GrpObj G']
    [IsCommMonObj G'] {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

theorem has_of_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ D : DegData R (maximalIdeal R), Has D := by
  intro R _ _ _ hB D
  rcases subsingleton_or_nontrivial D.toPre.X with hX | hX
  · exact GlobalTheory.Mum.has_of_subsingleton R hB.1 D hX
  obtain ⟨E, _, _, _, H, Dm, D', hmod, o, hPel, F, hA⟩ := GlobalTheory.T.exists_unitaryPELType_factor_degData R hB D hX
  have hX' : Nontrivial D'.toPre.X :=
    (Function.LeftInverse.injective (g := F.xp) (f := F.xi) F.xp_xi).nontrivial
  obtain ⟨R', _, _, _, ρ, D'', hρ, hpull, hcov⟩ := GlobalTheory.T.exists_labelledCover_unitaryPELType_finiteExt R hB E H Dm D' o hX' hPel
  have hB' : Base R' := ⟨hρ.1, @charZero_of_injective_ringHom _ _ _ _ ρ hρ.2.1 hB.2⟩
  have hfin'' : HasFin D'' := GlobalTheory.T.hasSemiAbelianUniformisation_of_labelledCover R' hB' D'' hcov
  have hfin' : HasFin D' := GlobalTheory.Mum.hasFin_of_finExt R R' ρ hρ D' D'' hpull hfin''
  obtain ⟨G', _, _, A', hG', ⟨U'⟩⟩ := GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt R hB D' hfin'
  obtain ⟨oA, oG, hlin⟩ := GlobalTheory.T.exists_ringAction_extension_to_uniformised_semiAbelian R hB D' A' G' hG' U' F.O F.o
  have hidem : oG.act F.e ≫ oG.act F.e = oG.act F.e := by rw [← oG.map_mul, F.idem]
  obtain ⟨G, _, _, inc, pr, hG, hinc, hpr, hip, hpi⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image (Sp R) G' hG' (oG.act F.e) (oG.hom F.e) hidem
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β, β₂, A₁, U₁, hρ₁, hpull₁, hgp, -, -⟩ :=
    GlobalTheory.T.idempotentFactor_uniformised_of_degData_factor R hB D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  exact GlobalTheory.T.hasSemiAbelianUniformisation_of_finiteExt R hB D
    ⟨R₁, _, _, _, ρ₁, D₁, hρ₁, hpull₁, G₁, _, _, A₁, isSemiAbelian_of_isGrpPullback' hgp hG, ⟨U₁⟩⟩
end GlobalTheory.Mum
