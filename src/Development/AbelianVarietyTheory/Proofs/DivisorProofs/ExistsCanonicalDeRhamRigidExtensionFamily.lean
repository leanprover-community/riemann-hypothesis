module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExtStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalIsoHodgeFiltrationEqRangeInvariantFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionPullbackNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTowerStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtensionStatement
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DeRhamExt

def canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : primDR A →ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) :=
  Classical.choose (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA)

theorem isCan_iff_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A)
    (x : ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))) : IsCan t c x ↔ canMap p hA t c = x :=
  Classical.choose_spec (GlobalTheory.T.exists_linear_canonical_map_primitiveDeRham_rigExt R A p G t hA) c x

theorem isCan_canMap (p : ℕ) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    (hA : IsAbelianScheme A) {G : PDivGroup p R} (t : G.TorsionTower A) (c : primDR A) :
    IsCan t c (canMap p hA t c) :=
  (isCan_iff_canMap p hA t c _).2 rfl

theorem canMap_bijective (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] {R : Type}
    [CommRing R] (hR : IsNilpotent (p : R)) {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A)
    {G : PDivGroup p R} (t : G.TorsionTower A) : Function.Bijective (canMap p hA t) := by
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
  exact GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent hP p R hR A g hA hg G t _ (isCan_canMap p hA t)

def canFamily (hP : GlobalTheory.Published.AbelianHodgeDeRham) (p : ℕ) [Fact p.Prime] :
    GlobalTheory.Published.DeRhamVectorExtension.Family p :=
  fun _ _ hR _ _ hA _ t => LinearEquiv.ofBijective (canMap p hA t) (canMap_bijective hP p hR hA t)

theorem exists_canonical_family : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime],
    ∃ e : GlobalTheory.Published.DeRhamVectorExtension.Family p, e.Natural ∧ e.Filtered ∧ e.Tangent ∧
      ∀ ⦃R : Type⦄ [CommRing R] (hR : IsNilpotent (p : R)) ⦃A : Over (Sp R)⦄ [GrpObj A]
        (hA : IsAbelianScheme A) ⦃G : PDivGroup p R⦄ (t : G.TorsionTower A) (c : primDR A),
        IsCan t c (e hR hA t c) := by
  intro hP p _
  refine ⟨canFamily hP p, ?_, ?_, ?_, ?_⟩
  · intro R R' _ _ hR hR' A _ A' _ hA hA' G G' t t' σ φ m c
    exact ((isCan_iff_canMap p hA' t' _ _).1
      (GlobalTheory.T.canonicalRigidifiedExtension_pullback_naturality p R R' A A' G G' t t' σ φ m c _ (isCan_canMap p hA t c)))
  · intro R _ hR A _ hA G t
    obtain ⟨N, hN⟩ := hR
    exact GlobalTheory.T.canonical_iso_hodge_filtration_eq_range_invariant_forms p R N hN A hA G t (canMap p hA t)
      (canMap_bijective hP p ⟨N, hN⟩ hA t).2 (isCan_canMap p hA t)
  · intro R _ hR A _ hA G t h v
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_relativeDimension_abelian_torsionTower hP p R hR A hA G t
    exact GlobalTheory.T.lie_image_iff_lie_correspondence_deRham_extension hP p R hR A g hA hg G t (canFamily hP p hR hA t)
      (isCan_canMap p hA t) h v
  · intro R _ hR A _ hA G t c
    exact isCan_canMap p hA t c

end GlobalTheory.DeRhamExt
