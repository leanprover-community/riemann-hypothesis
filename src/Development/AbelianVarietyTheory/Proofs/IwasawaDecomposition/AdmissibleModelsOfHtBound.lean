import Mathlib
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDeRhamFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineModelTrueOfFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelWithRatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombinationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsOfGenericLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrimeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFrameValuationBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.ShFam.Pad.exists_dominating_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (n : ℕ) (Z : Fin (n + 1) → Mdl Y i₀), (∀ a, (Z a).i = (Z 0).i ∧ (Z a).ty = (Z 0).ty) → ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧ ∀ a, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f :=
  fun E _ _ _ H Dw Xo p W Y i₀ hp hW hN n Z hZ =>
    GlobalTheory.LocM.MapComp.exists_dominating (fun Z₁ Z₂ h => ⟨_, GlobalTheory.T.correspondence_diagonal E H Dw Xo p W hp hW Y i₀ hN.1 Z₁ Z₂ h⟩) n Z hZ
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_common_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (n : ℕ) (Z : Fin (n + 1) → Mdl Y i₀), (∀ a, (Z a).i = (Z 0).i ∧ (Z a).ty = (Z 0).ty) → ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧ ∀ a, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f := by
  atlas_forward_decl GlobalTheory.ShFam.Pad.exists_dominating_model
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_with_ratio : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → N2 Y → ∀ (Z : Mdl Y i₀) st (x : Letter Dw), letterOf Dw st = some x → (∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) → HasRatio Z st → ∃ (Z' : Mdl Y i₀) (f : Z'.X ⟶ Z.X), Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ IsMap Z' Z f ∧ HasPRatio Z' st := by
  first | exact @GlobalTheory.HTLine.exists_pRatio | exact GlobalTheory.HTLine.exists_pRatio | (intros; apply GlobalTheory.HTLine.exists_pRatio <;> assumption)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_affine_domain {X : Scheme.{0}} [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (V : X.Opens) {z : X}
    (hz : z ∈ V) : ∃ (U : X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(X, U)),
      z ∈ U ∧ U ≤ V ∧ IsIntegrallyClosed Γ(X, U) := by
  have hC : IsOpen (irreducibleComponent z) :=
    GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents z)
  obtain ⟨U, hU, hzU, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := z)
    (U := V ⊓ ⟨irreducibleComponent z, hC⟩) ⟨hz, mem_irreducibleComponent⟩
  have hpre : IsPreirreducible (U : Set X) := (isIrreducible_irreducibleComponent (x := z)).2.open_subset U.2
    fun q hq => (hle hq).2
  have hirr : IsIrreducible (U : Set X) := ⟨⟨z, hzU⟩, hpre⟩
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hirr
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : Nonempty (Spec Γ(X, U)) := ⟨hU.isoSpec.hom ⟨z, hzU⟩⟩
  have : IsIntegral (Spec Γ(X, U)) := isIntegral_of_isOpenImmersion hU.isoSpec.inv
  have hd : IsDomain Γ(X, U) := (affine_isIntegral_iff _).1 this
  exact ⟨U, hU, hd, hzU, fun q hq => (hle hq).1,
    (GlobalTheory.IsNormalScheme.spec_iff_of_isDomain _).1 (GlobalTheory.IsNormalScheme.spec_of_isAffineOpen hU)⟩

theorem gen_mem {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(X, U)] {q : X} (hq : q ∈ U)
    (hV : q ∈ V) : ⊤ ≤ (spMap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) ≫ hU.fromSpec) ⁻¹ᵁ V := by
  intro q' _
  have hg : (spMap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q') ⤳ hU.primeIdealOf ⟨q, hq⟩ := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    have e : (PrimeSpectrum.comap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q').asIdeal = ⊥ := by
      let q₀ : PrimeSpectrum (FractionRing Γ(X, U)) := q'
      have := q₀.isPrime
      change Ideal.comap _ q₀.asIdeal = ⊥
      rw [Ideal.eq_bot_of_prime q₀.asIdeal]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    change (PrimeSpectrum.comap (algebraMap Γ(X, U) (FractionRing Γ(X, U))) q').asIdeal ≤ _
    rw [e]
    exact bot_le
  have h2 := hg.map hU.fromSpec.continuous
  rw [hU.fromSpec_primeIdealOf ⟨q, hq⟩] at h2
  exact h2.mem_open V.2 hV

theorem tan_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) {R S : Type} [CommRing R] [CommRing S] (ρ : R →+* S) {x : Sp R ⟶ X} {x' : Sp S ⟶ X}
    (hx : spMap ρ ≫ x = x') {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h2 : ∀ i, IsTanAtG t x (v i))
    (h3 : ∀ u, IsTanAtG t x u → ∃! cf, IsCombAtG t x v cf u) :
    (∀ i, IsTanAtG t x' (spMap (dualMap ρ) ≫ v i)) ∧
      ∀ u, IsTanAtG t x' u → ∃! cf, IsCombAtG t x' (fun i => spMap (dualMap ρ) ≫ v i) cf u := by
  subst hx
  have B := GlobalTheory.T.isTanBasis_of_unique_combination E H X t R x n v h2 h3
  exact ⟨fun i => GlobalTheory.LieMet.isTan_map ρ rfl (h2 i), fun u hu => B.2 _ ρ u hu⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem isLocallyNoetherian_model (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : IsLocallyNoetherian Z.X := by
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  have := isProper_str (Z.i.c.V W) Z.n
  have : LocallyOfFiniteType Z.s := by
    unfold Pre.s
    infer_instance
  exact LocallyOfFiniteType.isLocallyNoetherian Z.s

set_option maxHeartbeats 1600000 in

theorem intFrame_restrict (Z : Mdl Y i₀) {U₀ U : Z.X.Opens} (hU₀ : IsAffineOpen U₀) (hU : IsAffineOpen U)
    (ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U)) (eρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec) {w₀ : Vecs Dw (Y Z.i).t Γ(Z.X, U₀)}
    (hfr : IntFrame Z hU₀ w₀) : IntFrame Z hU (w₀.bc ρ) := by
  have ex : spMap ρ ≫ hU₀.fromSpec ≫ Z.π = hU.fromSpec ≫ Z.π := by rw [← Category.assoc, eρ]
  refine ⟨fun σ => ?_, fun k _ φ hr => ?_⟩
  · obtain ⟨n, v, e, h1, h2, h3⟩ := hfr.1 σ
    obtain ⟨b1, b2⟩ := tan_restrict (Y Z.i).t ρ ex h2 h3
    exact ⟨n, _, e, fun i => congrArg (spMap (dualMap ρ) ≫ ·) (h1 i), b1, b2⟩
  · have e1 : spMap (φ.comp ρ) ≫ hU₀.fromSpec = spMap φ ≫ hU.fromSpec := by
      rw [← eρ, ← Category.assoc, ModelRelProbe.spMap_comp]
    rw [Vecs.bc_bc, ← e1]
    exact hfr.2 k _ (by rwa [e1])

theorem exists_tanBasis (Z : Mdl Y i₀) {U₀ U : Z.X.Opens} (hU₀ : IsAffineOpen U₀) (hU : IsAffineOpen U)
    (ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U)) (eρ : spMap ρ ≫ hU₀.fromSpec = hU.fromSpec) {w₀ : Vecs Dw (Y Z.i).t Γ(Z.X, U₀)}
    (hfr : IntFrame Z hU₀ w₀) : ∃ (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)),
      GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e := by
  have ex : spMap ρ ≫ hU₀.fromSpec ≫ Z.π = hU.fromSpec ≫ Z.π := by rw [← Category.assoc, eρ]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain ⟨n, v, -, -, h2, h3⟩ := hfr.1 σ
  obtain ⟨b1, b2⟩ := tan_restrict (Y Z.i).t ρ ex h2 h3
  exact ⟨n, _, GlobalTheory.T.isTanBasis_of_unique_combination E H _ _ _ _ n _ b1 b2⟩

theorem exists_coeff_gen (Z : Mdl Y i₀) {U : Z.X.Opens} (hU : IsAffineOpen U) [IsDomain Γ(Z.X, U)] {z : Z.X} (hzU : z ∈ U) :
    ∃ (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), Function.Injective β ∧
      spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  obtain ⟨β, eβ⟩ : ∃ β : ↥(Z.i.c.V W) →+* Γ(Z.X, U), spMap β = hU.fromSpec ≫ Z.s :=
    ⟨(Spec.preimage (hU.fromSpec ≫ Z.s)).hom, Spec.map_preimage _⟩
  obtain ⟨q, hqU, hqo⟩ := Z.dense.inter_open_nonempty U U.2 ⟨z, hzU⟩
  have hqo' : q ∈ ⋃ a, ((Z.U a).1 : Set Z.X) := by rw [Z.cover]; exact hqo
  obtain ⟨a, hqa⟩ := Set.mem_iUnion.1 hqo'
  obtain ⟨φ, hφ⟩ := Pull.exists_fromSpec (Z.U a).2 _ (gen_mem hU hqU hqa)
  have hφ' : spMap φ ≫ Z.chart a = spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec := hφ
  obtain ⟨y, hy⟩ := Pull.exists_open_lift Z hφ'
  refine ⟨β, y, ?_, by rw [hy, Category.assoc]⟩
  have cs := Pull.affineOpenChart_comp_structure_eq_spMap Z hφ'
  rw [Z.π_s, Category.assoc, ← eβ, ModelRelProbe.spMap_comp, ModelRelProbe.spMap_comp] at cs
  have e : (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))).comp β = (φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) cs)
  refine Function.Injective.of_comp (f := algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ?_
  have e' : (⇑(algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ∘ ⇑β) = ⇑((φ.comp (Z.alg a)).comp (Z.i.c.V W).subtype) :=
    congrArg DFunLike.coe e
  rw [e']
  exact (φ.comp (Z.alg a)).injective.comp (Z.i.c.V W).subtype_injective

theorem exists_small_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀), HasDR Z → ∀ z : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(Z.X, U)) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), z ∈ U ∧ IsIntegrallyClosed Γ(Z.X, U) ∧ Function.Injective β ∧ IntFrame Z hU w ∧ GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e ∧ spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z hDR z
  have hN : GlobalTheory.IsNormalScheme Z.X := Z.normal
  have := isLocallyNoetherian_model hp hW Z
  obtain ⟨U₀, hU₀, w₀, hz, hfr⟩ := hDR.2 z
  obtain ⟨U, hU, hd, hzU, hle, hic⟩ := exists_affine_domain U₀ hz
  obtain ⟨ρ, eρ⟩ : ∃ ρ : Γ(Z.X, U₀) →+* Γ(Z.X, U), spMap ρ ≫ hU₀.fromSpec = hU.fromSpec :=
    ⟨(Z.X.presheaf.map (homOfLE hle).op).hom, hU₀.map_fromSpec hU _⟩
  obtain ⟨g, e, he⟩ := exists_tanBasis Z hU₀ hU ρ eρ hfr
  obtain ⟨β, y, hβ, hy⟩ := exists_coeff_gen Z hU hzU
  exact ⟨U, hU, hd, w₀.bc ρ, g, e, β, y, hzU, hic, hβ, intFrame_restrict Z hU₀ hU ρ eρ hfr, he, hy⟩

end GlobalTheory.HTLine
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_domain_frame_hasDR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀), HasDR Z → ∀ z : Z.X, ∃ (U : Z.X.Opens) (hU : IsAffineOpen U) (_ : IsDomain Γ(Z.X, U)) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (β : ↥(Z.i.c.V W) →+* Γ(Z.X, U)) (y : Sp (FractionRing Γ(Z.X, U)) ⟶ (Xo Z.i.l).XF Z.i.c), z ∈ U ∧ IsIntegrallyClosed Γ(Z.X, U) ∧ Function.Injective β ∧ IntFrame Z hU w ∧ GlobalTheory.LineNorm.IsTanBasis (Y Z.i).t (R := Γ(Z.X, U)) (hU.fromSpec ≫ Z.π) e ∧ spMap (algebraMap Γ(Z.X, U) (FractionRing Γ(Z.X, U))) ≫ hU.fromSpec ≫ Z.π = y ≫ (Y Z.i).j := by
  atlas_forward_decl GlobalTheory.HTLine.exists_small_chart
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.roots_of_unity_and_p_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → (∀ N : ℕ, N ∣ l.A → ∃ ζ : ↥(c.V W), IsPrimitiveRoot ζ N) ∧ (IsGalois ℚ E → ∃ a : ↥(c.V W), (p : ↥(c.V W)) ∈ (Ideal.span {a}).radical ∧ ∀ (C : SCF p) (φ : ↥(c.V W) →+* ↥(intO ↥C.S)), Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -(vDiff E p * Real.log p)) := by
  first | exact @GlobalTheory.HTConst.const_main | exact GlobalTheory.HTConst.const_main | (intros; apply GlobalTheory.HTConst.const_main <;> assumption)
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTPres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

theorem bc_bc {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'')
    (w : Sp (DualNumber R) ⟶ t.G.left) :
    spMap (dualMap ψ) ≫ spMap (dualMap φ) ≫ w = spMap (dualMap (ψ.comp φ)) ≫ w := by
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← Formalism.L2.Pj.dualMap_comp]

theorem isTanBasis_map {R S : Type} [CommRing R] [CommRing S] {x : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : GlobalTheory.LineNorm.IsTanBasis t x e) (φ : R →+* S) :
    GlobalTheory.LineNorm.IsTanBasis t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) := by
  refine ⟨fun i => GlobalTheory.FactorDepth.isTanAtG_map t φ (h.1 i), fun T _ ψ w hw => ?_⟩
  simp only [bc_bc]
  rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap] at hw ⊢
  exact h.2 T (ψ.comp φ) w hw

theorem ext_uniq (hX : X.IsSeparated) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    (x y : Sp ↥(intO C) ⟶ X) (h : spMap (intO C).subtype ≫ y = spMap (intO C).subtype ≫ x) : y = x := by
  have : IsDominant (spMap (intO C).subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (intO C).subtype_injective).le.trans bot_le)⟩
  exact ext_of_isDominant _ h

theorem mem_latDR_iff (hX : X.IsSeparated) {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : GlobalTheory.LineNorm.IsTanBasis t x e) (C : Type)
    [NontriviallyNormedField C] [IsUltrametricDist C] (φ : R →+* ↥(intO C)) (cf : Fin g → C)
    (w : Sp (DualNumber C) ⟶ t.G.left)
    (hw : IsCombAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) cf w) :
    w ∈ latDR t (spMap (intO C).subtype ≫ spMap φ ≫ x) ↔ ∀ i, ‖cf i‖ ≤ 1 := by
  have hb := isTanBasis_map t he φ
  have hv : ∀ i, IsTanAtG t (spMap (intO C).subtype ≫ spMap φ ≫ x)
      (spMap (dualMap ((intO C).subtype.comp φ)) ≫ e i) := fun i => by
    rw [← bc_bc]; exact GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype (hb.1 i)
  have hxC : spMap (intO C).subtype ≫ spMap φ ≫ x = spMap ((intO C).subtype.comp φ) ≫ x := by
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap]
  constructor
  · rintro ⟨xO, hx, vO, hvO, rfl⟩ i
    obtain rfl := ext_uniq hX C _ _ hx
    obtain ⟨a, ha, -⟩ := he.2 (↥(intO C)) φ vO hvO
    have hc := GlobalTheory.LatDRFree.comb_map t (intO C).subtype ha
    simp only [bc_bc] at hc
    have ht := GlobalTheory.FactorDepth.isTanAtG_map t (intO C).subtype hvO
    rw [hxC] at ht hc hw
    have e1 := (he.2 C _ _ ht).unique hw hc
    rw [e1]
    exact (a i).2
  · intro hc
    obtain ⟨wO, hwO, hcO⟩ := GlobalTheory.FlagEmb.exists_comb t hb.1 fun i => (⟨cf i, hc i⟩ : ↥(intO C))
    refine ⟨_, rfl, wO, hwO, ?_⟩
    have hb' := GlobalTheory.LatDRFree.comb_map t (intO C).subtype hcO
    simp only [bc_bc] at hb'
    exact GlobalTheory.FlagEmb.comb_unique t hv hb' hw

theorem sum_single {R C : Type} [CommRing R] [NontriviallyNormedField C] [IsUltrametricDist C] {g : ℕ}
    (φ : R →+* ↥(intO C)) (i : Fin g) (a : R) (cf : Fin g → C) :
    ∑ k, ((φ ((Pi.single i a : Fin g → R) k) : ↥(intO C)) : C) * cf k = (φ a : C) * cf i := by
  rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp)]
  simp

end GlobalTheory.HTPres

namespace GlobalTheory.HTPres

theorem exists_pres : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) [IsLocallyNoetherian X], X.IsSeparated → ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X), (∃ ζ : R, IsPrimitiveRoot ζ p) → GlobalTheory.LineNorm.SplitTors t x p → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∀ b : Bool, ∃ (M : ℕ) (h : Fin (M + 1) → Fin g → R), Pres t x p b e h := by
  intro hB E _ _ _ H X t _ hX p hp R _ _ _ _ x hζ hS g e he b
  cases b with
  | false =>
    refine ⟨g, Fin.cons 0 (fun i => Pi.single i 1), ⟨0, fun i => ?_⟩, fun C φ cf w hw => ?_⟩
    · rw [pow_zero]
      exact Submodule.subset_span ⟨i.succ, by simp⟩
    · change w ∈ latDR t _ ↔ _
      rw [mem_latDR_iff t hX x he C.S φ cf w hw, Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, sum_single, map_one]
      simp
  | true =>
    obtain ⟨n, h', hh'⟩ := GlobalTheory.T.exists_tangent_presentation_prime E H X t R x g e he p hp hζ hS
    refine ⟨n + g, Fin.cons 0 (Fin.append h' fun i => Pi.single i (p : R)), ⟨1, fun i => ?_⟩, fun C φ cf w hw => ?_⟩
    · rw [pow_one]
      exact Submodule.subset_span ⟨(Fin.natAdd n i).succ, by simp⟩
    · haveI := Fact.mk hp
      have hw' : IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
          (fun i => spMap (dualMap (intO ↥C.S).subtype) ≫ spMap (dualMap φ) ≫ e i) cf w := by
        simpa only [bc_bc] using hw
      change w ∈ latHT t p _ ↔ _
      rw [GlobalTheory.T.unique_integral_lift_norm_p_inverse hB E H X t p ↥C.S C.norm_p (spMap φ ≫ x)
        (fun x' hx' => ext_uniq hX _ _ _ hx') g _ (isTanBasis_map t he φ) n (fun j i => φ (h' j i))
        (hh' ↥C.S φ).1 (hh' ↥C.S φ).2 cf w hw', Fin.forall_fin_succ, Fin.forall_fin_add]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.append_left, Fin.append_right, sum_single, map_natCast]
      simp [norm_mul]

end GlobalTheory.HTPres
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_basis_of_split_torsion : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) [IsLocallyNoetherian X], X.IsSeparated → ∀ (p : ℕ), p.Prime → ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ X), (∃ ζ : R, IsPrimitiveRoot ζ p) → GlobalTheory.LineNorm.SplitTors t x p → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)), GlobalTheory.LineNorm.IsTanBasis t x e → ∀ b : Bool, ∃ (M : ℕ) (h : Fin (M + 1) → Fin g → R), Pres t x p b e h := by
  first | exact @GlobalTheory.HTPres.exists_pres | exact GlobalTheory.HTPres.exists_pres | (intros; apply GlobalTheory.HTPres.exists_pres <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_valuation_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (b : Z.i.c.V W →+* Γ(Z.X, U)), hU.fromSpec ≫ Z.s = spMap b → ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (a : 𝓞 E) (h : embK Z.i.c τ a ∈ Z.i.c.V W), w τ i ≫ ((Y Z.i).t.act.act a).left = spMap (epsMul (b ⟨_, h⟩)) ≫ w τ i := by
  first | exact @GlobalTheory.HTLine.eig_of_intFrame | exact GlobalTheory.HTLine.eig_of_intFrame | (intros; apply GlobalTheory.HTLine.eig_of_intFrame <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HTLine.GenInd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem embK_mem {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (τ : E →+* ℂ) (a : 𝓞 E) :
    embK c τ a ∈ c.V W := by
  show ((embK c τ a : c.F) : ℂ) ∈ W
  rw [embK_coe]
  have h1 : IsIntegral ℤ (τ (a : E)) := (NumberField.RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
  have h2 : IsIntegral W (τ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

theorem natCast_mem_max {l : Level H} (c : Coeff l) {W : ValuationSubring ℂ} {p : ℕ} (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.V W) ∈ IsLocalRing.maximalIdeal (c.V W) := by
  obtain ⟨h0, h1⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal).1 hW
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
  intro hu
  let g : c.V W →+* W := (c.F.val.toRingHom.comp (c.V W).subtype).codRestrict W (fun x => x.2)
  apply h1
  have := hu.map g
  rw [map_natCast] at this
  convert this using 1
  exact Subtype.ext (by simp)

theorem exists_ext {F : Type} [Field F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ)
    (hp : (p : V) ∈ IsLocalRing.maximalIdeal V) {k : Type} [Field k] (g : V →+* k) (hk : (p : k) ≠ 0) :
    ∃ f : F →+* k, ∀ v : V, f v = g v := by
  have hker : RingHom.ker g = ⊥ := by
    by_contra h
    have hm : (RingHom.ker g).IsMaximal := Ideal.IsPrime.isMaximal (RingHom.ker_isPrime g) h
    have he := IsLocalRing.eq_maximalIdeal hm
    apply hk
    have : (p : V) ∈ RingHom.ker g := he ▸ hp
    simpa using this
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun x hx => by
    have : x ∈ RingHom.ker g := hx
    rwa [hker] at this
  exact ⟨IsFractionRing.lift hinj, fun v => IsFractionRing.lift_algebraMap (K := F) hinj v⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem dualMap_epsMul {R k : Type} [CommRing R] [CommRing k] (ψ : R →+* k) (r : R) :
    (dualMap ψ).comp (epsMul r) = (epsMul (ψ r)).comp (dualMap ψ) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

variable {X : Scheme.{0}} {t : SAB H X}

theorem ind_of_basis {R k : Type} [CommRing R] [Field k] {x : Sp R ⟶ X} {n m : ℕ}
    {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (hv : GlobalTheory.LineNorm.IsTanBasis t x v) (e : Fin m ↪ Fin n)
    (ψ : R →+* k) : Pull.Ind t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ v (e i)) := by
  classical
  have hT : ∀ j, IsTanAtG t (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v j) := fun j => GlobalTheory.LieMet.isTan_map ψ rfl (hv.1 j)
  refine ⟨fun i => hT (e i), fun cf cf' w h h' => ?_⟩
  let V : Fin n → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap ψ ≫ x) t.G := fun j => GlobalTheory.LieMet.tanOf (hT j)
  have hs : ∀ d : Fin m → k, ∑ j, Function.extend e d 0 j • V j = ∑ i, d i • V (e i) := fun d => by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (fun j _ hj => by
      rw [Function.extend_apply' _ _ _ (fun ⟨i, hi⟩ => hj (Finset.mem_map.2 ⟨i, Finset.mem_univ _, hi⟩)),
        Pi.zero_apply, zero_smul]), Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by rw [e.injective.extend_apply]
  have hc : ∀ d, IsCombAtG t (spMap ψ ≫ x) (fun i => spMap (dualMap ψ) ≫ v (e i)) d w →
      IsCombAtG t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ v j) (Function.extend e d 0) w := fun d hd => by
    have h1 := (Pull.comb_iff (fun i => V (e i)) d w).1 hd
    exact (Pull.comb_iff V _ w).2 (by rw [hs]; exact h1)
  have hw : IsTanAtG t (spMap ψ ≫ x) w := by
    rw [(Pull.comb_iff (fun i => V (e i)) cf w).1 h]; exact GlobalTheory.LieMet.isTan_tv _
  have := (hv.2 k ψ w hw).unique (hc cf h) (hc cf' h')
  funext i
  have h2 := congrFun this (e i)
  rwa [e.injective.extend_apply, e.injective.extend_apply] at h2

theorem ind_concat {Dw : Datum H} {l : Level H} (c : Coeff l) {k : Type} [Field k] (f : c.F →+* k) {x : Sp k ⟶ X}
    (u : Vecs Dw t k) (hE : ∀ τ i (a : 𝓞 E), u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i)
    (hI : ∀ τ, Pull.Ind t x (u τ)) :
    Pull.Ind t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  classical
  refine ⟨fun i => (hI _).1 _, fun cf cf' w h h' => ?_⟩
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G := fun y => GlobalTheory.LieMet.tanOf ((hI y.1).1 y.2)
  let e := Equiv.ofBijective _ (GlobalTheory.Proof.frame_combination_coeff_unique.get_bijective Dw)
  have hc : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      cf w ↔ w = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (∑ y, cf (e.symm y) • U y)).left := fun cf w => by
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U (e i)) cf w
  have hτ : ∀ τ cf w, IsCombAtG t x (u τ) cf w ↔ w = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (∑ i, cf i • U ⟨τ, i⟩)).left :=
    fun τ cf w => GlobalTheory.Proof.frame_combination_coeff_unique.comb_iff (fun i => U ⟨τ, i⟩) cf w
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := k) t.act
  have hEv : ∀ τ (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x t.G), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left ≫ (t.act.act a).left =
        spMap (epsMul (f (embK c τ a))) ≫ (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left := fun τ v =>
    forall_congr' fun a => ⟨fun h => congrArg (fun z => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv z).left) h,
      fun h => GlobalTheory.LieMet.tan_ext h⟩
  have hS : ∀ τ (a : Fin (Dw.mult τ) → k), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • U ⟨τ, i⟩) :=
    fun τ a s => by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hEv τ (U ⟨τ, i⟩)).2 (hE τ i) s, smul_comm]
  have h1 := GlobalTheory.LieMet.tan_ext (((hc cf w).1 h).symm.trans ((hc cf' w).1 h'))
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
  funext i
  obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective i
  have h2 := congrArg (ReciprocityTheory.ChartRestriction.G.PullbackSections.proj ρ (embK c) α τ) h1
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _)] at h2
  exact congrFun ((hI τ).2 _ _ _ ((hτ τ _ _).2 rfl)
    ((hτ τ _ _).2 (congrArg (fun z => (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv z).left) h2))) i

end GlobalTheory.HTLine.GenInd

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.HTLine.GenInd.ind_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (k : Type) [Field k] (ψ : Γ(Z.X, U) →+* k), (p : k) ≠ 0 → (∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ)) ∧ Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (fun i : Fin (letters Dw).length => w.bc ψ ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW Z U hU w hw k _ ψ hk
  obtain ⟨b, hb⟩ : ∃ b : Z.i.c.V W →+* Γ(Z.X, U), hU.fromSpec ≫ Z.s = spMap b := by
    refine ⟨(Spec.preimage (hU.fromSpec ≫ Z.s)).hom, ?_⟩
    exact (Spec.map_preimage (hU.fromSpec ≫ Z.s)).symm
  have := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff (W := W) Z.i.c hp.ne_zero hW
  obtain ⟨f, hf⟩ := GlobalTheory.HTLine.GenInd.exists_ext (Z.i.c.V W) p (GlobalTheory.HTLine.GenInd.natCast_mem_max Z.i.c hW) (ψ.comp b) hk
  have hE : ∀ τ i (a : 𝓞 E), w.bc ψ τ i ≫ ((Y Z.i).t.act.act a).left =
      spMap (epsMul (f (embK Z.i.c τ a))) ≫ w.bc ψ τ i := by
    intro τ i a
    have h := GlobalTheory.HTLine.GenInd.embK_mem Z.i.c W τ a
    have h1 := GlobalTheory.T.integral_frame_valuation_bound E H Dw Xo p W Y i₀ Z U hU w hw b hb τ i a h
    have h2 : f (embK Z.i.c τ a) = ψ (b ⟨_, h⟩) := hf ⟨_, h⟩
    show spMap (dualMap ψ) ≫ w τ i ≫ _ = spMap (epsMul _) ≫ spMap (dualMap ψ) ≫ w τ i
    rw [h1, h2, ← Category.assoc, ← Category.assoc, GlobalTheory.HTLine.GenInd.spMap_comp',
      GlobalTheory.HTLine.GenInd.spMap_comp', GlobalTheory.HTLine.GenInd.dualMap_epsMul]
  have hI : ∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ) := by
    intro τ
    obtain ⟨n, v, e, hve, hvt, hvu⟩ := hw.1 τ
    have hB := GlobalTheory.T.isTanBasis_of_unique_combination E H _ (Y Z.i).t _ (hU.fromSpec ≫ Z.π) n v hvt hvu
    have h3 := GlobalTheory.HTLine.GenInd.ind_of_basis hB e ψ
    simp only [hve] at h3
    exact h3
  refine ⟨hI, ?_⟩
  exact GlobalTheory.HTLine.GenInd.ind_concat (t := (Y Z.i).t) (x := spMap ψ ≫ hU.fromSpec ≫ Z.π) (Dw := Dw) Z.i.c f (w.bc ψ) hE hI
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_frame_residue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (U : Z.X.Opens) (hU : IsAffineOpen U) (w : Vecs Dw (Y Z.i).t Γ(Z.X, U)), IntFrame Z hU w → ∀ (k : Type) [Field k] (ψ : Γ(Z.X, U) →+* k), (p : k) ≠ 0 → (∀ τ, Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (w.bc ψ τ)) ∧ Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (fun i : Fin (letters Dw).length => w.bc ψ ((letters Dw).get i).1 ((letters Dw).get i).2) := by
  atlas_forward_decl GlobalTheory.HTLine.GenInd.ind_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm

theorem exists_ne {L : Type} [Field L] {g J : ℕ} (h : Fin J → Fin g → L)
    (hh : ∀ c : Fin g → L, (∀ j, ∑ i, h j i * c i = 0) → c = 0) {m : ℕ} (a : Fin m → Fin g → L)
    (ha : LinearIndependent L a) {k : ℕ} (hk : k ≤ m) :
    ∃ σ : Fin k → Fin J, ∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s ≠ 0 := by
  let G : Matrix (Fin J) (Fin m) L := Matrix.of fun j l => ∑ t, h j t * a l t
  have hli : LinearIndependent L G.transpose := by
    have hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥ :=
      LinearMap.ker_eq_bot'.mpr fun c hc => hh c fun j => congrFun hc j
    exact ha.map' _ hker
  obtain ⟨κ, u, b, -, hu0, hu1, hb, hbd, hc⟩ := GlobalTheory.LineNorm.Covol.exists_pivot (⊤ : ValuationSubring L) G hli
  refine ⟨κ ∘ Fin.castLE hk, ?_⟩
  rw [GlobalTheory.LineNorm.Covol.sum_prod_mul_minor (fun i => h ((κ ∘ Fin.castLE hk) i)) a hk, ← Matrix.det_transpose]
  change (G.submatrix (κ ∘ Fin.castLE hk) (Fin.castLE hk)).det ≠ 0
  rw [hc, GlobalTheory.LineNorm.Covol.det_eq u b hb hk]
  have hMt : (u.submatrix (κ ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual :=
    fun i j hij => hu0 _ _ hij
  rw [Matrix.det_of_isLowerTriangular _ hMt]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun l _ => hbd _)
  simp [hu1]

theorem sep_of_span {R S : Type} [CommRing R] [Field S] (ψ : R →+* S) (p : ℕ) (hp : (p : S) ≠ 0) {g J : ℕ}
    (h : Fin J → Fin g → R) (N : ℕ) (hN : ∀ i, Pi.single i ((p : R) ^ N) ∈ Submodule.span R (Set.range h))
    (c : Fin g → S) (hc : ∀ j, ∑ i, ψ (h j i) * c i = 0) : c = 0 := by
  have key : ∀ v ∈ Submodule.span R (Set.range h), ∑ i, ψ (v i) * c i = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hc j
    | zero => simp
    | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
    | smul r x _ hx =>
      calc ∑ i, ψ ((r • x) i) * c i = ψ r * ∑ i, ψ (x i) * c i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by simp <;> ring
        _ = 0 := by rw [hx, mul_zero]
  funext i
  have h1 := key _ (hN i)
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)] at h1
  simpa [hp] using h1

theorem norm_eq_iSup {κ : Type} [Fintype κ] [Nonempty κ] {S : Type} [NormedField S] (f : κ → S) :
    ‖f‖ = ⨆ i, ‖f i‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg ?_).2 fun i => le_ciSup (f := fun i => ‖f i‖) (Finite.bddAbove_range _) i)
    (ciSup_le fun i => norm_le_pi_norm f i)
  exact (norm_nonneg (f (Classical.arbitrary κ))).trans (le_ciSup (f := fun i => ‖f i‖) (Finite.bddAbove_range _) _)

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : ψ (minor a hk s) = minor (fun l i => ψ (a l i)) hk s := by
  unfold minor
  rw [RingHom.map_det]
  rfl

end GlobalTheory.HTLine.GrMinor

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (u i)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ i, a i • tanOf (hu i))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ i, a i • tanOf (hu i))).left := (isComb_iff (fun i => tanOf (hu i)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨v, hv, e⟩ := h
  obtain ⟨v', hv', e'⟩ := h0
  have : v = v' := funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)
  rw [← e, ← e', this]

theorem comb_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {w : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j))
    (a : Fin m → Fin g → S) (ha : ∀ j, IsCombAtG t x e (a j) (w j)) (cf : Fin m → S)
    (v : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x w cf v ↔ IsCombAtG t x e (fun r => ∑ l, cf l * a l r) v := by
  have hW : ∀ j, tanOf (hw j) = ∑ r, a j r • tanOf (he r) := fun j => tan_ext ((comb_eq he _ _).1 (ha j))
  rw [comb_eq hw, comb_eq he]
  have : ∑ l, cf l • tanOf (hw l) = ∑ r, (∑ l, cf l * a l r) • tanOf (he r) := by
    simp only [hW, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [this]

theorem linIndep_of_ind {k : Type} [Field k] {x : Sp k ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber k) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {w : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} (hw : Pull.Ind t x w)
    (a : Fin m → Fin g → k) (ha : ∀ j, IsCombAtG t x e (a j) (w j)) : LinearIndependent k a := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : ∀ r, ∑ l, c l * a l r = ∑ l, (0 : Fin m → k) l * a l r := fun r => by
    have := congrFun hc r
    simpa [Finset.sum_apply] using this
  have h1 : IsCombAtG t x w c (tv (∑ l, c l • tanOf (hw.1 l))).left := (comb_eq hw.1 _ _).2 rfl
  have h2 : IsCombAtG t x w 0 (tv (∑ l, c l • tanOf (hw.1 l))).left := by
    rw [comb_comb he hw.1 a ha] at h1 ⊢
    rw [show (fun r => ∑ l, c l * a l r) = (fun r => ∑ l, (0 : Fin m → k) l * a l r) from funext h0] at h1
    exact h1
  exact congrFun (hw.2 _ _ _ h1 h2)

theorem coords {R : Type} [CommRing R] {x : Sp R ⟶ X} {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)}
    (he : IsTanBasis t x e) {m : ℕ} {w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j)) :
    ∃ a : Fin m → Fin g → R, ∀ j, IsCombAtG t x e (a j) (w j) := by
  have h1 : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have h := he.2 R (RingHom.id R)
  simp only [h1, h3, Category.id_comp] at h
  choose a ha using fun j => (h (w j) (hw j)).exists
  exact ⟨a, ha⟩

end GlobalTheory.HTLine.GrMinor

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm GlobalTheory.LieMet

theorem grNorm_eq_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : ℕ) (b : Bool) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin (M + 1) → Fin g → R), p.Prime → GlobalTheory.LineNorm.IsTanBasis t x e → Pres t x p b e h → ∀ (m : ℕ) (w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)), (∀ j, IsTanAtG t x (w j)) → (∀ (k : Type) [Field k] (ψ : R →+* k), (p : k) ≠ 0 → Pull.Ind t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ w j)) → ∀ i : Fin m, ∃ (a a' : ℕ) (A : Fin a → R) (B : Fin a' → R), (p : R) ∈ (Ideal.span (Set.range A)).radical ∧ (p : R) ∈ (Ideal.span (Set.range B)).radical ∧ ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)), GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ w j) i * ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ := by
  intro E _ _ _ H X t R _ x p b g M e h hp he hP m w hw hind i
  obtain ⟨a, ha⟩ := coords he hw
  obtain ⟨N, hN⟩ := hP.1
  let F : ∀ k, k ≤ m → (Fin k → Fin (M + 1)) → R := fun k hk σ =>
    ∑ s : Fin k → Fin g, (∏ l, h (σ l) (s l)) * minor a hk s
  have hrad : ∀ k (hk : k ≤ m),
      (p : R) ∈ (Ideal.span (Set.range fun j => F k hk ((Fintype.equivFin _).symm j))).radical := by
    intro k hk
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro (P : Ideal R) ⟨hle, hPr⟩
    by_contra hpP
    haveI := hPr
    have hp0 : ((p : ℕ) : P.ResidueField) ≠ 0 := by
      rw [← map_natCast (algebraMap R P.ResidueField)]
      exact fun h0 => hpP (Ideal.algebraMap_residueField_eq_zero.1 h0)
    have hI := hind P.ResidueField (algebraMap R P.ResidueField) hp0
    have he' : ∀ r, IsTanAtG t (spMap (algebraMap R P.ResidueField) ≫ x)
        (spMap (dualMap (algebraMap R P.ResidueField)) ≫ e r) := fun r => isTan_map _ rfl (he.1 r)
    have ha' := fun j => GlobalTheory.LatDRFree.comb_map t (algebraMap R P.ResidueField) (ha j)
    have hli := linIndep_of_ind he' hI _ ha'
    obtain ⟨σ, hσ⟩ := exists_ne (fun j r => algebraMap R P.ResidueField (h j r))
      (sep_of_span _ p hp0 h N hN) _ hli hk
    apply hσ
    have hmem : F k hk σ ∈ P := hle (Ideal.subset_span ⟨Fintype.equivFin _ σ, by simp⟩)
    calc _ = algebraMap R P.ResidueField (F k hk σ) := by
          simp only [F, map_sum, map_mul, map_prod, map_minor]
      _ = 0 := Ideal.algebraMap_residueField_eq_zero.2 hmem
  refine ⟨_, _, fun j => F (i + 1) (Nat.succ_le_of_lt i.2) ((Fintype.equivFin _).symm j),
    fun j => F i i.2.le ((Fintype.equivFin _).symm j), hrad _ _, hrad _ _, fun C φ => ?_⟩
  set ψ : R →+* ↥C.S := (intO ↥C.S).subtype.comp φ with hψ
  have hx : spMap ψ ≫ x = spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hp0 : ((p : ℕ) : ↥C.S) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have he' : ∀ r, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (spMap (dualMap ψ) ≫ e r) :=
    fun r => isTan_map ψ hx (he.1 r)
  have hw' : ∀ l, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (spMap (dualMap ψ) ≫ w l) :=
    fun l => isTan_map ψ hx (hw l)
  have ha' : ∀ l, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (fun r => spMap (dualMap ψ) ≫ e r)
      (fun r => ψ (a l r)) (spMap (dualMap ψ) ≫ w l) := fun l => hx ▸ GlobalTheory.LatDRFree.comb_map t ψ (ha l)
  have hI := hind ↥C.S ψ hp0
  rw [hx] at hI
  have hli := linIndep_of_ind he' hI _ ha'
  have hsep := sep_of_span ψ p hp0 h N hN
  let Nf : Fin m → ℝ := fun l => grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
    (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ψ) ≫ w j) l
  have hset : ∀ l, Nf l = sInf {r | ∃ cf : Fin m → ↥C.S, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧
      (∀ j, ‖∑ i, ψ (h j i) * ∑ l', cf l' * ψ (a l' i)‖ ≤ 1) ∧ r = ‖cf l‖⁻¹} := by
    intro l
    simp only [Nf, grNorm]
    congr 1
    ext r
    refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
    constructor
    · rintro ⟨v, hv, hc⟩
      exact (hP.2 C φ _ v ((comb_comb he' hw' _ ha' cf v).1 hc)).1 hv
    · intro hn
      have hc := (comb_eq hw' cf _).2 rfl
      exact ⟨_, (hP.2 C φ _ _ ((comb_comb he' hw' _ ha' cf _).1 hc)).2 hn, hc⟩
  obtain ⟨-, hprod⟩ := GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor ↥C.S g (Fin (M + 1)) (fun j r => ψ (h j r))
    hsep m (fun l r => ψ (a l r)) hli Nf hset
  have hnorm : ∀ k (hk : k ≤ m), ‖fun j => ((φ (F k hk ((Fintype.equivFin _).symm j)) : ↥(intO ↥C.S)) : ↥C.S)‖ =
      ∏ l : Fin k, Nf (Fin.castLE hk l) := by
    intro k hk
    haveI : Nonempty (Fin (Fintype.card (Fin k → Fin (M + 1)))) := ⟨Fintype.equivFin _ (fun _ => 0)⟩
    rw [norm_eq_iSup, hprod k hk]
    refine ((Fintype.equivFin _).symm.iSup_comp (g := fun σ => ‖ψ (F k hk σ)‖)).trans ?_
    congr 1
    funext σ
    simp only [F, map_sum, map_mul, map_prod, map_minor]
  rw [hnorm, hnorm, Fin.prod_univ_castSucc, mul_comm]
  rfl

end GlobalTheory.HTLine.GrMinor
end

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.presentation_tangent_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : ℕ) (b : Bool) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin (M + 1) → Fin g → R), p.Prime → GlobalTheory.LineNorm.IsTanBasis t x e → Pres t x p b e h → ∀ (m : ℕ) (w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)), (∀ j, IsTanAtG t x (w j)) → (∀ (k : Type) [Field k] (ψ : R →+* k), (p : k) ≠ 0 → Pull.Ind t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ w j)) → ∀ i : Fin m, ∃ (a a' : ℕ) (A : Fin a → R) (B : Fin a' → R), (p : R) ∈ (Ideal.span (Set.range A)).radical ∧ (p : R) ∈ (Ideal.span (Set.range B)).radical ∧ ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)), GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ w j) i * ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ := by
  atlas_forward_decl GlobalTheory.HTLine.GrMinor.grNorm_eq_ratio
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine.Ratio

attribute [local instance] Over.cartesianMonoidalCategory

section Fam

def pf {R : Type} [Mul R] {m n : ℕ} (A : Fin m → R) (B : Fin n → R) : Fin (m * n) → R :=
  fun q => A (finProdFinEquiv.symm q).1 * B (finProdFinEquiv.symm q).2

theorem pf_pair {R : Type} [Mul R] {m n : ℕ} (A : Fin m → R) (B : Fin n → R) (i : Fin m) (j : Fin n) :
    pf A B (finProdFinEquiv (i, j)) = A i * B j := by
  simp [pf]

theorem exists_norm_eq {C : Type} [NormedField C] {m : ℕ} [NeZero m] (x : Fin m → C) : ∃ i, ‖x‖ = ‖x i‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖x i‖) ⟨0, Finset.mem_univ _⟩
  exact ⟨i, le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ _))
    (norm_le_pi_norm x i)⟩

theorem norm_pf {C : Type} [NormedField C] {m n : ℕ} (x : Fin m → C) (y : Fin n → C) : ‖pf x y‖ = ‖x‖ * ‖y‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun q => ?_) ?_
  · rw [pf, norm_mul]
    exact mul_le_mul (norm_le_pi_norm x _) (norm_le_pi_norm y _) (norm_nonneg _) (norm_nonneg _)
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · have : ‖x‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      rw [this, zero_mul]; exact norm_nonneg _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : ‖y‖ = 0 := by rw [norm_eq_zero]; exact Subsingleton.elim _ _
      rw [this, mul_zero]; exact norm_nonneg _
    haveI : NeZero m := ⟨hm.ne'⟩
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨i, hi⟩ := exists_norm_eq x
    obtain ⟨j, hj⟩ := exists_norm_eq y
    rw [hi, hj, ← norm_mul, ← pf_pair]
    exact norm_le_pi_norm _ _

theorem radical_pf {R : Type} [CommRing R] {m n : ℕ} {A : Fin m → R} {B : Fin n → R} {r : R}
    (hA : r ∈ (Ideal.span (Set.range A)).radical) (hB : r ∈ (Ideal.span (Set.range B)).radical) :
    r ∈ (Ideal.span (Set.range (pf A B))).radical := by
  have e : Ideal.span (Set.range (pf A B)) = Ideal.span (Set.range A) * Ideal.span (Set.range B) := by
    rw [Ideal.span_mul_span']
    congr 1
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact Set.mul_mem_mul ⟨_, rfl⟩ ⟨_, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      exact ⟨finProdFinEquiv (i, j), pf_pair A B i j⟩
  rw [e, Ideal.radical_mul]
  exact ⟨hA, hB⟩

theorem norm_pos_of_radical {R C : Type} [CommRing R] [NormedField C] [CharZero C] (χ : R →+* C) {p : ℕ} (hp : p ≠ 0)
    {m : ℕ} {A : Fin m → R} (h : (p : R) ∈ (Ideal.span (Set.range A)).radical) : 0 < ‖fun j => χ (A j)‖ := by
  refine lt_of_le_of_ne (norm_nonneg _) fun e => ?_
  have h0 : ∀ j, χ (A j) = 0 := fun j => congrFun (norm_eq_zero.1 e.symm) j
  obtain ⟨n, hn⟩ := h
  have : (p : R) ^ n ∈ RingHom.ker χ := Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact h0 j) hn
  rw [RingHom.mem_ker, map_pow, map_natCast] at this
  exact pow_ne_zero n (Nat.cast_ne_zero.2 hp : (p : C) ≠ 0) this

theorem comp_pf {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {m n : ℕ} (A : Fin m → R) (B : Fin n → R) :
    (fun q => ψ (pf A B q)) = pf (fun j => ψ (A j)) (fun j => ψ (B j)) := by
  funext q
  simp [pf]

theorem comp_single {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (a : R) :
    (fun j => ψ ((![a] : Fin 1 → R) j)) = ![ψ a] := by
  funext j
  fin_cases j
  rfl

theorem norm_single {C : Type} [NormedField C] (c : C) : ‖(![c] : Fin 1 → C)‖ = ‖c‖ := by
  have : (![c] : Fin 1 → C) = fun _ => c := by
    funext j
    fin_cases j
    rfl
  rw [this, pi_norm_const]

theorem log_ratio {g₁ b₁ a₁ g₀ b₀ a₀ s c : ℝ} (hb₁ : 0 < b₁) (ha₁ : 0 < a₁) (hb₀ : 0 < b₀) (ha₀ : 0 < a₀) (hs : 0 < s)
    (h₁ : g₁ * b₁ = a₁) (h₀ : g₀ * b₀ = a₀) (hc : Real.log s = -c) :
    (Real.log g₁ - c) - (Real.log g₀ - 0) = Real.log (s * a₁ * b₀) - Real.log (b₁ * a₀) := by
  have n₁ : g₁ ≠ 0 := fun e => ha₁.ne' (by rw [← h₁, e, zero_mul])
  have n₀ : g₀ ≠ 0 := fun e => ha₀.ne' (by rw [← h₀, e, zero_mul])
  have e₁ : Real.log g₁ + Real.log b₁ = Real.log a₁ := by rw [← h₁, Real.log_mul n₁ hb₁.ne']
  have e₀ : Real.log g₀ + Real.log b₀ = Real.log a₀ := by rw [← h₀, Real.log_mul n₀ hb₀.ne']
  rw [Real.log_mul (mul_pos hs ha₁).ne' hb₀.ne', Real.log_mul hs.ne' ha₁.ne', Real.log_mul hb₁.ne' ha₀.ne']
  linarith

end Fam

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

open GlobalTheory.ShFam.Pad.Pull

theorem gen_eq {Z : Mdl Y i₀} {U : Z.X.Opens} (hU : IsAffineOpen U) (y : Z.Pt) {χ : Γ(Z.X, U) →+* ↥(intO ↥y.C.S)}
    (hχ : spMap χ ≫ hU.fromSpec = y.z) : spMap ((intO ↥y.C.S).subtype.comp χ) ≫ hU.fromSpec = y.gen := by
  rw [Mdl.Pt.gen, ← hχ, ← GlobalTheory.ModelRelProbe.spMap_comp, Category.assoc]

theorem diff_frame (hB : HTBoundSt) (hp : p.Prime) (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ)
    {U : Z.X.Opens} (hU : IsAffineOpen U) {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} (hw : IntFrame Z hU w) (y : Z.Pt)
    (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S) (hφ : spMap φ ≫ Z.chart a = y.gen)
    (χ : Γ(Z.X, U) →+* ↥(intO ↥y.C.S)) (hχ : spMap χ ≫ hU.fromSpec = y.z)
    {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (hx : letterOf Dw st = some x) :
    lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p true st -
        lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p false st =
      lnStep (Y Z.i).t (y.gen ≫ Z.π) (w.bc ((intO ↥y.C.S).subtype.comp χ)) p true st -
        lnStep (Y Z.i).t (y.gen ≫ Z.π) (w.bc ((intO ↥y.C.S).subtype.comp χ)) p false st := by
  have hgen := gen_eq hU y hχ
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = (intO ↥y.C.S).subtype.comp χ := ⟨_, rfl⟩
  rw [← hψ] at hgen ⊢
  obtain ⟨a₁, φ₁, h₁, hF, hS⟩ := hw.2 _ ψ (hgen ▸ range_opn Z hφ)
  rw [hgen] at h₁ hF hS
  have := mono_spMap_subtype (Z.i.c.V W)
  have hf : φ₁.comp (Z.alg a₁) = φ.comp (Z.alg a) := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (a₁ := CommRingCat.ofHom _) (a₂ := CommRingCat.ofHom _) ?_)
    rw [← cancel_mono (spMap (Z.i.c.V W).subtype)]
    exact (affineOpenChart_comp_structure_eq_spMap Z h₁).symm.trans (affineOpenChart_comp_structure_eq_spMap Z hφ)
  rw [hf] at hF
  have hu := chart_frame Z hφ
  have hT : ∀ τ, Tri (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ τ) (w.bc ψ τ) := fun τ =>
    Tri.trans (fun i => (chart_frame Z hφ).1 τ i |>.1) (fun i => (chart_frame Z h₁).1 τ i |>.1)
      (chart_tri Z hty hφ h₁ τ) (tri_of_sameFlag hty hS τ)
  obtain ⟨cf, -, hc⟩ := hT x.1 x.2
  have hxe : y.gen ≫ Z.π = spMap (intO ↥y.C.S).subtype ≫ y.z ≫ Z.π := Category.assoc _ _ _
  rw [hxe] at hu hF hT hc ⊢
  have key := fun b => lnStep_tri (p := p) hB hp y.C b (y.z ≫ Z.π) (fun q hq => ext_unique Z.i _ _ hq) hu hF hT hx hc
  rw [key true, key false]
  ring

theorem exists_ratio (hB : HTBoundSt) (hp : p.Prime) (Z : Mdl Y i₀) (hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ)
    {U : Z.X.Opens} (hU : IsAffineOpen U) {w : Vecs Dw (Y Z.i).t Γ(Z.X, U)} (hw : IntFrame Z hU w)
    {st : ((E →+* ℂ) × ℕ) ⊕ ℕ} {x : Letter Dw} (hx : letterOf Dw st = some x) {n : ℕ}
    (fam : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)) (i : Fin n) (c : ℝ) (a : Γ(Z.X, U))
    (ha : (p : Γ(Z.X, U)) ∈ (Ideal.span {a}).radical)
    (hc : ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)), Real.log ‖((φ a : ↥(intO ↥C.S)) : ↥C.S)‖ = -c)
    (hst : ∀ (y : Z.Pt) (b : Bool) (ψ : Γ(Z.X, U) →+* ↥y.C.S),
      lnStep (Y Z.i).t (y.gen ≫ Z.π) (w.bc ψ) p b st =
        Real.log (grNorm (Y Z.i).t (y.gen ≫ Z.π) (lat (Y Z.i).t p (y.gen ≫ Z.π) b)
          (fun j => spMap (dualMap ψ) ≫ fam j) i) - (if b then c else 0))
    (hg : ∀ b : Bool, ∃ (a₁ a₂ : ℕ) (A : Fin a₁ → Γ(Z.X, U)) (B : Fin a₂ → Γ(Z.X, U)),
      (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range A)).radical ∧ (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range B)).radical ∧
      ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)),
        grNorm (Y Z.i).t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π)
          (lat (Y Z.i).t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π) b)
          (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ fam j) i *
            ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖) :
    ∃ (m m' : ℕ) (A : Fin m → Γ(Z.X, U)) (B : Fin m' → Γ(Z.X, U)), RatioAt Z st U A B := by
  obtain ⟨m₁, m₁', A₁, B₁, hA₁, hB₁, h₁⟩ := hg true
  obtain ⟨m₀, m₀', A₀, B₀, hA₀, hB₀, h₀⟩ := hg false
  have ha' : (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range ![a])).radical := by simpa using ha
  refine ⟨_, _, pf (pf ![a] A₁) B₀, pf B₁ A₀, radical_pf (radical_pf ha' hA₁) hB₀, radical_pf hB₁ hA₀, ?_⟩
  intro y a' φ hφ hU'
  obtain ⟨χ, hχ⟩ := exists_fromSpec hU y.z hU'
  rw [diff_frame hB hp Z hty hU hw y a' φ hφ χ hχ hx, hst, hst]
  have hgen := gen_eq hU y hχ
  have hxe : spMap (intO ↥y.C.S).subtype ≫ spMap χ ≫ hU.fromSpec ≫ Z.π = y.gen ≫ Z.π := by
    rw [Mdl.Pt.gen, ← hχ]
    simp only [Category.assoc]
  have e₁ := h₁ y.C χ
  have e₀ := h₀ y.C χ
  rw [hxe] at e₁ e₀
  have hval : ∀ s, valF y.gen U s = (intO ↥y.C.S).subtype.comp χ s := fun s => by rw [← hgen, valF_fromSpec]
  simp only [hval, comp_pf, comp_single, norm_pf, norm_single]
  have p₁ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hB₁
  have q₁ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hA₁
  have p₀ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hB₀
  have q₀ := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero hA₀
  have ps := norm_pos_of_radical ((intO ↥y.C.S).subtype.comp χ) hp.ne_zero ha'
  rw [comp_single, norm_single] at ps
  simpa using log_ratio p₁ q₁ p₀ q₀ ps e₁ e₀ (hc y.C χ)

theorem lnStep_inl {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x : Sp C ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool)
    (τ : E →+* ℂ) {k : ℕ} (h : k < Dw.mult τ) :
    lnStep t x u p b (.inl (τ, k)) = Real.log (grNorm t x (lat t p x b) (u τ) ⟨k, h⟩) -
      (if b ∧ τ (H.rt : E) = H.rt0 then vDiff E p * Real.log p else 0) := by
  simp only [lnStep, dif_pos h]

theorem lnStep_inr {X : Scheme.{0}} (t : SAB H X) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    (x : Sp C ⟶ X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber C) ⟶ t.G.left)) (p : ℕ) (b : Bool)
    {k : ℕ} (h : k < (letters Dw).length) :
    lnStep t x u p b (.inr k) = Real.log (grNorm t x (lat t p x b)
      (fun i => u ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, h⟩) := by
  simp only [lnStep, dif_pos h]

end Main

theorem hasRatio : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → IsGalois ℚ E → ∀ (Z : Mdl Y i₀), HasDR Z → p ∣ Z.i.l.A → ∀ st (x : Letter Dw), letterOf Dw st = some x → HasRatio Z st := by
  intro hB E _ _ _ H Dw Xo p W Y i₀ hp hW hGal Z hZ hdvd st x hx z
  obtain ⟨U, hU, hdom, w, g, e, β, y, hz, hic, hβ, hw, he, hy⟩ := GlobalTheory.T.exists_affine_domain_frame_hasDR E H Dw Xo p W Y i₀ hp hW Z hZ z
  have hty : ∀ τ n, n ≤ Dw.mult τ → n ∈ Z.ty τ := fun τ n hn => by
    rw [hZ.1 τ]
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hn)
  haveI : CharZero ↥(Z.i.c.V W) := inferInstance
  have hcz : CharZero Γ(Z.X, U) := ⟨fun m n h => Nat.cast_injective (R := ↥(Z.i.c.V W)) (hβ (by simpa using h))⟩
  obtain ⟨hroots, hdiff⟩ := GlobalTheory.T.roots_of_unity_and_p_valuation E H Z.i.l Z.i.c p W hp hW
  obtain ⟨ζ, hζ⟩ := hroots p hdvd
  obtain ⟨a₀, ha₀, hv⟩ := hdiff hGal
  have hsp := @GlobalTheory.T.splitTors_of_generic_level E _ _ _ H Dw Z.i.l (Xo Z.i.l) Z.i.c _ _ (Z.i.c.V W).subtype (Y Z.i) Γ(Z.X, U) _ hdom
    (hU.fromSpec ≫ Z.π) y hy p hdvd
  have hsep := GlobalTheory.ShFam.Pad.Pull.isSeparated_base (Y := Y) Z.i
  haveI := GlobalTheory.ProjBlowup.isDiscreteValuationRing_coeff Z.i.c hp.ne_zero hW
  haveI : IsProper (Y Z.i).s := projProper _ _ _ (Y Z.i).proj
  have hln : IsLocallyNoetherian (Y Z.i).X := LocallyOfFiniteType.isLocallyNoetherian (Y Z.i).s
  have hpres := @GlobalTheory.T.tangent_basis_of_split_torsion hB E _ _ _ H (Y Z.i).X (Y Z.i).t hln hsep p hp Γ(Z.X, U) _ hdom hic hcz (hU.fromSpec ≫ Z.π)
    ⟨β ζ, hζ.map_of_injective hβ⟩ hsp g e he
  have hind := GlobalTheory.T.integral_frame_residue E H Dw Xo p W Y i₀ hp hW Z U hU w hw
  have htan : ∀ τ i, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) (w τ i) := fun τ i => by
    obtain ⟨n, v, f, h₁, h₂, -⟩ := hw.1 τ
    exact h₁ i ▸ h₂ (f i)
  have hgn : ∀ {n : ℕ} (fam : Fin n → (Sp (DualNumber Γ(Z.X, U)) ⟶ (Y Z.i).t.G.left)),
      (∀ j, IsTanAtG (Y Z.i).t (hU.fromSpec ≫ Z.π) (fam j)) →
      (∀ (k : Type) [Field k] (ψ : Γ(Z.X, U) →+* k), (p : k) ≠ 0 →
        GlobalTheory.ShFam.Pad.Pull.Ind (Y Z.i).t (spMap ψ ≫ hU.fromSpec ≫ Z.π) (fun j => spMap (dualMap ψ) ≫ fam j)) →
      ∀ (i : Fin n) (b : Bool), ∃ (a₁ a₂ : ℕ) (A : Fin a₁ → Γ(Z.X, U)) (B : Fin a₂ → Γ(Z.X, U)),
      (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range A)).radical ∧ (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range B)).radical ∧
      ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)),
        grNorm (Y Z.i).t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π)
          (lat (Y Z.i).t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ hU.fromSpec ≫ Z.π) b)
          (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ fam j) i *
            ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ :=
    fun {n} fam h₁ h₂ i b => by
      obtain ⟨M, h, hP⟩ := hpres b
      exact GlobalTheory.T.presentation_tangent_combination E H _ (Y Z.i).t _ (hU.fromSpec ≫ Z.π) p b g M e h hp he hP n fam h₁ h₂ i
  have hone : (p : Γ(Z.X, U)) ∈ (Ideal.span {(1 : Γ(Z.X, U))}).radical := by
    rw [Ideal.span_singleton_one, Ideal.radical_top]
    exact Submodule.mem_top
  have hlog1 : ∀ (C : SCF p) (φ : Γ(Z.X, U) →+* ↥(intO ↥C.S)),
      Real.log ‖((φ 1 : ↥(intO ↥C.S)) : ↥C.S)‖ = -0 := fun C φ => by simp
  rcases st with ⟨τ, k⟩ | k
  · have hk : k < Dw.mult τ := by
      by_contra h
      simp [letterOf, h] at hx
    have hG := hgn (w τ) (htan τ) (fun k' _ ψ h => (hind k' ψ h).1 τ) ⟨k, hk⟩
    by_cases hr : τ (H.rt : E) = H.rt0
    · obtain ⟨m, m', A, B, h⟩ := exists_ratio hB hp Z hty hU hw hx (w τ) ⟨k, hk⟩ (vDiff E p * Real.log p) (β a₀)
        (by
          obtain ⟨n, hn⟩ := ha₀
          refine ⟨n, Ideal.mem_span_singleton.2 ?_⟩
          have := map_dvd β (Ideal.mem_span_singleton.1 hn)
          simpa using this)
        (fun C φ => hv C (φ.comp β))
        (fun y b ψ => by
          rw [lnStep_inl _ _ _ _ _ _ hk]
          cases b <;> simp [hr] <;> rfl) hG
      exact ⟨U, m, m', A, B, hz, hU, h⟩
    · obtain ⟨m, m', A, B, h⟩ := exists_ratio hB hp Z hty hU hw hx (w τ) ⟨k, hk⟩ 0 1 hone hlog1
        (fun y b ψ => by
          rw [lnStep_inl _ _ _ _ _ _ hk]
          cases b <;> simp [hr] <;> rfl) hG
      exact ⟨U, m, m', A, B, hz, hU, h⟩
  · have hk : k < (letters Dw).length := by
      by_contra h
      simp [letterOf, List.getElem?_eq_none (not_lt.1 h)] at hx
    obtain ⟨m, m', A, B, h⟩ := exists_ratio hB hp Z hty hU hw hx
      (fun i : Fin (letters Dw).length => w ((letters Dw).get i).1 ((letters Dw).get i).2) ⟨k, hk⟩ 0 1 hone hlog1
      (fun y b ψ => by
        rw [lnStep_inr _ _ _ _ _ hk]
        cases b <;> simp <;> rfl)
      (hgn _ (fun j => htan _ _) (fun k' _ ψ h => (hind k' ψ h).2) ⟨k, hk⟩)
    exact ⟨U, m, m', A, B, hz, hU, h⟩

end GlobalTheory.HTLine.Ratio
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRatio_of_hasDR_galois : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → IsGalois ℚ E → ∀ (Z : Mdl Y i₀), HasDR Z → p ∣ Z.i.l.A → ∀ st (x : Letter Dw), letterOf Dw st = some x → HasRatio Z st := by
  atlas_forward_decl GlobalTheory.HTLine.Ratio.hasRatio
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.HTLine

theorem exists_lineModel_hodgeTate : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (i : Idx H p) (n : ℕ), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → p ^ n ∣ i.l.A → 1 + 1 / ((p : ℝ) - 1) < n → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z true st x) := by
  intro hB E _ _ _ hG H Dw Xo p W Y i₀ hp hW hY i n hd hF hpn hn st x hx
  obtain ⟨Z₀, rfl, hty, hL⟩ := GlobalTheory.T.local_system_model_exists E H Dw Xo p W Y i₀ hp hW hY i hd hF st x hx
  obtain ⟨Z₁, h₁, hDR, ⟨f₁, hf₁⟩, -⟩ := GlobalTheory.T.exists_de_rham_flag E H Dw Xo p W hp hW Y i₀ Z₀ (fun σ => by rw [hty])
  have hn1 : 1 ≤ n := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h3 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
    have h4 : (1 : ℝ) < n := by linarith
    exact_mod_cast h4.le
  have full₀ : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z₀.ty τ := fun τ k hk => by
    rw [hty]; exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  have full₁ : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z₁.ty τ := fun τ k hk => by
    rw [hDR.1]; exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  have hR := GlobalTheory.T.hasRatio_of_hasDR_galois hB E H Dw Xo p W Y i₀ hp hW hG Z₁ hDR (h₁ ▸ (dvd_pow_self p (by omega)).trans hpn) st x hx
  obtain ⟨Z₂, f₂, h₂, hty₂, hf₂, hP⟩ := GlobalTheory.T.exists_model_with_ratio hB E H Dw Xo p W Y i₀ hp hW hY.1 Z₁ st x hx full₁ hR
  have hL₁ := GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY Z₀ Z₁ f₁ hf₁ full₀ false st x hx hL
  have hL₂ := GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY Z₁ Z₂ f₂ hf₂ full₁ false st x hx hL₁
  exact ⟨Z₂, h₂.trans h₁, hty₂.trans (funext hDR.1), GlobalTheory.T.lineModel_true_of_false E H Dw Xo p W Y i₀ hp hW Z₂ st x hP hL₂⟩

end GlobalTheory.HTLine
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_system_level_growth : HTBoundSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (i : Idx H p) (n : ℕ), i₀.l.Dvd i.l → i₀.c.F ≤ i.c.F → p ^ n ∣ i.l.A → 1 + 1 / ((p : ℝ) - 1) < n → ∀ st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧ (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z true st x) := by
  atlas_forward_decl GlobalTheory.HTLine.exists_lineModel_hodgeTate
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

namespace AdmExist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem zeta_isIntegral (n : ℕ) (hn : n ≠ 0) : IsIntegral ℚ (zeta n) :=
  ((Complex.isPrimitiveRoot_exp n hn).isIntegral (Nat.pos_of_ne_zero hn)).tower_top

theorem exists_idx {p : ℕ} (i₀ : Idx H p) (k : ℕ) (hk : 0 < k) :
    ∃ i : Idx H p, i.l.M = i₀.l.M ∧ i.l.Mb = i₀.l.Mb ∧ i.l.A = i₀.l.A * k ∧ i₀.c.F ≤ i.c.F := by
  let l : Level H := { i₀.l with A := i₀.l.A * k, A_pos := Nat.mul_pos i₀.l.A_pos hk }
  have hA : l.A ≠ 0 := l.A_pos.ne'
  have hM : l.M' ≠ 0 := Nat.lcm_ne_zero (by have := l.three_le; omega) hA
  let F : IntermediateField ℚ ℂ := i₀.c.F ⊔ IntermediateField.adjoin ℚ {zeta l.M', zeta l.A}
  have hfin : FiniteDimensional ℚ F := by
    haveI := i₀.c.fin
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ)) :=
      IntermediateField.finiteDimensional_adjoin (by
        rintro x (rfl | rfl)
        · exact zeta_isIntegral _ hM
        · exact zeta_isIntegral _ hA)
    exact IntermediateField.finiteDimensional_sup _ _
  have h1 : i₀.c.F ≤ F := le_sup_left
  have h2 : IntermediateField.adjoin ℚ ({zeta l.M', zeta l.A} : Set ℂ) ≤ F := le_sup_right
  let c : Coeff l :=
    { F := F
      fin := hfin
      conj := fun τ a => h1 (i₀.c.conj τ a)
      zeta_mem := h2 (IntermediateField.subset_adjoin _ _ (by simp))
      le := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        rintro x (rfl | rfl)
        · exact h1 (i₀.c.le (IntermediateField.subset_adjoin _ _ (by simp)))
        · exact h2 (IntermediateField.subset_adjoin _ _ (by simp)) }
  exact ⟨⟨l, c, i₀.good⟩, rfl, rfl, rfl, h1⟩

theorem finite_steps (Dw : Datum H) : Finite {st // ∃ x, letterOf Dw st = some x} := by
  let f : Letter Dw ⊕ Fin (letters Dw).length → ((E →+* ℂ) × ℕ) ⊕ ℕ := fun a => match a with
    | .inl x => .inl (x.1, x.2)
    | .inr k => .inr k
  have : {st | ∃ x, letterOf Dw st = some x} ⊆ Set.range f := by
    rintro (⟨τ, k⟩ | k) ⟨x, hx⟩
    · by_cases h : k < Dw.mult τ
      · exact ⟨.inl ⟨τ, ⟨k, h⟩⟩, rfl⟩
      · simp [letterOf, h] at hx
    · have h : k < (letters Dw).length := by
        by_contra h
        simp only [letterOf] at hx
        rw [List.getElem?_eq_none (not_lt.1 h)] at hx
        cases hx
      exact ⟨.inr ⟨k, h⟩, rfl⟩
  exact ((Set.finite_range f).subset this).to_subtype

theorem mult_add_mult_conj (D : Datum H) (τ : E →+* ℂ) : D.mult τ + D.mult (ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ) = D.p + D.q := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    simpa using this
  have h0 := H.sqrt_neg_disc_sq
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → starRingEnd ℂ z = -z := fun z hz => by
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp [pow_two] at hre him
    have : z.re = 0 := by
      by_contra hne
      have : z.im = 0 := by
        have : z.re * z.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [sq_nonneg z.re]
    apply Complex.ext <;> simp [this]
  have hne : H.rt0 ≠ 0 := by
    intro h; rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0.symm
    exact hd.ne' (by exact_mod_cast this)
  have hc : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ (H.rt : E) = -τ (H.rt : E) := key _ h1
  unfold Datum.mult
  rw [hc]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (h1.trans h0.symm) with h | h
  · have : ¬ (-H.rt0 = H.rt0) := fun e => hne (by linear_combination -e / 2)
    simp [h, this]
  · have : ¬ (-H.rt0 = H.rt0) := fun e => hne (by linear_combination -e / 2)
    simp [h, this, add_comm]

theorem exists_letter (Dw : Datum H) (h : 1 ≤ Dw.p + Dw.q) : Nonempty (Letter Dw) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h2 := mult_add_mult_conj Dw τ
  by_cases h0 : 0 < Dw.mult τ
  · exact ⟨⟨τ, ⟨0, h0⟩⟩⟩
  · exact ⟨⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb τ, ⟨0, by omega⟩⟩⟩

theorem exists_adm [IsGalois ℚ E] (hB : HTBoundSt) {Dw : Datum H} (hr : 1 ≤ Dw.p + Dw.q) {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ}
    {W : ValuationSubring ℂ} (Y : LocalSystem Xo p W) (i₀ : Idx H p) (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits)
    (hY : N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) (n : ℕ) (hn : 1 + 1 / ((p : ℝ) - 1) < n) :
    ∃ z : admitted Y i₀, z.n = n := by
  obtain ⟨i, hM, hMb, hA, hF⟩ := exists_idx i₀ (p ^ n) (pow_pos hp.pos n)
  have hd : i₀.l.Dvd i.l := ⟨hM ▸ dvd_rfl, hMb.le, hA ▸ dvd_mul_right _ _⟩
  have hpn : p ^ n ∣ i.l.A := hA ▸ dvd_mul_left _ _
  have hex : ∀ b st x, letterOf Dw st = some x → ∃ Z : Mdl Y i₀, Z.i = i ∧
      (Z.ty = fun τ => Finset.range (Dw.mult τ + 1)) ∧ Nonempty (LineModel Z b st x) := by
    intro b st x hx
    cases b
    · exact GlobalTheory.T.local_system_model_exists E H Dw Xo p W Y i₀ hp hW hY i hd hF st x hx
    · exact GlobalTheory.T.local_system_level_growth hB E H Dw Xo p W Y i₀ hp hW hY i n hd hF hpn hn st x hx
  haveI := finite_steps Dw
  let T := Bool × {st // ∃ x, letterOf Dw st = some x}
  obtain ⟨x₀⟩ := exists_letter Dw hr
  haveI : Nonempty T := ⟨(false, ⟨.inl (x₀.1, x₀.2), x₀, by simp [letterOf]⟩)⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card T = m + 1 := ⟨Nat.card T - 1, by have := Nat.card_pos (α := T); omega⟩
  let e : T ≃ Fin (m + 1) := Finite.equivFinOfCardEq hm
  choose Z hZi hZty hZl using fun t : T => hex t.1 t.2.1 t.2.2.choose t.2.2.choose_spec
  obtain ⟨Z', h1, h2, h3⟩ := GlobalTheory.T.local_system_common_refinement E H Dw Xo p W Y i₀ hp hW hY m (fun a => Z (e.symm a))
    (fun a => ⟨(hZi _).trans (hZi _).symm, (hZty _).trans (hZty _).symm⟩)
  have h1' : Z'.i = i := h1.trans (hZi _)
  have h2' := h2.trans (hZty _)
  have hl : ∀ b st x, letterOf Dw st = some x → Nonempty (LineModel Z' b st x) := by
    intro b st x hx
    let t : T := (b, ⟨st, x, hx⟩)
    obtain ⟨f, hf⟩ := h3 (e t)
    have hxe : t.2.2.choose = x := Option.some.inj (t.2.2.choose_spec.symm.trans hx)
    have hl := hZl t
    rw [hxe] at hl
    refine GlobalTheory.T.local_system_model_map hB E H Dw Xo p W Y i₀ hp hW hY _ Z' f hf ?_ b st x hx ?_
    · intro τ k hk
      rw [hZty]
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    · rw [e.symm_apply_apply]
      exact hl
  refine ⟨⟨Z', ?_, n, ?_, fun b st x hx => (hl b st x hx).some⟩, rfl⟩
  · intro τ k hk
    rw [h2']
    exact Finset.mem_range.2 (Nat.lt_succ_of_le hk)
  · rw [h1']
    exact ⟨hM, hMb, hA⟩

end AdmExist

theorem admEx_of_htBound : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), AdmEx S κ := by
  intro hB D A N j S κ p hp W hW n hn
  haveI := D.host.hostE_isGalois
  exact AdmExist.exists_adm hB (by have := S.rank_eq; have := S.two_le; omega) _ _ hp hW (S.sys.clauses p W hp hW) n hn

end GlobalTheory.ShFam.Pad
end
end
