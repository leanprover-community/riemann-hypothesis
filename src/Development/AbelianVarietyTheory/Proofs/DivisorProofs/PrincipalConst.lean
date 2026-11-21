import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisor
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKaehlerBasisDifferentialsOfTopFormFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVani
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericResidueLinearIndependence
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChart
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDivisorEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.LogResolutionMultiplierLocal
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsLogResolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFunctionFieldPullbackPrimeDivisorOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameEtale

theorem etale_eval₂Hom_of_basis {k A : Type} [CommRing k] [CommRing A] (α : k →+* A) (hα : α.Smooth)
    {n : ℕ} (z : Fin n → A) (b : Module.Basis (Fin n) A (Omega α)) (hb : ∀ i, b i = dFun α (z i)) :
    (MvPolynomial.eval₂Hom α z).Etale := by
  letI := α.toAlgebra
  haveI : Algebra.Smooth k A := hα
  letI := (MvPolynomial.eval₂Hom α z).toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin n) k) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C α z r).symm
  have hX (i) : algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i) = z i :=
    MvPolynomial.eval₂Hom_X' α z i
  exact EtaleCoordJacobian.etale_of_basis k A (Fin n) b fun i => by rw [hX]; exact hb i

theorem isEtCoord_of_isFrame : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (V : Y.Opens) (z : Fin n → Γ(Y, V)), IsFrame (dOn q z) → IsAffineOpen V ∧ IsEtCoord q V z := by
  intro k _ Y q n hq V z hz
  refine ⟨hz.affine, ?_⟩
  obtain ⟨b, hb⟩ := FrameBasis.exists_basis_of_isFrame k Y q n hq V z hz
  haveI : Smooth q := SmoothOfRelativeDimension.smooth n q
  have h := HasRingHomProperty.appLE (@Smooth) q inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hz.affine⟩ le_top
  have h₁ : (DVR.FlatBC.algX q V).Smooth :=
    RingHom.Smooth.respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv h
  exact etale_eval₂Hom_of_basis (DVR.FlatBC.algX q V) h₁ z b hb

end GlobalTheory.FrameEtale
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinatesOnOpen_of_isTopFormFrame : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (V : Y.Opens) (z : Fin n → Γ(Y, V)), IsFrame (dOn q z) → IsAffineOpen V ∧ IsEtCoord q V z := by
  atlas_forward_decl GlobalTheory.FrameEtale.isEtCoord_of_isFrame
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.LogPair TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem smooth_quotient_of_isEtCoord (Y : Scheme.{0}) (q : Y ⟶ Sp ℂ) (n : ℕ) (U : Y.Opens) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n))
    (hE : IsEtCoord q U z) :
    ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  let A := MvPolynomial (Fin n) ℂ
  let B := Γ(Y, U)
  let φ : A →+* B := MvPolynomial.eval₂Hom (cstOn q U) z
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.Etale A B := RingHom.etale_algebraMap.1 hE
  let I : Ideal A := Ideal.span (MvPolynomial.X '' (J : Set (Fin n)))
  have hI : I.map (algebraMap A B) = Ideal.span (z '' (J : Set (Fin n))) := by
    rw [Ideal.map_span, Set.image_image]
    congr 1
    ext x
    simp only [RingHom.algebraMap_toAlgebra, φ, Set.mem_image, Finset.mem_coe]
    constructor <;> rintro ⟨j, hj, rfl⟩ <;> exact ⟨j, hj, by rw [MvPolynomial.eval₂Hom_X']⟩
  have h1 : (algebraMap ℂ (A ⧸ I)).Smooth := by
    rw [RingHom.smooth_algebraMap]
    haveI : Algebra.Smooth ℂ (MvPolynomial {x // x ∉ (J : Set (Fin n))} ℂ) := ⟨inferInstance, inferInstance⟩
    exact Algebra.Smooth.of_equiv (quotientSpanXEquiv ℂ (J : Set (Fin n))).symm
  have h2 : (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).Smooth := by
    rw [RingHom.smooth_algebraMap]; infer_instance
  let e : ((A ⧸ I) ⊗[A] B) ≃+* B ⧸ Ideal.span (z '' (J : Set (Fin n))) :=
    ((Algebra.TensorProduct.comm A (A ⧸ I) B).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toRingEquiv).trans
      (Ideal.quotEquivOfEq hI)
  have h12 : ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I))).Smooth :=
    RingHom.Smooth.comp h1 h2
  have h3 : (e.toRingHom.comp ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I)))).Smooth :=
    have he : e.toRingHom.Smooth := RingHom.Smooth.of_bijective e.bijective
    RingHom.Smooth.comp h12 he
  convert h3 using 1
  ext c
  simp only [RingHom.comp_apply]
  have k1 : algebraMap ℂ (A ⧸ I) c = Ideal.Quotient.mk I (MvPolynomial.C c) := rfl
  have k2 : algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I (MvPolynomial.C c)) =
      (1 : A ⧸ I) ⊗ₜ[A] (algX q U c) := by
    have hm : Ideal.Quotient.mk I (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hm,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    congr 1
    simp [RingHom.algebraMap_toAlgebra, φ]
    rfl
  have k3 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm (algX q U c ⊗ₜ[A] (1 : A ⧸ I)) =
      Ideal.Quotient.mk _ (algX q U c) := by
    rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  rw [k1, k2]
  simp only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul, k3,
    Ideal.quotEquivOfEq_mk]

theorem smooth_coordStratum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ J : Finset (Fin n), ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  intro Y _ _ q n _ U z hF J
  exact smooth_quotient_of_isEtCoord Y q n U z J (GlobalTheory.T.isEtaleCoordinatesOnOpen_of_isTopFormFrame ℂ Y q n U z hF).2

end GlobalTheory.PairStep
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_coordinateStratum_etaleChart : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ J : Finset (Fin n), ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  atlas_forward_decl GlobalTheory.PairStep.smooth_coordStratum
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.StrataBertini

theorem isLocalization_atPrime_quotient {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p] (I : Ideal A) (hI : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    IsLocalization.AtPrime (S ⧸ I.map (algebraMap A S)) (p.map (Ideal.Quotient.mk I)) := by
  constructor
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∉ p := fun h => hx (Ideal.mem_map_of_mem _ h)
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units S (⟨a, ha⟩ : p.primeCompl)).map _
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.primeCompl w
    refine ⟨⟨Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I s, ?_⟩⟩, ?_⟩
    · exact fun hs => s.2 ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
      rw [← map_mul, h]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq, ← map_sub] at hxy
    rw [IsLocalization.mem_map_algebraMap_iff p.primeCompl S] at hxy
    obtain ⟨⟨⟨i, hi⟩, m⟩, hm⟩ := hxy
    rw [← map_mul, IsLocalization.eq_iff_exists p.primeCompl S] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨⟨Ideal.Quotient.mk I (c * m), ?_⟩, ?_⟩
    · exact fun hs => (p.primeCompl.mul_mem c.2 m.2) ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · show Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I a = Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I b
      rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have : (↑c * ↑m * (a - b) : A) = ↑c * i := by linear_combination hc
      rw [this]
      exact I.mul_mem_left _ hi

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem linearIndependent_option_cotangent {S : Type*} [CommRing S] [IsLocalRing S] {J : Type*}
    [Fintype J] (w : Option J → S) (hw : ∀ j, w j ∈ maximalIdeal S)
    (hind : LinearIndependent (ResidueField S)
      (fun j : J => ((maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ : CotangentSpace S)))
    (hnot : w none ∉ maximalIdeal S ^ 2 ⊔ Ideal.span (Set.range (fun j : J => w (some j)))) :
    LinearIndependent (ResidueField S)
      (fun j : Option J => ((maximalIdeal S).toCotangent ⟨w j, hw j⟩ : CotangentSpace S)) := by
  rw [linearIndependent_option]
  refine ⟨hind, fun hmem => hnot ?_⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  choose b hb using fun j => IsLocalRing.residue_surjective (c j)
  have hc' : ∑ j, b j • (maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ =
      (maximalIdeal S).toCotangent ⟨w none, hw none⟩ := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, ← hb j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have h0 : (maximalIdeal S).toCotangent
      (⟨w none, hw none⟩ - ∑ j, b j • ⟨w (some j), hw (some j)⟩) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [hc', sub_self]
  rw [Ideal.toCotangent_eq_zero] at h0
  have h1 : w none = (w none - ∑ j, b j * w (some j)) + ∑ j, b j * w (some j) := by ring
  rw [h1]
  refine Submodule.add_mem_sup ?_ ?_
  · simpa using h0
  · exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem key (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n q] (U : Y.Opens) (z : Fin n → Γ(Y, U)) (hfr : IsFrame (dOn q z))
    (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)) (J : Finset (Fin n)) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) →
      (∀ j : J, Y.presheaf.germ U y hy (z j) ∈ maximalIdeal (Y.presheaf.stalk y)) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∈ maximalIdeal (Y.presheaf.stalk y) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∉
        maximalIdeal (Y.presheaf.stalk y) ^ 2 ⊔
          Ideal.span (Set.range (fun j : J => Y.presheaf.germ U y hy (z j))) := by
  have hU : IsAffineOpen U := hfr.affine
  set I : Ideal Γ(Y, U) := Ideal.span (z '' (J : Set (Fin n))) with hIdef
  letI : Algebra ℂ (Γ(Y, U) ⧸ I) := ((Ideal.Quotient.mk I).comp (algX q U)).toAlgebra
  haveI : Algebra.Smooth ℂ (Γ(Y, U) ⧸ I) := GlobalTheory.T.smooth_coordinateStratum_etaleChart Y q n U z hfr J
  obtain ⟨Q1, hQ1, hQ1u⟩ :=
    GlobalTheory.bertini_cotangent_independent ℂ (Γ(Y, U) ⧸ I) (fun i => Ideal.Quotient.mk I (f i)) 1
  have hinj : Function.Injective (Prod.snd : Fin 1 × ι → ι) :=
    fun a b h => Prod.ext (Subsingleton.elim _ _) h
  refine ⟨MvPolynomial.rename Prod.snd Q1, fun h0 => hQ1 (MvPolynomial.rename_injective _ hinj
    (by rw [h0, map_zero])), ?_⟩
  intro u hu y hy hf hz ht
  have hu' : MvPolynomial.eval (u ∘ Prod.snd) Q1 ≠ 0 := by rwa [MvPolynomial.eval_rename] at hu
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  set p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal with hpdef
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, hy⟩
  have hgerm : ∀ a, algebraMap Γ(Y, U) (Y.presheaf.stalk y) a = Y.presheaf.germ U y hy a :=
    fun a => rfl
  have hpm : ∀ a, a ∈ p ↔ Y.presheaf.germ U y hy a ∈ maximalIdeal (Y.presheaf.stalk y) := by
    intro a
    rw [← IsLocalization.AtPrime.comap_maximalIdeal (Y.presheaf.stalk y) p, ← hgerm]
    rfl
  have hIp : I ≤ p := Ideal.span_le.2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact (hpm _).2 (hz ⟨j, hj⟩))
  haveI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  set IS := I.map (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) with hISdef
  have hISm : IS ≤ maximalIdeal (Y.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (fun a ha => (hpm a).1 (hIp ha))
  haveI : Nontrivial (Y.presheaf.stalk y ⧸ IS) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hISm)
  haveI : IsLocalRing (Y.presheaf.stalk y ⧸ IS) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IS) Ideal.Quotient.mk_surjective
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y ⧸ IS) (p.map (Ideal.Quotient.mk I)) :=
    isLocalization_atPrime_quotient p I hIp
  have hmk : ∀ a ∈ maximalIdeal (Y.presheaf.stalk y),
      Ideal.Quotient.mk IS a ∈ maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hun
    obtain ⟨c, hc⟩ := hun.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, ← map_one (Ideal.Quotient.mk IS), Ideal.Quotient.eq] at hc
    have h1 : a * c' ∈ maximalIdeal (Y.presheaf.stalk y) := Ideal.mul_mem_right _ _ ha
    have h2 := Ideal.sub_mem _ h1 (hISm hc)
    rw [sub_sub_cancel] at h2
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have hfi : ∃ i, Ideal.Quotient.mk I (f i) ∉ p.map (Ideal.Quotient.mk I) := by
    obtain ⟨i, hi⟩ := hf
    refine ⟨i, ?_⟩
    rw [Ideal.mem_quotient_iff_mem hIp, hpm]
    exact fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) ((Y.mem_basicOpen _ _ hy).1 hi)
  have htR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) =
      Ideal.Quotient.mk IS (Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i)) := by
    rw [← hgerm, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul, map_mul]
    rfl
  have hli := hQ1u (u ∘ Prod.snd) hu' (p.map (Ideal.Quotient.mk I)) (Y.presheaf.stalk y ⧸ IS) hfi
  have hmemR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈
      maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    rw [htR]; exact hmk _ ht
  have hne := hli.ne_zero ⟨0, hmemR⟩
  rw [Ne, Ideal.toCotangent_eq_zero] at hne
  intro hmem2
  apply hne
  show algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈ _
  rw [htR]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem2
  have hbI : b ∈ IS := by
    refine (Ideal.span_le.2 ?_) hb
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) (Ideal.subset_span ⟨j, j.2, rfl⟩)
  rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hbI, add_zero]
  have hma : Ideal.Quotient.mk IS a ∈ (maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk IS) ^ 2 := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmk) 2 hma

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

theorem bertini_strata_cotangent : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)), ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) → ∀ (J : Finset (Fin n)) (h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) j, h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hfr ι _ f
  choose Q hQ0 hQ using fun J : Finset (Fin n) => key Y q n U z hfr ι f J
  refine ⟨∏ J, Q J, Finset.prod_ne_zero_iff.2 fun J _ => hQ0 J, fun u hu y hy hf J h => ?_⟩
  rw [map_prod] at hu
  have huJ := Finset.prod_ne_zero_iff.1 hu J (Finset.mem_univ _)
  exact linearIndependent_option_cotangent
    (fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) h
    (GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hfr y hy J (fun j => h (some j)))
    (hQ J u huJ y hy hf (fun j => h (some j)) (h none))

end GlobalTheory.StrataBertini
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bertini_coordinateStrata_etaleChart_cotangent : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)), ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) → ∀ (J : Finset (Fin n)) (h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) j, h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  atlas_forward_decl GlobalTheory.StrataBertini.bertini_strata_cotangent
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_nbhd_specializes_of_isClosed {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : Set Y) (hF : IsClosed F) (hη : genericPoint Y ∉ F) {y : Y} {O : Y.Opens} (hy : y ∈ O) :
    ∃ V : Y.Opens, y ∈ V ∧ V ≤ O ∧
      ∀ y' ∈ V, ∀ v, v ⤳ y' → Order.coheight v = 1 → v ∈ F → v ⤳ y := by
  classical
  obtain ⟨W, hW, hyW, hWO⟩ := exists_isAffineOpen_mem_and_subset hy
  haveI := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hN : NoetherianSpace W := by
    have := NoetherianSpace.range hW.fromSpec hW.fromSpec.continuous
    rw [hW.range_fromSpec] at this
    exact this
  have hC : IsClosed ((Subtype.val : W → Y) ⁻¹' F) := hF.preimage continuous_subtype_val
  obtain ⟨S, hS, hc, hi, hU⟩ := @NoetherianSpace.exists_finite_set_isClosed_irreducible _ _ hN _ hC
  let y₀ : W := ⟨y, hyW⟩
  let bad : Set W := ⋃₀ {T ∈ S | y₀ ∉ T}
  have hS' : {T ∈ S | y₀ ∉ T}.Finite := hS.subset fun T hT => hT.1
  have hbad : IsClosed bad := by
    change IsClosed (⋃₀ {T ∈ S | y₀ ∉ T})
    rw [Set.sUnion_eq_biUnion]
    exact hS'.isClosed_biUnion fun T hT => hc T hT.1
  refine ⟨⟨Subtype.val '' badᶜ, W.isOpen.isOpenMap_subtype_val _ hbad.isOpen_compl⟩,
    ⟨y₀, ?_, rfl⟩, ?_, ?_⟩
  · rintro ⟨T, ⟨-, hyT⟩, hyT'⟩
    exact hyT hyT'
  · rintro _ ⟨x, -, rfl⟩
    exact hWO x.2
  · rintro _ ⟨x, hx, rfl⟩ v hv hcv hvF
    have hvW : v ∈ W := hv.mem_open W.isOpen x.2
    let v' : W := ⟨v, hvW⟩
    have hv' : v' ⤳ x := Topology.IsInducing.subtypeVal.specializes_iff.1 hv
    have hvS : v' ∈ ⋃₀ S := hU ▸ hvF
    obtain ⟨T, hT, hvT⟩ := hvS
    have hxT : x ∈ T := hv'.mem_closed (hc T hT) hvT
    have hyT : y₀ ∈ T := by
      by_contra h
      exact hx ⟨T, ⟨hT, h⟩, hxT⟩
    obtain ⟨g, hg⟩ := QuasiSober.sober (hi T hT) (hc T hT)
    have hgF : g.1 ∈ F := by
      have : g ∈ ⋃₀ S := ⟨T, hT, hg.mem⟩
      rw [← hU] at this
      exact this
    have hgv : g.1 ⤳ v := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hvT)
    have hgy : g.1 ⤳ y := Topology.IsInducing.subtypeVal.specializes_iff.2 (hg.specializes hyT)
    have hgη : g.1 < genericPoint Y := by
      refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
      have e' : g.1 = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
      exact hη (e' ▸ hgF)
    have hvg : v = g.1 := by
      by_contra hne
      have h₃ := Order.coheight_add_one_le (show v < g.1 from lt_of_le_not_ge hgv fun e =>
        hne (Specializes.antisymm e hgv).eq)
      have h₄ := Order.coheight_add_one_le hgη
      rw [hcv] at h₃
      have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
      exact absurd h₅ (by decide)
    rw [hvg]
    exact hgy

theorem isSncChart_spread : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ)
    (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ),
    genericPoint Y ∉ B → IsSncChart q n B y U hy z J w u → ∃ V : Y.Opens, y ∈ V ∧ ∀ y' ∈ V,
      ∃ (hy' : y' ∈ U) (J' : Finset (Fin n)), J' ⊆ J ∧ IsSncChart q n B y' U hy' z J' w u ∧
        ∀ j ∈ J', y' ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B y U hy z J w u hη hc
  classical
  have hηb : ∀ j ∈ J, genericPoint Y ∈ Y.basicOpen (z j) := fun j hj =>
    (Y.mem_basicOpen (z j) _ (gen_mem hy)).2 (by
      have : IsUnit (u j : Y.functionField) := (u j).isUnit
      rw [hc.val j hj] at this
      exact this)
  have hord0 : ∀ j ∈ J, ∀ v ∈ Y.basicOpen (z j), Scheme.ord (u j : Y.functionField) v = 0 := by
    intro j hj v hv
    haveI : Nonempty (Y.basicOpen (z j)) := ⟨⟨v, hv⟩⟩
    have h1 := Scheme.ord_of_isUnit (U := Y.basicOpen (z j))
      (Y.toRingedSpace.isUnit_res_basicOpen (z j)) hv
    rw [hc.val j hj, ← h1]
    congr 1
    exact (Y.presheaf.germ_res_apply (homOfLE (Y.basicOpen_le (z j))) _ _ (z j)).symm
  let F : Set Y := (B : Set Y) ∪ ⋃ j ∈ J, ((Y.basicOpen (z j) : Set Y))ᶜ
  have hF : IsClosed F := B.isClosed.union
    (isClosed_biUnion_finset fun j _ => (Y.basicOpen (z j)).isOpen.isClosed_compl)
  have hηF : genericPoint Y ∉ F := by
    rintro (h | h)
    · exact hη h
    · obtain ⟨j, hj, h⟩ := Set.mem_iUnion₂.1 h
      exact h (hηb j hj)
  obtain ⟨V, hyV, hVU, hV⟩ := exists_nbhd_specializes_of_isClosed F hF hηF hy
  refine ⟨V, hyV, fun y' hy' => ?_⟩
  have hy'U : y' ∈ U := hVU hy'
  refine ⟨hy'U, J.filter (fun j => w j ⤳ y'), Finset.filter_subset _ _,
    ⟨hc.frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    exact hc.val j (Finset.mem_filter.1 hj).1
  · intro j hj
    exact (Finset.mem_filter.1 hj).2
  · intro j hj
    exact hc.coheight j (Finset.mem_filter.1 hj).1
  · exact hc.inj.mono fun j hj => (Finset.mem_filter.1 hj).1
  · intro j hj
    exact hc.ord_self j (Finset.mem_filter.1 hj).1
  · intro j hj v hv hne
    have hjJ := (Finset.mem_filter.1 hj).1
    by_cases hb : v ∈ Y.basicOpen (z j)
    · exact hord0 j hjJ v hb
    by_cases hcv : Order.coheight v = 1
    · exact hc.ord_other j hjJ v (hV y' hy' v hv hcv (Or.inr (Set.mem_iUnion₂.2 ⟨j, hjJ, hb⟩))) hne
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hcv _
  · intro v hv hcv
    constructor
    · intro hvB
      obtain ⟨j, hj, rfl⟩ := (hc.mem v (hV y' hy' v hv hcv (Or.inl hvB)) hcv).1 hvB
      exact ⟨j, Finset.mem_filter.2 ⟨hj, hv⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      have hjJ := (Finset.mem_filter.1 hj).1
      exact (hc.mem _ (hc.spec j hjJ) hcv).2 ⟨j, hjJ, rfl⟩
  · intro j hj hb
    have hjJ := (Finset.mem_filter.1 hj).1
    have h0 := hord0 j hjJ (w j) ((Finset.mem_filter.1 hj).2.mem_open (Y.basicOpen (z j)).isOpen hb)
    rw [hc.ord_self j hjJ] at h0
    exact one_ne_zero h0

end GlobalTheory.PairStep
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSncAdaptedCoordinates_of_mem_nhds : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), genericPoint Y ∉ B → IsSncChart q n B y U hy z J w u → ∃ V : Y.Opens, y ∈ V ∧ ∀ y' ∈ V, ∃ (hy' : y' ∈ U) (J' : Finset (Fin n)), J' ⊆ J ∧ IsSncChart q n B y' U hy' z J' w u ∧ ∀ j ∈ J', y' ∉ Y.basicOpen (z j) := by
  atlas_forward_decl GlobalTheory.PairStep.isSncChart_spread
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem genericPoint_notMem_of_snc (Y : Scheme.{0}) [IsIntegral Y] (B : Closeds Y)
    (h : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)) : genericPoint Y ∉ B := by
  obtain ⟨-, U, hy, n, f, J, ⟨-, hn⟩, hI⟩ := h (genericPoint Y)
  have hdim : ringKrullDim (Y.presheaf.stalk (genericPoint Y)) = 0 :=
    ringKrullDim_eq_zero_of_field Y.functionField
  rw [hdim] at hn
  have hn0 : n = 0 := by exact_mod_cast hn
  subst hn0
  have hJ : J = ∅ := Finset.eq_empty_of_isEmpty J
  subst hJ
  intro hB
  have hs : genericPoint Y ∈ (Scheme.IdealSheafData.vanishingIdeal B).support := by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hB
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hy, hI, Scheme.mem_zeroLocus_iff] at hs
  refine hs 1 (Ideal.subset_span (by simp)) ?_
  simpa using hy

end GlobalTheory.PairStep
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

theorem exists_sncChart_isEqn_affine : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∀ y₀ : Y, ∃ (W : Y.Opens) (hW : y₀ ∈ W) (z : Fin n → Γ(Y, W)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ) (e : Y.functionFieldˣ) (f : ι → Γ(Y, W)), IsFrame (dOn q z) ∧ (∀ y ∈ W, A.IsEqn y e) ∧ (∀ i, fnOf W (gen_mem hW) (f i) = s i * e) ∧ ∀ (y : Y) (hy : y ∈ W), ∃ J : Finset (Fin n), IsSncChart q n B y W hy z J w u ∧ ∀ j ∈ J, y ∉ Y.basicOpen (z j) := by
  intro Y _ _ q n _ B hB A ι s hs y₀
  obtain ⟨U, hy₀, z, J, w, u, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB y₀
  have hgen : genericPoint Y ∉ B := GlobalTheory.PairStep.genericPoint_notMem_of_snc Y B hB
  obtain ⟨V, hyV, hV⟩ := GlobalTheory.T.isSncAdaptedCoordinates_of_mem_nhds Y q n B y₀ U hy₀ z J w u hgen hc
  obtain ⟨N, hyN, e, he⟩ := A.exists_isEqn_nhds y₀
  obtain ⟨W, hWa, hyW, hWle⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
    (show y₀ ∈ U ⊓ V ⊓ N from ⟨⟨hy₀, hyV⟩, hyN⟩)
  have hWU : W ≤ U := hWle.trans (inf_le_left.trans inf_le_left)
  have hWV : W ≤ V := hWle.trans (inf_le_left.trans inf_le_right)
  have hWN : W ≤ N := hWle.trans inf_le_right
  have hf : ∀ i, ∃ a : Γ(Y, W), fnOf W (gen_mem hyW) a = s i * e := fun i =>
    exists_fnOf_eq (gen_mem hyW) fun x hx =>
      (he x (hWN hx)).regularAt_iff.1 (CartierDiv.mem_sections.1 (hs i) x)
  choose f hf using hf
  have hfr : IsFrame (dOn q fun j => resG Y hWU (z j)) := by
    have := hc.frame.res hWa hWU
    rwa [resForm_dOn] at this
  refine ⟨W, hyW, fun j => resG Y hWU (z j), w, u, e, f, hfr, fun y hy => he y (hWN hy), hf, ?_⟩
  intro y hy
  obtain ⟨hyU, J', -, hc', hJ'⟩ := hV y (hWV hy)
  refine ⟨J', ⟨hfr, ?_, hc'.spec, hc'.coheight, hc'.inj, hc'.ord_self, hc'.ord_other, hc'.mem⟩, ?_⟩
  · intro j hj
    rw [hc'.val j hj, fnOf_resG]
  · intro j hj hmem
    have hb : Y.basicOpen (resG Y hWU (z j)) = W ⊓ Y.basicOpen (z j) :=
      Y.basicOpen_res (z j) (homOfLE hWU).op
    rw [hb] at hmem
    exact hJ' j hj hmem.2

end GlobalTheory.PairStep
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_snc_chart_cartier_single_equation : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∀ y₀ : Y, ∃ (W : Y.Opens) (hW : y₀ ∈ W) (z : Fin n → Γ(Y, W)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ) (e : Y.functionFieldˣ) (f : ι → Γ(Y, W)), IsFrame (dOn q z) ∧ (∀ y ∈ W, A.IsEqn y e) ∧ (∀ i, fnOf W (gen_mem hW) (f i) = s i * e) ∧ ∀ (y : Y) (hy : y ∈ W), ∃ J : Finset (Fin n), IsSncChart q n B y W hy z J w u ∧ ∀ j ∈ J, y ∉ Y.basicOpen (z j) := by
  atlas_forward_decl GlobalTheory.PairStep.exists_sncChart_isEqn_affine
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.ord_zpow_int {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  obtain ⟨m, rfl | rfl⟩ := r.eq_nat_or_neg
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]; ring

theorem DivOver.ord_finsetProd_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ)
    (e : ι → ℤ) : E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, E.ord_mul, ih, E.ord_zpow_int]

theorem DivOver.ord_eq_zero_of_unitAt_through {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {y : X} (hE : E.Through y) (v : X.functionFieldˣ)
    (h : UnitAt y (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, e⟩ := h
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, e⟩
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := by
    refine hE _ ⟨(ha.unit⁻¹ : (X.presheaf.stalk y)ˣ), ?_⟩
    rw [Units.val_inv_eq_inv_val, ← e]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have a1 := (E.ord_nonneg_iff v).2 h1
  have a2 := (E.ord_nonneg_iff v⁻¹).2 h2
  rw [E.ord_inv] at a2
  omega

end GlobalTheory.Discrepancy

namespace GlobalTheory.Discrepancy

theorem IsSncChart.discrep_eq_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  intro Y _ _ q n _ B y U hy z J w u hc η K Θ m g hη hK hm hΘ hg E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  set ω := formOf U (gen_mem hy) (dOn q z) with hω
  have hgen := isFreeGen_formOf (gen_mem hy) hc.frame
  have h0 : ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [← hω, h]))
  obtain ⟨c, hcη⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hcη]; simp [h])
  set k0 : Y.functionFieldˣ := Units.mk0 c hc0 with hk0
  have hηk : η = (k0 : Y.functionField) • ω := by rw [hk0, Units.val_mk0]; exact hcη.symm
  have hKy : K.IsEqn y k0 := hK U (dOn q z) hc.frame y hy k0 hηk
  have hΘy := GlobalTheory.T.snc_chart_divisor_equation ℂ Y q n B y U hy z J w u hc Θ hΘ
  set M : Y.functionFieldˣ := ∏ j ∈ J, u j ^ Θ.mult (w j) with hM
  have hsum : (Θ + m • K).IsEqn y (M * k0 ^ m) := hΘy.add (hKy.nsmul m)
  set v : Y.functionFieldˣ := g * (M * k0 ^ m)⁻¹ with hv
  have hvu : UnitAt y (v : Y.functionField) := by
    have := hsum.iff_unitAt.1 hg
    rwa [hv, Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
  have hv0 : E.ord v = 0 := E.ord_eq_zero_of_unitAt_through hE v hvu
  have hvo : E.ord v = E.ord g - (E.ord M + m * E.ord k0) := by
    rw [hv, E.ord_mul, E.ord_inv, E.ord_mul, E.ord_pow]; ring
  have hMo : E.ord M = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) := by
    rw [hM, E.ord_finsetProd_zpow]
  have hordg : E.ord g = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) + m * E.ord k0 := by
    rw [← hMo]; omega
  have hform : E.formOrd η = E.ord k0 + E.formOrd ω := by
    rw [hηk]; exact E.formOrd_smul hn h0 k0
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, hform, hordg]
  push_cast
  have hs : ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * (E.ord (u j) : ℚ) =
      (∑ j ∈ J, (Θ.mult (w j) : ℚ) * E.ord (u j)) / m := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => div_mul_eq_mul_div _ _ _
  rw [hs]
  field_simp
  ring

end GlobalTheory.Discrepancy
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrepancy_eq_formOrder_sub_weighted_coordOrders : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  atlas_forward_decl GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndepDiscrep

theorem neg_one_lt_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], topologicalKrullDim Y = n → ∀ (y : Y) (U : Y.Opens) (hy : y ∈ U) (ω : FormsOn q n U), IsFrame ω → ∀ (J : Type) [Fintype J] (a : J → Y.presheaf.stalk y) (ha : ∀ j, a j ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (v : J → Y.functionFieldˣ) (c : J → ℚ), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨a j, ha j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) → (∀ j, (v j : Y.functionField) = algebraMap (Y.presheaf.stalk y) Y.functionField (a j)) → (∀ j, c j < 1) → ∀ E : DivOver q, E.Through y → -1 < (E.formOrd (formOf U (gen_mem hy) ω) : ℚ) - ∑ j, c j * E.ord (v j) := by
  classical
  intro Y _ _ q n _ hn y U hy ω hω J _ a ha v c hind hv hc E hE
  haveI := SmoothOfRelativeDimension.smooth n q
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth q
  obtain ⟨U', hy', z, e, he, hze, hz⟩ :=
    GlobalTheory.AdaptedFrame.exists_adapted_frame (p := q) (n := n) y a ha hind
  have h0 : formOf U (gen_mem hy) ω ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have h0' : formOf U' (gen_mem hy') (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy') hz).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨f, hf⟩ := (isFreeGen_formOf (gen_mem hy') hz).2 (formOf U (gen_mem hy) ω)
  have hf0 : f ≠ 0 := fun h => h0 (by rw [← hf, h]; exact zero_smul _ _)
  set u : Y.functionFieldˣ := Units.mk0 f hf0 with hu
  have hfu : ((u : Y.functionField) • formOf U' (gen_mem hy') (dOn q z)) = formOf U (gen_mem hy) ω :=
    by rw [hu, Units.val_mk0]; exact hf
  have hF (Fd : DivOver q) : Fd.formOrd (formOf U (gen_mem hy) ω) =
      Fd.ord u + Fd.formOrd (formOf U' (gen_mem hy') (dOn q z)) := by
    rw [← Fd.formOrd_smul hn h0' u, hfu]
  have h0z : ∀ w, w ⤳ y → ∀ Fd : DivOver q, Fd.IsAt w → Fd.ord u = 0 := by
    intro w hw Fd hFd
    have h1 := hF Fd
    have a1 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U.isOpen hy) hFd hω
    have a2 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U'.isOpen hy') hFd hz
    rw [a1, a2] at h1
    omega
  have reg : ∀ w : Y.functionFieldˣ,
      (∀ x, x ⤳ y → ∀ Fd : DivOver q, Fd.IsAt x → 0 ≤ Fd.ord w) → 0 ≤ E.ord w := fun w hw =>
    (E.ord_nonneg_iff w).2 (hE _ (regAt_of_forall_coheight_eq_one fun x hx h1 =>
      have ⟨Fd, hFd⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) h1
      (hFd _).1 ((Fd.ord_nonneg_iff w).1 (hw x hx Fd hFd))))
  have hu1 := reg u fun x hx Fd hFd => (h0z x hx Fd hFd).ge
  have hu2 := reg u⁻¹ fun x hx Fd hFd => by rw [Fd.ord_inv, h0z x hx Fd hFd, neg_zero]
  rw [E.ord_inv] at hu2
  have hu0 : E.ord u = 0 := by omega
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy' hE z h0' e he v fun j => by
    rw [hv, ← hze j, algebraMap_germ]
  have hN := DivOver.formOrd_formOf_nonneg hn hy' hE (dOn q z) h0'
  have hnn : ∀ j, 0 ≤ E.ord (v j) := fun j => (E.ord_nonneg_iff _).2 (hE _ ⟨a j, (hv j).symm⟩)
  rw [hF E, hu0, zero_add]
  have hAq : (∑ j, (E.ord (v j) : ℚ)) - 1 ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by
    exact_mod_cast hA
  have hNq : (0 : ℚ) ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by exact_mod_cast hN
  have hle : ∀ j, c j * (E.ord (v j) : ℚ) ≤ E.ord (v j) := fun j => by
    have : (0 : ℚ) ≤ E.ord (v j) := by exact_mod_cast hnn j
    nlinarith [hc j]
  by_cases h : ∃ j, 0 < E.ord (v j)
  · obtain ⟨j, hj⟩ := h
    have hlt : ∑ j, c j * (E.ord (v j) : ℚ) < ∑ j, (E.ord (v j) : ℚ) :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨j, Finset.mem_univ _, by
        have : (0 : ℚ) < E.ord (v j) := by exact_mod_cast hj
        nlinarith [hc j]⟩
    linarith
  · push_neg at h
    have h' : ∀ j, E.ord (v j) = 0 := fun j => le_antisymm (h j) (hnn j)
    simp only [h', Int.cast_zero, mul_zero, Finset.sum_const_zero, sub_zero]
    linarith

end GlobalTheory.IndepDiscrep
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  intro Y _ _ q n _ B y U hy z J w u hc hJ F hind φ f a c hφ hf ha hc1 E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)

  have hunit : ∀ g : Y.functionFieldˣ, UnitAt y (g : Y.functionField) → E.ord g = 0 := by
    rintro g ⟨b, hb, hbg⟩
    have h1 : (g : Y.functionField) ∈ E.ring := hE _ ⟨b, hbg⟩
    have h2 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ∈ E.ring := hE _ ⟨↑(hb.unit⁻¹), by
      rw [map_units_inv, IsUnit.unit_spec, hbg]; simp⟩
    have e1 := (E.ord_nonneg_iff g).2 h1
    have e2 := (E.ord_nonneg_iff _).2 h2
    rw [E.ord_inv] at e2
    omega
  have hfφ : E.ord f = E.ord φ := by
    have hg : UnitAt y ((f * φ⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      simpa [div_eq_mul_inv] using hf
    have h0 := hunit _ hg
    have : f = (f * φ⁻¹) * φ := by group
    rw [this, E.ord_mul, h0, zero_add]
  by_cases hyF : y ∈ Y.basicOpen F
  · have hφu : UnitAt y (φ : Y.functionField) := hφ ▸ (unitAt_fnOf_iff hy _ F).2 hyF
    have hfu : UnitAt y (f : Y.functionField) := by
      have := UnitAt.mul hf hφu
      rwa [div_mul_cancel₀ _ φ.ne_zero] at this
    have h0 := hunit f hfu
    have key := (IsSncChart.neg_one_lt_formOrd_sub_sum ℂ Y q n B y U hy z J w u hc E hE a).1 ha
    rw [h0]
    simpa using key
  · have hmax : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rintro (_ | ⟨j, hj⟩)
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hyF ((Scheme.mem_basicOpen Y F y hy).2 h))
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hJ j hj ((Scheme.mem_basicOpen Y (z j) y hy).2 h))
    have hv : ∀ j : Option J, ((j.elim φ fun j => u j : Y.functionFieldˣ) : Y.functionField) =
        algebraMap (Y.presheaf.stalk y) Y.functionField
          (Y.presheaf.germ U y hy (j.elim F fun j => z j)) := by
      rintro (_ | ⟨j, hj⟩)
      · simp only [Option.elim]
        rw [hφ, algebraMap_germ]
      · simp only [Option.elim]
        rw [hc.val j hj, algebraMap_germ]
    have hc' : ∀ j : Option J, (j.elim c fun j => a j) < 1 := by
      rintro (_ | ⟨j, hj⟩)
      · exact hc1
      · exact ha j hj
    have key := GlobalTheory.IndepDiscrep.neg_one_lt_formOrd_sub_sum Y q n hn y U hy (dOn q z) hc.frame
      (Option J) (fun j => Y.presheaf.germ U y hy (j.elim F fun j => z j)) hmax
      (fun j => j.elim φ fun j => u j) (fun j => j.elim c fun j => a j) (hind hmax) hv hc' E hE
    rw [Fintype.sum_option] at key
    simp only [Option.elim] at key
    rw [Finset.sum_coe_sort J (fun j => a j * (E.ord (u j) : ℚ))] at key
    rw [hfφ]
    linarith

end GlobalTheory.Discrepancy
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrepancy_lt_adaptedCoords_independent_function : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  atlas_forward_decl GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem exists_mvPolynomial_of_forall_nhds {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} (P : (ι → ℂ) → X → Prop)
    (h : ∀ x₀ : X, ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧
      ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x ∈ W, P c x) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x, P c x := by
  classical
  choose W hW hxW Q hQ hP using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨∏ x ∈ t, Q x, Finset.prod_ne_zero_iff.2 fun x _ => hQ x, fun c hc y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  rw [map_prod] at hc
  exact hP x c (Finset.prod_ne_zero_iff.1 hc x hx) y hy

theorem exists_poly_neg_one_lt_discrep_member : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) [Fintype ι] (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (u i) * s i → ∀ y : Y, (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c : ℚ) (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c < 1 → (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g → (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y → -1 < discrep E η m g - c * E.ord f := by
  intro Y _ _ q n _ hproj B hB A ι _ s hs
  haveI : IsProper q := ((isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hproj).1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  refine (exists_mvPolynomial_of_forall_nhds (X := Y) (fun c y =>
    ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (c i) * s i →
    (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c' : ℚ)
      (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c' < 1 →
      (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g →
      (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y →
      -1 < discrep E η m g - c' * E.ord f) fun y₀ => ?_).imp
    fun Q ⟨hQ, hQc⟩ => ⟨hQ, fun c hc t ht y => hQc c hc y t ht⟩
  obtain ⟨W, hW, z, w, u, e, f, hfr, he, hf, hch⟩ := GlobalTheory.T.exists_affine_snc_chart_cartier_single_equation Y q n B hB A ι s hs y₀
  obtain ⟨Q, hQ, hQc⟩ := GlobalTheory.T.bertini_coordinateStrata_etaleChart_cotangent Y q n W z hfr ι f
  refine ⟨W, W.isOpen, hW, Q, hQ, fun c hc y hy t ht hgen η K Θ m c' g f' hη hK hm hΘ hc' hmult
    hg hf' E hE => ?_⟩
  obtain ⟨J, hJ, hJz⟩ := hch y hy
  have hFv : fnOf W (gen_mem hy) (∑ i, algX q W (c i) * f i) = ((t * e : Y.functionFieldˣ) : Y.functionField) := by
    rw [Units.val_mul, ht, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hf i, ← RingHom.comp_apply, fnOf_comp_algX, mul_assoc]
  have hunit : UnitAt y ((f' : Y.functionField) / ((t * e : Y.functionFieldˣ) : Y.functionField)) :=
    ((CartierDiv.isEqn_principal t y).add (he y hy)).iff_unitAt.1 hf'
  have hbas : ∃ i, y ∈ Y.basicOpen (f i) := by
    obtain ⟨i, hi⟩ := hgen
    refine ⟨i, (unitAt_fnOf_iff hy (gen_mem hy) (f i)).1 ?_⟩
    rw [hf i]
    exact (he y hy).generatesAt_iff.1 hi
  rw [GlobalTheory.T.discrepancy_eq_formOrder_sub_weighted_coordOrders Y q n B y W hy z J w u hJ η K Θ m g hη hK hm hΘ hg E hE]
  exact GlobalTheory.T.discrepancy_lt_adaptedCoords_independent_function Y q n B y W hy z J w u hJ hJz _ (fun h => hQc c hc y hy hbas J h) (t * e) f'
    (fun j => (Θ.mult (w j) : ℚ) / m) c' hFv.symm hunit (fun j hj => by
      have := hmult (w j) (hJ.spec j hj)
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      rw [div_lt_one hm']
      exact_mod_cast this) hc' E hE

end GlobalTheory.Discrepancy
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) [Fintype ι] (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (u i) * s i → ∀ y : Y, (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c : ℚ) (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c < 1 → (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g → (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y → -1 < discrep E η m g - c * E.ord f := by
  atlas_forward_decl GlobalTheory.Discrepancy.exists_poly_neg_one_lt_discrep_member
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeneralMember

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem regAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : RegAt (q y) f) : RegAt y (functionFieldMap q f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨q.stalkMap y a, (functionFieldMap_algebraMap q y a).symm⟩

theorem unitAt_functionFieldMap (q : Y ⟶ X) [IsDominant q] (y : Y) {f : X.functionField}
    (h : UnitAt (q y) f) : UnitAt y (functionFieldMap q f) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨q.stalkMap y a, ha.map _, (functionFieldMap_algebraMap q y a).symm⟩

theorem supp_nsmul_le (D : CartierDiv X) (r : ℕ) : (r • D).supp ≤ D.supp := by
  induction r with
  | zero => rw [zero_smul, CartierDiv.supp_eq_bot_iff.2 rfl]; exact bot_le
  | succ r ih => rw [succ_nsmul]; exact (CartierDiv.supp_add_le _ _).trans (sup_le ih le_rfl)

theorem functionFieldMap_mem_sections (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X}
    {f : X.functionField} (h : f ∈ A.sections) : functionFieldMap q f ∈ (pullCart q A).sections := by
  refine CartierDiv.mem_sections.2 fun y => ?_
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  have h1 := hg.regularAt_iff.1 (CartierDiv.mem_sections.1 h (q y))
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := regAt_functionFieldMap q y h1
  rwa [map_mul] at this

theorem generatesAt_pullCart (q : Y ⟶ X) [IsDominant q] {A : CartierDiv X} {y : Y}
    {f : X.functionField} (h : A.GeneratesAt (q y) f) :
    (pullCart q A).GeneratesAt y (functionFieldMap q f) := by
  obtain ⟨g, hg⟩ := A.exists_isEqn (q y)
  refine ⟨fnPull q g, isEqn_pullCart q hg, ?_⟩
  have := unitAt_functionFieldMap q y (hg.generatesAt_iff.1 h)
  rwa [map_mul] at this

variable [IsLocallyNoetherian X]

theorem isLogMult_add {p : X ⟶ Sp ℂ} {n : ℕ} {Δ : X → ℚ} {η : RatForms p n} {m m' b e : ℕ}
    {G D₀ : CartierDiv X} {a : ℚ} (hG : IsLogMult p n Δ η m G) (hm' : 0 < m') (he : 0 < e)
    (hab : a = b / e) :
    IsLogMult p n (Δ + a • qWeil D₀ m') η (m * (e * m')) ((e * m') • G + m • (b • D₀)) := by
  refine ⟨hG.ne_zero, Nat.mul_pos hG.pos (Nat.mul_pos he hm'), fun x g hg z hz E hE => ?_⟩
  obtain ⟨V, hV, hgV⟩ := hg.exists_nhds
  obtain ⟨g₁, hg₁⟩ := G.exists_isEqn z
  obtain ⟨d, hd⟩ := D₀.exists_isEqn z
  have h3 := ((hgV z (hz.mem_open V.isOpen hV)).mult_eq.symm.trans
    ((hg₁.nsmul (e * m')).add ((hd.nsmul b).nsmul m)).mult_eq)
  rw [← hE.ord_eq, ← hE.ord_eq, E.ord_mul, E.ord_pow, E.ord_pow, E.ord_pow] at h3
  have h4 := hG.eqn z g₁ hg₁ z specializes_rfl E hE
  have hd' := hd.mult_eq
  rw [← hE.ord_eq] at hd'
  have h1 : (m' : ℚ) ≠ 0 := by exact_mod_cast hm'.ne'
  have h2 : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, qWeil, hd', h3, hab]
  push_cast
  rw [← h4]
  field_simp
  ring

end GlobalTheory.GeneralMember

open GlobalTheory.GeneralMember in

theorem GlobalTheory.PairStep.kltAt_add_general_member : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  intro hP X _ _ _ p n hproj hn Δ D m G A ι _ s hm hG hD hs
  obtain ⟨η, hη⟩ := hG.exists_isLogMult hm
  obtain ⟨m', D₀, hm', -, rfl⟩ := hD
  obtain ⟨Y, hY, π, hπ, K, B, hres, hB⟩ :=
    GlobalTheory.T.exists_log_resolution hP ℂ X p n hproj hn η m G hη.ne_zero D₀.supp D₀.supp_ne_top
  haveI : IsNoetherian Y := isNoetherian_of_isProjOver hres.proj
  haveI := hres.smooth
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hproj).1
  haveI : IsProper (π ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hres.proj).1
  haveI : IsProper π := IsProper.of_comp π p
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary Y (π ≫ p) n hres.proj B hres.snc (pullCart π A) ι
    (fun i => functionFieldMap π (s i)) fun i => functionFieldMap_mem_sections π (hs i)
  refine ⟨Q, hQ0, fun u hu t ht y ⟨i, hi⟩ a c ha hc hklt => ?_⟩

  set b : ℕ := a.num.toNat with hb
  set e : ℕ := a.den with he
  have hepos : 0 < e := a.den_pos
  have hab : a = b / e := by
    have h0 : (0 : ℤ) ≤ a.num := Rat.num_nonneg.2 ha
    have h1 : ((a.num.toNat : ℕ) : ℚ) = (a.num : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    rw [hb, he, h1]
    exact (Rat.num_div_den a).symm
  set m'' := m * (e * m') with hm''
  set G' := (e * m') • G + m • (b • D₀) with hG'
  have hm''pos : 0 < m'' := Nat.mul_pos hm (Nat.mul_pos hepos hm')
  have hmult : IsLogMult p n (Δ + a • qWeil D₀ m') η m'' G' := isLogMult_add hη hm' hepos hab

  have hΘ : pullCart π G' - m'' • K = (e * m') • (pullCart π G - m • K) + (m * b) • pullCart π D₀ := by
    have hn1 : ∀ (r : ℕ) (D : CartierDiv X), pullCart π (r • D) = r • pullCart π D :=
      fun r D => map_nsmul (pullCartHom π) r D
    rw [hG', pullCart_add, hn1, hn1, hn1, hm'']
    module
  have hsupp : (pullCart π G' - m'' • K).supp ≤ B := by
    rw [hΘ]
    refine (CartierDiv.supp_add_le _ _).trans (sup_le ((supp_nsmul_le _ _).trans hres.supp)
      ((supp_nsmul_le _ _).trans fun w hw => hB w ((GlobalTheory.T.cartierDivisorPullback_support_and_effective X Y π D₀).1 w hw)))
  have hres' : IsLogRes p n η m'' G' π K B := { hres with supp := hsupp }

  obtain ⟨g'', hg''⟩ := G'.exists_isEqn y
  have hL := hmult.eqn y g'' hg''
  obtain ⟨ya, hya⟩ := A.exists_isEqn y
  have hH : (CartierDiv.principal t + A).IsEqn y (t * ya) := (CartierDiv.isEqn_principal t y).add hya
  have hHz : ∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal t + A) 1 z = (E.ord (t * ya) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    obtain ⟨V, hV, hHV⟩ := hH.exists_nhds
    rw [qWeil, (hHV z (hz.mem_open V.isOpen hV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, hL₂, hdisc⟩ := isLogEqn_add_smul X p n (Δ + a • qWeil D₀ m')
    (qWeil (CartierDiv.principal t + A) 1) η y m'' 1 g'' (t * ya) c hm''pos one_pos hL hHz
  rw [hL₂.kltAt_iff hn hη.ne_zero hm₂]
  intro E hE
  rw [hdisc]

  obtain ⟨E', hE'⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p π hres.bir E
  obtain ⟨y', rfl, hy'⟩ := GlobalTheory.T.divisor_center_proper_lift ℂ X Y p π hres.bir inferInstance E' E hE' y hE
  have hη' : EtaleKlt.ratPull p π n η ≠ 0 := fun h =>
    hη.ne_zero ((GlobalTheory.T.rationalTopFormPullback_bijective_birational ℂ X Y p π hres.bir n).1 (h.trans (map_zero _).symm))
  have hΘm : ∀ w, w ⤳ y' → (pullCart π G' - m'' • K).mult w < m'' := fun w hw =>
    ((GlobalTheory.T.log_resolution_multiplier_local ℂ X p n hproj hn _ η m'' G' Y π K B hmult hres' (π y')).1.1 hklt) w
      (hw.map π.continuous)
  have hΘe : (pullCart π G' - m'' • K + m'' • K).IsEqn y' (fnPull π g'') := by
    rw [sub_add_cancel]; exact isEqn_pullCart π hg''
  have ht' : ((fnPull π t : Y.functionFieldˣ) : Y.functionField) =
      ∑ i, Cartier.constFn (π ≫ p) (u i) * functionFieldMap π (s i) := by
    change functionFieldMap π (t : X.functionField) = _
    rw [ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← EtaleKlt.functionFieldMap_comp_constFn p π, RingHom.comp_apply]
  have hH' : (CartierDiv.principal (fnPull π t) + pullCart π A).IsEqn y' (fnPull π (t * ya)) := by
    rw [map_mul]; exact (CartierDiv.isEqn_principal _ y').add (isEqn_pullCart π hya)
  have key := hQ u hu (fnPull π t) ht' y' ⟨i, generatesAt_pullCart π hi⟩ (EtaleKlt.ratPull p π n η)
    K (pullCart π G' - m'' • K) m'' c (fnPull π g'') (fnPull π (t * ya)) hη' hres.div hm''pos
    hsupp hc hΘm hΘe hH' E' hy'
  have e1 := GlobalTheory.T.form_order_birational_pullback ℂ X Y p π hres.bir E' E hE' n η hη.ne_zero
  have e2 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' g''
  have e3 := GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p π hres.bir E' E hE' (t * ya)
  simp only [discrep, e1, e2, e3] at key
  simpa [discrep] using key
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataLogTerminal_add_generalMember_linearSystem : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (ι : Type) [Fintype ι] (s : ι → X.functionField), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : X.functionFieldˣ, (t : X.functionField) = ∑ i, Cartier.constFn p (u i) * s i → ∀ y : X, (∃ i, A.GeneratesAt y (s i)) → ∀ a c : ℚ, 0 ≤ a → c < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + c • qWeil (GlobalTheory.Cartier.CartierDiv.principal t + A) 1) y := by
  atlas_forward_decl GlobalTheory.PairStep.kltAt_add_general_member
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  first | exact @GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | exact GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | (intros; apply GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.IdGenRat

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    ∃ r, Presents (l • A) (lbPow (toLB A) l) r := by
  have h := GlobalTheory.CombChern.presents_zpow (presents_toLB A) (l : ℤ)
  rw [natCast_zsmul] at h
  exact ⟨_, h⟩

theorem exists_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  intro X _ _ p hp A z hA
  obtain ⟨l₁, hl₁⟩ := Filter.eventually_atTop.1
    (GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed X p hp (toLB A) (Closeds.closure {z}) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  obtain ⟨r, κ, -, hz, hy⟩ := hl₁ l hl
  obtain ⟨ρ, hρ⟩ := presents_lbPow_toLB A l
  refine ⟨r, fun i => hρ.rat (κ i), fun i => hρ.rat_mem _, fun i => ?_, fun y hy' => ?_⟩
  · exact (hρ.vanishesAt_rat_iff _).2 (hz i z (subset_closure rfl))
  · have hyZ : y ∉ Closeds.closure ({z} : Set X) := fun h => hy' (specializes_iff_mem_closure.2 h)
    obtain ⟨i, hi⟩ := hy y hyZ
    exact ⟨i, (hρ.generatesAt_rat_iff _).2 hi⟩

end GlobalTheory.IdGenRat
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∃ (r : ℕ) (κ : Fin r → X.functionField), (∀ i, κ i ∈ (l • A).sections) ∧ (∀ i, (l • A).VanishesAt z (κ i)) ∧ ∀ y, ¬ z ⤳ y → ∃ i, (l • A).GeneratesAt y (κ i) := by
  atlas_forward_decl GlobalTheory.IdGenRat.exists_sections_vanish_generate
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.GeneralLift

theorem unitAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0) (x : X) :
    GlobalTheory.Cartier.UnitAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.unitAt_fnOf (U := ⊤) trivial trivial
    (Units.map (algX p ⊤ : ℂ →+* Γ(X, ⊤)).toMonoidHom (Units.mk0 a ha))

theorem regAt_constFn {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) (a : ℂ) (x : X) :
    GlobalTheory.Cartier.RegAt x (GlobalTheory.Cartier.constFn p a) :=
  GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial (algX p ⊤ a)

theorem principal_const {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp ℂ) {a : ℂ} (ha : a ≠ 0)
    (w : X.functionFieldˣ) (hw : (w : X.functionField) = GlobalTheory.Cartier.constFn p a) :
    GlobalTheory.Cartier.CartierDiv.principal w = 0 :=
  GlobalTheory.Cartier.CartierDiv.ext_of_isEqn fun x =>
    ⟨1, (GlobalTheory.Cartier.CartierDiv.isEqn_principal w x).iff_unitAt.2 (by
      rw [Units.val_one, one_div, hw]; exact (unitAt_constFn p ha x).inv),
      GlobalTheory.Cartier.CartierDiv.isEqn_zero x⟩

end GlobalTheory.GeneralLift

open GlobalTheory.GeneralLift in

theorem GlobalTheory.GeneralLift.exists_lift_klt : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (m : ℕ) (G A : CartierDiv X) (z : X), 0 < m → IsLogCanonicalMultiple p n Δ m G → IsQCart D → IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l → ∀ f₀ ∈ (l • A).sections, ∃ u : X.functionField, u ∈ (l • A).sections ∧ (l • A).VanishesAt z u ∧ ∀ g : X.functionFieldˣ, (g : X.functionField) = f₀ + u → ∀ y, ¬ z ⤳ y → ∀ a t : ℚ, 0 ≤ a → t < 1 → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + t • qWeil (GlobalTheory.Cartier.CartierDiv.principal g + l • A) 1) y := by
  intro hP X _ _ _ p n hp hn Δ D m G A z hm hG hD hA
  obtain ⟨l₁, hl₁⟩ := GlobalTheory.T.exists_ampleMultiple_sections_vanish_generate X p hp A z hA
  refine ⟨l₁, fun l hl f₀ hf₀ => ?_⟩
  obtain ⟨r, κ, hκs, hκv, hκg⟩ := hl₁ l hl
  let s : Option (Fin r) → X.functionField := fun i => Option.elim i f₀ κ
  have hs : ∀ i, s i ∈ (l • A).sections := by
    rintro (_ | i)
    exacts [hf₀, hκs i]
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.kawamataLogTerminal_add_generalMember_linearSystem hP X p n hp hn Δ D m G (l • A) (Option (Fin r)) s hm hG hD hs
  obtain ⟨v, hv⟩ : ∃ v : Option (Fin r) → ℂ, MvPolynomial.eval v (Q * MvPolynomial.X none) ≠ 0 := by
    by_contra h
    push_neg at h
    exact mul_ne_zero hQ (MvPolynomial.X_ne_zero _) (MvPolynomial.funext fun v => by rw [h v, map_zero])
  rw [map_mul, MvPolynomial.eval_X] at hv
  have hv0 : v none ≠ 0 := right_ne_zero_of_mul hv
  have hvQ : MvPolynomial.eval v Q ≠ 0 := left_ne_zero_of_mul hv
  refine ⟨∑ i : Fin r, GlobalTheory.Cartier.constFn p (v (some i) / v none) * κ i, ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    exact GlobalTheory.Cartier.CartierDiv.mem_sections.2 fun x =>
      (GlobalTheory.Cartier.CartierDiv.mem_sections.1 (hκs i) x).regAt_mul (regAt_constFn p _ x)
  · refine Finset.sum_induction _ (fun f => (l • A).VanishesAt z f)
      (fun _ _ h h' => h.add h') ((l • A).vanishesAt_zero z) fun i _ => ?_
    obtain ⟨g, hg, hz⟩ := hκv i
    exact ⟨g, hg, by convert hz.mul (regAt_constFn p (v (some i) / v none) z) using 1; ring⟩
  · intro g hg y hy a t ha ht hk
    have hc : GlobalTheory.Cartier.constFn p (v none) ≠ 0 := (map_ne_zero _).2 hv0
    have key := hQe v hvQ (Units.mk0 _ hc * g) (by
      rw [Units.val_mul, Units.val_mk0, hg, Fintype.sum_option, mul_add, Finset.mul_sum]
      refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun i _ => ?_)
      rw [← mul_assoc, ← map_mul, mul_div_cancel₀ _ hv0]
      rfl) y (have ⟨i, hi⟩ := hκg y hy; ⟨some i, hi⟩) a t ha ht hk
    rwa [GlobalTheory.Cartier.CartierDiv.principal_mul, principal_const p hv0 _ (Units.val_mk0 hc),
      zero_add] at key
end
