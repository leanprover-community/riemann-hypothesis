import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsClosedOfChartIdeal
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

section
namespace ReciprocityTheory.AnForm.R.WMult

open AlgebraicGeometry CategoryTheory MvPolynomial

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}

theorem secHom_surjective (P : AffPres s) : Function.Surjective P.secHom := by
  unfold AffPres.secHom
  rw [RingHom.coe_comp, RingHom.coe_comp, RingHom.coe_comp]
  have i1 : IsIso P.iso.hom.appTop := by
    have : IsIso (Scheme.Γ.map P.iso.hom.op) := inferInstance
    simpa using this
  refine (ConcreteCategory.bijective_of_isIso P.V.topIso.hom).2.comp ?_
  refine (ConcreteCategory.bijective_of_isIso P.iso.hom.appTop).2.comp ?_
  refine (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).inv).2.comp ?_
  exact Ideal.Quotient.mk_surjective

theorem isUnit_algebraMap_of_eval_ne_zero {n : ℕ} (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p : Fin n → ℂ) {g : MvPolynomial (Fin n) ℂ} (hg : eval p g ≠ 0) :
    IsUnit (algebraMap _ (locRing K p) g) := by
  have hg' : g ∉ ptIdeal p := fun h => hg (RingHom.mem_ker.mp h)
  have := (IsLocalization.map_units (locPt p) (⟨g, hg'⟩ : (ptIdeal p).primeCompl)).map
    (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K))
  rwa [Ideal.Quotient.mk_algebraMap] at this

theorem algebraMap_eq_zero_of_mem {n : ℕ} {K : Ideal (MvPolynomial (Fin n) ℂ)} (p : Fin n → ℂ)
    {k : MvPolynomial (Fin n) ℂ} (hk : k ∈ K) : algebraMap _ (locRing K p) k = 0 := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hk

theorem map_bd_eq_span {m : ℕ} {I bd : Ideal (MvPolynomial (Fin m) ℂ)} {p : Fin m → ℂ} {e rc : ℕ}
    (S : SncData I bd p e rc) :
    Ideal.map (algebraMap _ (locRing I p)) bd =
      Ideal.span {∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)} := by
  obtain ⟨v, hv⟩ := isUnit_algebraMap_of_eval_ne_zero I p S.eval_h
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    have h1 := S.le_span g hg
    have h3 : Ideal.map (algebraMap _ (locRing I p)) (Ideal.span {∏ l ∈ S.J, S.r l} ⊔ I) ≤
        Ideal.span {∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)} := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_prod]
      refine sup_le le_rfl ?_
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, algebraMap_eq_zero_of_mem p hk]
      exact Ideal.zero_mem _
    have h2 := h3 (Ideal.mem_map_of_mem _ h1)
    rw [map_mul] at h2
    have he : algebraMap _ (locRing I p) g =
        ↑v⁻¹ * (algebraMap _ (locRing I p) S.h * algebraMap _ (locRing I p) g) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ h2
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have h1 := Ideal.mem_map_of_mem (algebraMap _ (locRing I p)) S.mem_bd
    rw [map_mul, map_prod] at h1
    have he : ∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l) =
        ↑v⁻¹ * (algebraMap _ (locRing I p) S.h * ∏ l ∈ S.J, algebraMap _ (locRing I p) (S.r l)) := by
      rw [← hv, ← mul_assoc, Units.inv_mul, one_mul]
    rw [he]
    exact Ideal.mul_mem_left _ _ h1

theorem stalkId_eq_span_of_sncData (P : AffPres s) (Z : W.IdealSheafData) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) {e rc : ℕ} (S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc) :
    FinalTheorems.stalkId Z x = Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l))} := by
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  have hsecmap : Z.ideal P.affOpen = Ideal.map P.secHom (P.bdIdeal Z) :=
    (Ideal.map_comap_of_surjective _ (secHom_surjective P) _).symm
  have hcompψ : (((P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx)).comp
      (W.presheaf.germ P.V x hx).hom).comp P.secHom) =
      algebraMap _ (locRing P.K (P.coord x hx)) :=
    RingHom.ext hψ
  have e1 : Ideal.map (P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx))
      (FinalTheorems.stalkId Z x) =
      Ideal.map (P.stalkEquiv x hx hcl : W.presheaf.stalk x →+* locRing P.K (P.coord x hx))
        (Ideal.span {∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l))}) := by
    have hZmap : FinalTheorems.stalkId Z x = Ideal.map (W.presheaf.germ P.V x hx).hom
        (Ideal.map P.secHom (P.bdIdeal Z)) := by
      rw [← hsecmap]; exact stalkId_eq_map_germ Z x P.affOpen hx
    rw [hZmap, Ideal.map_map, Ideal.map_map, hcompψ, map_bd_eq_span S,
      Ideal.map_span, Set.image_singleton, map_prod]
    simp only [RingHom.coe_coe, hψ]
  have := congrArg (Ideal.map ((P.stalkEquiv x hx hcl).symm :
    locRing P.K (P.coord x hx) →+* W.presheaf.stalk x)) e1
  rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this

theorem rsp_of_sncData (P : AffPres s) (Z : W.IdealSheafData) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) {e rc : ℕ} (hdim : ringKrullDim (W.presheaf.stalk x) = e)
    (S : SncData P.K (P.bdIdeal Z) (P.coord x hx) e rc) :
    FinalTheorems.Rsp (W.presheaf.stalk x) e (fun l => W.presheaf.germ P.V x hx (P.secHom (S.r l))) := by
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  rw [P.rsp_iff x hx hcl]
  refine ⟨?_, ?_⟩
  · simp only [hψ]
    exact S.span_eq
  · rw [← P.ringKrullDim_stalk x hx hcl, hdim]

end ReciprocityTheory.AnForm.R.WMult
end

section
namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

variable {W : Scheme.{0}}

open Classical in

def ordAlong (G : W.IdealSheafData) (C : Set W) : ℕ :=
  if h : IsIrreducible C then
    (Module.length (W.presheaf.stalk h.genericPoint)
      (W.presheaf.stalk h.genericPoint ⧸ FinalTheorems.stalkId G h.genericPoint)).toNat
  else 0

theorem stalkId_eq_monomial [IsNoetherian W] {Z G : W.IdealSheafData} (hG : FinalTheorems.EffCartier G)
    (hGZ : (G.support : Set W) ⊆ Z.support) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) {n : ℕ}
    (f : Fin n → Γ(W, U.1)) (J : Finset (Fin n)) [IsRegularLocalRing (W.presheaf.stalk y)]
    (hrsp : FinalTheorems.Rsp (W.presheaf.stalk y) n (fun i => W.presheaf.germ U.1 y hy (f i)))
    (hZy : FinalTheorems.stalkId Z y = Ideal.span {∏ i ∈ J, W.presheaf.germ U.1 y hy (f i)})
    (σ : Fin n → Set W) (hσ : ∀ i ∈ J, IsBranch (Z.support : Set W) (f i) y (σ i)) :
    FinalTheorems.stalkId G y =
      Ideal.span {∏ i ∈ J, W.presheaf.germ U.1 y hy (f i) ^ ordAlong G (σ i)} := by
  classical
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(W, U.1) (W.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf yU
  have hlocY : IsLocalization.AtPrime (W.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  set f' : Fin n → W.presheaf.stalk y := fun i => W.presheaf.germ U.1 y hy (f i) with hf'

  obtain ⟨U', g, hyU', hg, hGU'⟩ := hG y
  set γ : W.presheaf.stalk y := W.presheaf.germ U'.1 y hyU' g with hγ
  have hGy : FinalTheorems.stalkId G y = Ideal.span {γ} := by
    rw [WMult.stalkId_eq_map_germ G y U' hyU', hGU', Ideal.map_span, Set.image_singleton]
  have hγ0 : γ ≠ 0 := by
    intro h0
    have hU' : IsAffineOpen U'.1 := U'.2
    let : Algebra Γ(W, U'.1) (W.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨y, hyU'⟩ : U'.1)
    have := hU'.isLocalization_stalk ⟨y, hyU'⟩
    obtain ⟨⟨c, hc⟩, hcg⟩ := (IsLocalization.map_eq_zero_iff
      (M := (hU'.primeIdealOf ⟨y, hyU'⟩).asIdeal.primeCompl) (S := W.presheaf.stalk y) g).mp h0
    have hc0 : c = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff hg).mp hcg
    exact hc (by rw [hc0]; exact Ideal.zero_mem _)

  have hrad : (∏ i ∈ J, f' i) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    have := hQ
    let P : PrimeSpectrum Γ(W, U.1) := ⟨Q.comap (W.presheaf.germ U.1 y hy).hom, inferInstance⟩
    have h1 : hU.fromSpec P ∈ (G.support : Set W) := by
      rw [WMult.mem_support_fromSpec_iff G U hU]
      show G.ideal U ≤ Q.comap (W.presheaf.germ U.1 y hy).hom
      rw [← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ G y U hy, hGy]
      exact hQγ
    have h2 := hGZ h1
    rw [WMult.mem_support_fromSpec_iff Z U hU] at h2
    have h3 : FinalTheorems.stalkId Z y ≤ Q := by
      rw [WMult.stalkId_eq_map_germ Z y U hy]; exact Ideal.map_le_iff_le_comap.mpr h2
    rw [hZy] at h3
    exact h3 (Ideal.mem_span_singleton_self _)
  obtain ⟨u, m, hmJ, hγu⟩ := eq_unit_mul_monomial f' hrsp.1 hrsp.2 J hγ0 hrad

  have hord : ∀ i ∈ J, ordAlong G (σ i) = m i := by
    intro i hi
    obtain ⟨hCc, hyC, hirr, hηU, hηf⟩ := hσ i hi
    have hCm : Maximal (fun C => IsIrreducible C ∧ C ⊆ (Z.support : Set W)) (σ i) := hCc
    have hCcl : IsClosed (σ i) := by
      have h := hCm.eq_of_subset ⟨hirr.closure, closure_minimal hCm.1.2 Z.support.isClosed⟩
        subset_closure
      rw [h]; exact isClosed_closure
    have hgen : IsGenericPoint hirr.genericPoint (σ i) := by
      have := hirr.isGenericPoint_genericPoint_closure
      rwa [hCcl.closure_eq] at this
    set η := hirr.genericPoint with hη
    have hηy : η ⤳ y := hgen.specializes hyC
    let Pη := hU.primeIdealOf ⟨η, hηU⟩
    have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hηU⟩
    have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
    have emb := hU.fromSpec.isOpenEmbedding
    have hspec : ∀ P Q : PrimeSpectrum Γ(W, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
      intro P Q
      rw [PrimeSpectrum.le_iff_specializes]
      exact emb.isInducing.specializes_iff
    have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
    have hfη : f i ∈ Pη.asIdeal := by
      have h' : η ∈ W.zeroLocus {f i} ∩ U.1 := ⟨hηf, hηU⟩
      rw [← hU.fromSpec_image_zeroLocus] at h'
      obtain ⟨Q, hQ, hQη⟩ := h'
      rw [← hfromη] at hQη
      have := emb.injective hQη
      subst this
      exact (PrimeSpectrum.mem_zeroLocus _ _).mp hQ (Set.mem_singleton _)
    have hpi : Prime (f' i) := prime_of_regular_params f' hrsp.1 hrsp.2 i
    have hQi : (Ideal.span {f' i}).IsPrime := (Ideal.span_singleton_prime hpi.ne_zero).mpr hpi
    let Pi : PrimeSpectrum Γ(W, U.1) :=
      ⟨(Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)), inferInstance⟩
    have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(W, U.1)) Pη.asIdeal :=
      Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
    have hPiη : Pi ≤ Pη := by
      show (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) ≤ Pη.asIdeal
      calc _ ≤ (Pη.asIdeal.map (algebraMap Γ(W, U.1) (W.presheaf.stalk y))).comap
              (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) := by
            apply Ideal.comap_mono
            rw [Ideal.span_le, Set.singleton_subset_iff]
            exact Ideal.mem_map_of_mem _ hfη
        _ = Pη.asIdeal := IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
              (W.presheaf.stalk y) Pη.isPrime hdisj
    have hζZ : hU.fromSpec Pi ∈ (Z.support : Set W) := by
      rw [WMult.mem_support_fromSpec_iff Z U hU]
      show Z.ideal U ≤ (Ideal.span {f' i}).comap (W.presheaf.germ U.1 y hy).hom
      rw [← Ideal.map_le_iff_le_comap, ← WMult.stalkId_eq_map_germ Z y U hy, hZy, Ideal.span_le,
        Set.singleton_subset_iff]
      exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem _ hi)
    have hζη : hU.fromSpec Pi ⤳ η := by rw [← hfromη]; exact (hspec _ _).mpr hPiη
    have hcl : closure {η} = σ i := hgen
    have hsub : σ i ⊆ closure {hU.fromSpec Pi} := by
      intro z hz
      rw [← hcl] at hz
      exact specializes_iff_closure_subset.mp hζη hz
    have hirrζ : IsIrreducible (closure {hU.fromSpec Pi}) := isIrreducible_singleton.closure
    have hsubZ : closure {hU.fromSpec Pi} ⊆ (Z.support : Set W) :=
      closure_minimal (Set.singleton_subset_iff.mpr hζZ) Z.support.isClosed
    have hCeq : σ i = closure {hU.fromSpec Pi} := hCm.eq_of_subset ⟨hirrζ, hsubZ⟩ hsub
    have hηζ : η ⤳ hU.fromSpec Pi := by
      rw [specializes_iff_mem_closure, hcl, hCeq]
      exact subset_closure (Set.mem_singleton _)
    have hηPi : Pη ≤ Pi := (hspec _ _).mp (by rw [hfromη]; exact hηζ)
    have hPeq : Pη.asIdeal =
        (Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) :=
      congrArg PrimeSpectrum.asIdeal (le_antisymm hηPi hPiη)

    let T := Localization.AtPrime (Ideal.span {f' i})
    have hT : IsLocalization.AtPrime T
        ((Ideal.span {f' i}).comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Py.asIdeal.primeCompl) (S := W.presheaf.stalk y) (T := T) (Ideal.span {f' i})
    have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
      have hsm : Pη.asIdeal.primeCompl =
          (Ideal.comap (algebraMap Γ(W, U.1) (W.presheaf.stalk y)) (Ideal.span {f' i})).primeCompl := by
        ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
      rw [hsm]; exact hT
    let ηU : U.1 := ⟨η, hηU⟩
    let algη : Algebra Γ(W, U.1) (W.presheaf.stalk η) :=
      TopCat.Presheaf.algebra_section_stalk W.presheaf ηU
    have hlocη : IsLocalization.AtPrime (W.presheaf.stalk η) Pη.asIdeal :=
      hU.isLocalization_stalk ηU
    let φ : W.presheaf.stalk η ≃ₐ[Γ(W, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
    let algYη : Algebra (W.presheaf.stalk y) (W.presheaf.stalk η) :=
      (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (W.presheaf.stalk y) T)).toAlgebra
    have hlocYη : IsLocalization.AtPrime (W.presheaf.stalk η) (Ideal.span {f' i}) :=
      (IsLocalization.isLocalization_iff_of_ringEquiv (M := (Ideal.span {f' i}).primeCompl)
        (S := T) φ.symm.toRingEquiv).mp inferInstance
    have hgerm : ∀ a : Γ(W, U.1), W.presheaf.germ U.1 η hηU a =
        algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) (W.presheaf.germ U.1 y hy a) :=
by
      intro a
      have h1 := (φ.symm.commutes a).symm
      rw [IsScalarTower.algebraMap_apply Γ(W, U.1) (W.presheaf.stalk y) T] at h1
      exact h1
    have hGη : FinalTheorems.stalkId G η =
        Ideal.span {algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η) γ} := by
      rw [WMult.stalkId_eq_map_germ G η U hηU]
      have hcomp : (W.presheaf.germ U.1 η hηU).hom =
          (algebraMap (W.presheaf.stalk y) (W.presheaf.stalk η)).comp
            (W.presheaf.germ U.1 y hy).hom :=
        RingHom.ext fun a => hgerm a
      rw [hcomp, ← Ideal.map_map, ← WMult.stalkId_eq_map_germ G y U hy, hGy, Ideal.map_span,
        Set.image_singleton]
    have hordS := WMult.ord_isLocalization_eq_exponent f' hrsp.1 hrsp.2 J u m i hi
      (W.presheaf.stalk η)
    have hlen : Module.length (W.presheaf.stalk η) (W.presheaf.stalk η ⧸ FinalTheorems.stalkId G η) =
        (m i : ℕ∞) := by
      rw [hGη, hγu]; exact hordS
    unfold ordAlong
    rw [dif_pos hirr, ← hη, hlen]
    exact ENat.toNat_natCast (m i)
  rw [hGy, hγu]
  have hprod : ∏ i ∈ J, f' i ^ m i = ∏ i ∈ J, f' i ^ ordAlong G (σ i) :=
    Finset.prod_congr rfl fun i hi => by rw [hord i hi]
  rw [hprod]
  exact Ideal.span_singleton_mul_left_unit u.isUnit _

section Chart

variable {s : W ⟶ Spec (.of ℂ)}

theorem monomial_chart [IsNoetherian W] [LocallyOfFiniteType s] {Z G : W.IdealSheafData}
    (hG : FinalTheorems.EffCartier G) (hGZ : (G.support : Set W) ⊆ Z.support) (P : AffPres s) {rc : ℕ}
    (c : Fin rc ≃ comps (Z.support : Set W)) (e : ℕ) (x : W) (hx : x ∈ P.V)
    (hcl : IsClosed ({x} : Set W)) [IsRegularLocalRing (W.presheaf.stalk x)]
    (hdim : ringKrullDim (W.presheaf.stalk x) = e) {pt : Fin P.n → ℂ} (hpt : P.coord x hx = pt)
    (S : SncData P.K (P.bdIdeal Z) pt e rc)
    (hσ : ∀ l ∈ S.J, ∃ k, S.σ l = some k ∧
      IsBranch (Z.support : Set W) (P.secHom (S.r l)) x (c k))
    (a : MvPolynomial (Fin P.n) ℂ)
    (ha : FinalTheorems.stalkId G x = Ideal.span {W.presheaf.germ P.V x hx (P.secHom a)}) :
    ∃ u : locRing P.K pt, IsUnit u ∧
      algebraMap _ (locRing P.K pt) a =
        u * ∏ l ∈ S.J, algebraMap _ (locRing P.K pt) (S.r l) ^
          (S.σ l).elim 0 fun k => ordAlong G (c k) := by
  classical
  subst hpt
  have hψ : ∀ g, P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom g)) =
      algebraMap _ (locRing P.K (P.coord x hx)) g :=
    P.stalkEquiv_germ x hx hcl
  have : IsDomain (W.presheaf.stalk x) := isDomain_of_isRegularLocalRing
  let σ' : Fin e → Set W := fun l => (S.σ l).elim ∅ fun k => (c k : Set W)
  have hσ' : ∀ l ∈ S.J, IsBranch (Z.support : Set W) (P.secHom (S.r l)) x (σ' l) := by
    intro l hl
    obtain ⟨k, hk, hb⟩ := hσ l hl
    show IsBranch _ _ x ((S.σ l).elim ∅ fun k => (c k : Set W))
    rw [hk]
    exact hb
  have hmain : FinalTheorems.stalkId G x = Ideal.span {∏ l ∈ S.J,
      W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)} :=
    stalkId_eq_monomial (U := P.affOpen) hG hGZ x hx (fun l => P.secHom (S.r l)) S.J
      (WMult.rsp_of_sncData P Z x hx hcl hdim S) (WMult.stalkId_eq_span_of_sncData P Z x hx hcl S)
      σ' hσ'
  rw [ha] at hmain
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hmain
  refine ⟨P.stalkEquiv x hx hcl ↑v⁻¹, (Units.isUnit v⁻¹).map _, ?_⟩
  have hv' : W.presheaf.germ P.V x hx (P.secHom a) =
      (∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)) * ↑v⁻¹ := by
    rw [← hv, mul_assoc, Units.mul_inv, mul_one]
  have hprod : P.stalkEquiv x hx hcl
      (∏ l ∈ S.J, W.presheaf.germ P.V x hx (P.secHom (S.r l)) ^ ordAlong G (σ' l)) =
      ∏ l ∈ S.J, algebraMap _ (locRing P.K (P.coord x hx)) (S.r l) ^
          (S.σ l).elim 0 fun k => ordAlong G (c k) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun l hl => ?_
    obtain ⟨k, hk, -⟩ := hσ l hl
    rw [map_pow]
    show P.stalkEquiv x hx hcl (W.presheaf.germ P.V x hx (P.secHom (S.r l))) ^
      ordAlong G ((S.σ l).elim ∅ fun k => (c k : Set W)) = _
    rw [hψ, hk]
    rfl
  rw [← hψ a, hv', map_mul, hprod]
  exact mul_comm _ _

end Chart

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

theorem surj' (hD : IsMultiHomogIdeal D) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts P)
    (hzD : z ∉ conePts D) :
    ∃ c, ∃ x ∈ w.src c, SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) z := by
  have := w.isIso_off
  obtain ⟨p, hzp, -⟩ := exists_chart z hz.1
  have hzc : ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 :=
    (mem_conePts_iff_chartIdeal hP p z hzp).1 hz
  obtain ⟨y, hy, hyc, hyv⟩ := exists_closed_of_chartIdeal (hP := hP) p (affCoord p z) hzc
  have hyB : y ∈ projBCompl P D hP := by
    intro hB
    have h1 := (mem_projB_iff_val hD p y hy hyc).1 hB
    rw [funext hyv] at h1
    exact hzD ((mem_conePts_iff_affCoord hD p z hzp).2 h1)
  obtain ⟨x, ⟨hxc, -⟩, hxy⟩ := (bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP)
    (sX := toSpecC hP) w.π rfl (projBCompl P D hP)).2.2 ⟨hyc, hyB⟩
  subst hxy
  have hxp : x ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hy
  rw [← w.iSup_pres p] at hxp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hxp
  refine ⟨⟨p, i⟩, ⟨x, hxc⟩, hi, ?_⟩
  have hl : (fun q => eval (w.coord ⟨p, i⟩ ⟨x, hxc⟩) (w.lift ⟨p, i⟩ q)) = affCoord p z := by
    funext q
    rw [w.lift_eval_eq_val ⟨p, i⟩ ⟨x, hxc⟩ hi q]
    exact hyv q
  rw [hl]
  exact sameOrbit_symm' (sameOrbit_affCoord p z hzp)

theorem inj' (hD : IsMultiHomogIdeal D) (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c) (x' : w.M)
    (hx' : x' ∈ w.src c') (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D)
    (ho : SameOrbit (fun q => eval (w.coord c x) (w.lift c q))
      (fun q => eval (w.coord c' x') (w.lift c' q))) : x = x' := by
  have := w.isIso_off
  obtain ⟨a, ha0, ha⟩ := ho
  have hxc : w.π.base x.1 ∈ (chartOpen hP c.1).1 := w.le_pres c.1 c.2 hx
  have hone : ∀ k, eval (w.coord c x) (w.lift c ⟨k, c.1 k⟩) = 1 := fun k => by simp [lift]
  have hx'c : ∀ k, eval (w.coord c' x') (w.lift c' ⟨k, c.1 k⟩) ≠ 0 := by
    intro k h0
    have := congrFun ha ⟨k, c.1 k⟩
    simp only [hone k, h0, mul_zero] at this
    exact one_ne_zero this
  have hpx' : w.π.base x'.1 ∈ (chartOpen hP c.1).1 := (w.mem_chartOpen_iff c' x' hx' c.1).2 hx'c
  have heq : w.π.base x.1 = w.π.base x'.1 := by
    refine eq_of_val_chartCoord c.1 _ _ hxc hpx' (w.isClosed_image c x hx)
      (w.isClosed_image c' x' hx') fun q => ?_
    rw [w.val_chartCoord c x hx c.1 hxc q, w.val_chartCoord c' x' hx' c.1 hpx' q,
      affCoord_eq_of_sameOrbit c.1 ⟨a, ha0, ha⟩]
  have hxU : w.π.base x.1 ∈ projBCompl P D hP :=
    fun h => hxD ((w.mem_projB_iff_lift hD c x hx).1 h)
  have hbij := bijOn_closedPoints_of_isIso (sW := w.π ≫ toSpecC hP) (sX := toSpecC hP) w.π rfl
    (projBCompl P D hP)
  exact Subtype.ext (hbij.injOn ⟨x.2, hxU⟩ ⟨x'.2, heq ▸ hxU⟩ heq)

end WData

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {n : ℕ}

theorem ptIdeal_isMaximal (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨MvPolynomial.C c, by simp⟩)

private theorem withBot_add_right_cancel {a b : WithBot ℕ∞} {c : ℕ∞} {N : ℕ}
    (h : a + (c : WithBot ℕ∞) = b + c) (hb : b + (c : WithBot ℕ∞) = N) : a = b := by
  induction b using WithBot.recBotCoe with
  | bot => simp at hb
  | coe y =>
    induction a using WithBot.recBotCoe with
    | bot => rw [← h] at hb; simp at hb
    | coe x =>
      rw [← WithBot.coe_add, ← WithBot.coe_add, WithBot.coe_inj] at h
      rw [← WithBot.coe_add] at hb
      have hc : c ≠ ⊤ := by
        rintro rfl
        rw [add_top] at hb
        rw [← WithBot.coe_natCast, WithBot.coe_inj] at hb
        exact ENat.top_ne_natCast N hb
      exact congrArg _ (WithTop.add_right_cancel hc h)

theorem regular_point_unique_minimalPrime (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    [IsRegularLocalRing (locRing K p)] :
    ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptIdeal p ∧
      (∀ 𝔮' ∈ K.minimalPrimes, 𝔮' ≤ ptIdeal p → 𝔮' = 𝔮) ∧
      ringKrullDim (locRing K p) + (𝔮.height : WithBot ℕ∞) = n := by
  set A := MvPolynomial (Fin n) ℂ
  set P := ptIdeal p
  set S := locPt p
  set I : Ideal S := Ideal.map (algebraMap A S) K with hI
  have : IsDomain (S ⧸ I) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  have hIp : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp inferInstance
  set 𝔮 : Ideal A := I.under A with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.under A I
  have hdisj : Disjoint (P.primeCompl : Set A) 𝔮 :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint P.primeCompl S I).mp hIp).2
  have h𝔮P : 𝔮 ≤ P := by
    intro x hx
    by_contra hxP
    exact Set.disjoint_left.mp hdisj (show x ∈ (P.primeCompl : Set A) from hxP) hx
  have hK𝔮 : K ≤ 𝔮 := fun x hx => Ideal.mem_map_of_mem _ hx

  have key : ∀ Q : Ideal A, Q.IsPrime → K ≤ Q → Q ≤ P → 𝔮 ≤ Q := by
    intro Q hQ hKQ hQP
    have hd : Disjoint (P.primeCompl : Set A) Q := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hQP hxQ)
    have hmap : I ≤ Ideal.map (algebraMap A S) Q := Ideal.map_mono hKQ
    calc 𝔮 ≤ (Ideal.map (algebraMap A S) Q).under A := Ideal.comap_mono hmap
      _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl S hQ hd
  have hmin : 𝔮 ∈ K.minimalPrimes :=
    ⟨⟨h𝔮p, hK𝔮⟩, fun Q ⟨hQ, hKQ⟩ hQ𝔮 => key Q hQ hKQ (hQ𝔮.trans h𝔮P)⟩
  refine ⟨𝔮, hmin, h𝔮P, ?_, ?_⟩
  · intro 𝔮' h' h'P
    exact le_antisymm (h'.2 ⟨h𝔮p, hK𝔮⟩ (key 𝔮' h'.1.1 h'.1.2 h'P)) (key 𝔮' h'.1.1 h'.1.2 h'P)
  ·
    set 𝔪 : Ideal (A ⧸ 𝔮) := P.map (Ideal.Quotient.mk 𝔮) with h𝔪
    have hmem : ∀ a : A, Ideal.Quotient.mk 𝔮 a ∈ 𝔪 ↔ a ∈ P := fun a =>
      Ideal.mem_quotient_iff_mem h𝔮P
    have hPmax : P.IsMaximal := ptIdeal_isMaximal p
    have h𝔪max : 𝔪.IsMaximal := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective hPmax with h | h
      · exfalso
        have h1 : Ideal.Quotient.mk 𝔮 1 ∈ 𝔪 := by rw [h𝔪, h]; exact Submodule.mem_top
        exact hPmax.ne_top ((Ideal.eq_top_iff_one (I := P)).mpr ((hmem 1).mp h1))
      · exact h
    let f : A ⧸ 𝔮 →+* S ⧸ I := Ideal.quotientMap I (algebraMap A S) le_rfl
    letI : Algebra (A ⧸ 𝔮) (S ⧸ I) := f.toAlgebra
    have hf : ∀ a : A, algebraMap (A ⧸ 𝔮) (S ⧸ I) (Ideal.Quotient.mk 𝔮 a) =
        Ideal.Quotient.mk I (algebraMap A S a) := fun a => Ideal.quotientMap_mk
    have hloc : IsLocalization.AtPrime (S ⧸ I) 𝔪 := by
      show IsLocalization 𝔪.primeCompl (S ⧸ I)
      rw [isLocalization_iff]
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨y, hy⟩
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
        have ha : a ∈ P.primeCompl := fun h => hy ((hmem a).mpr h)
        rw [hf]
        exact (IsLocalization.map_units S (⟨a, ha⟩ : P.primeCompl)).map _
      · intro z
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
        have ht : Ideal.Quotient.mk 𝔮 (t : A) ∈ 𝔪.primeCompl := fun h => t.2 ((hmem _).mp h)
        refine ⟨⟨Ideal.Quotient.mk 𝔮 a, ⟨_, ht⟩⟩, ?_⟩
        simp only [hf, ← map_mul]
        rw [IsLocalization.mk'_spec]
      · intro x y hxy
        exact ⟨1, by rw [Ideal.quotientMap_injective hxy]⟩
    have hdim : ringKrullDim (S ⧸ I) = 𝔪.height :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (S ⧸ I)
    have hsum := ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 𝔪
    show ringKrullDim (S ⧸ I) + _ = _
    rw [hdim, ← WithBot.coe_add, add_comm, hsum]
    rfl

theorem ringKrullDim_locRing_eq_of_minimalPrime (K : Ideal (MvPolynomial (Fin n) ℂ))
    (p p' : Fin n → ℂ) [IsRegularLocalRing (locRing K p)] [IsRegularLocalRing (locRing K p')]
    (𝔮 : Ideal (MvPolynomial (Fin n) ℂ)) (h𝔮 : 𝔮 ∈ K.minimalPrimes)
    (hp : 𝔮 ≤ ptIdeal p) (hp' : 𝔮 ≤ ptIdeal p') :
    ringKrullDim (locRing K p) = ringKrullDim (locRing K p') := by
  obtain ⟨q1, -, -, hu1, hd1⟩ := regular_point_unique_minimalPrime K p
  obtain ⟨q2, -, -, hu2, hd2⟩ := regular_point_unique_minimalPrime K p'
  obtain rfl := hu1 𝔮 h𝔮 hp
  obtain rfl := hu2 𝔮 h𝔮 hp'
  rw [← hd2] at hd1
  exact withBot_add_right_cancel hd1 hd2

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory IsLocalRing

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem ne_zero_of_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hd : ringKrullDim R = d) (v : Fin d → R) (hv : Ideal.span (Set.range v) = maximalIdeal R)
    (l : Fin d) : v l ≠ 0 := by
  intro h0
  have hfin : (Set.range v \ {0}).Finite := (Set.finite_range v).sdiff
  have hncard : (Set.range v \ {0}).ncard < d := by
    have h1 : (Set.range v \ {0}).ncard < (Set.range v).ncard :=
      Set.ncard_sdiff_singleton_lt_of_mem ⟨l, h0⟩ (Set.finite_range v)
    have h2 : (Set.range v).ncard ≤ d := by
      calc (Set.range v).ncard ≤ (Set.univ : Set (Fin d)).ncard := by
            rw [← Set.image_univ]; exact Set.ncard_image_le (Set.finite_univ)
        _ = d := by simp
    omega
  have hspan : Ideal.span (Set.range v \ {0}) = maximalIdeal R := by
    rw [Ideal.span_sdiff_singleton_zero, hv]
  have hle : (maximalIdeal R).spanFinrank ≤ (Set.range v \ {0}).ncard := by
    rw [← hspan]; exact Submodule.spanFinrank_span_le_ncard_of_finite hfin
  have hdim := ringKrullDim_le_spanFinrank_maximalIdeal R
  rw [hd] at hdim
  have : (d : WithBot ℕ∞) ≤ ((Set.range v \ {0}).ncard : WithBot ℕ∞) :=
    hdim.trans (by exact_mod_cast hle)
  have := (Nat.cast_le (α := WithBot ℕ∞)).mp this
  omega

theorem WData.exists_closed_off (w : WData P D hP) (Q : AffPres (w.π ≫ toSpecC hP)) (x : w.M) (hxV : x.1 ∈ Q.V)
    (𝔮 : Ideal (MvPolynomial (Fin Q.n) ℂ)) (h𝔮min : 𝔮 ∈ Q.K.minimalPrimes)
    (h𝔮x : 𝔮 ≤ ptIdeal (Q.coord x.1 hxV)) (G : MvPolynomial (Fin Q.n) ℂ)
    (hG : eval (Q.coord x.1 hxV) G ≠ 0) :
    ∃ x' : w.M, ∃ hx' : x'.1 ∈ Q.V,
      𝔮 ≤ ptIdeal (Q.coord x'.1 hx') ∧
        w.π.base x'.1 ∉ (projB P D hP : Set (projX P hP)) ∧ eval (Q.coord x'.1 hx') G ≠ 0 := by
  generalize hp : Q.coord x.1 hxV = p at h𝔮x hG
  have := w.regular x.1
  haveI hregL : IsRegularLocalRing (locRing Q.K p) := by
    rw [← hp]; exact (Q.isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  haveI : IsDomain (locRing Q.K p) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  set d := (maximalIdeal (w.W.presheaf.stalk x.1)).spanFinrank with hdd
  have hd : ringKrullDim (w.W.presheaf.stalk x.1) = d :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal).symm
  obtain ⟨S, -, -⟩ := exists_sncData w.snc_Zb Q w.compEquiv d x.1 hxV x.2 hd
  rw [hp] at S
  have hdL : ringKrullDim (locRing Q.K p) = d := by
    rw [← hp, ← Q.ringKrullDim_stalk x.1 hxV x.2]; exact hd
  have hmax : Ideal.map (algebraMap _ (locRing Q.K p)) (ptIdeal p) = maximalIdeal (locRing Q.K p) := by
    subst hp
    rw [← Q.map_maximalIdeal_stalk x.1 hxV x.2]; exact map_ringEquiv_maximalIdeal _

  set 𝔮' := RingHom.ker (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locRing Q.K p)) with h𝔮'
  have h𝔮'prime : 𝔮'.IsPrime := RingHom.ker_isPrime _
  have hK𝔮' : Q.K ≤ 𝔮' := by
    intro f hf
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hf)
  have h𝔮'p : 𝔮' ≤ ptIdeal p := by
    intro f hf
    by_contra hfp
    rw [h𝔮', RingHom.mem_ker, IsScalarTower.algebraMap_apply (MvPolynomial (Fin Q.n) ℂ) (locPt p),
      Ideal.Quotient.algebraMap_eq] at hf
    have hu : IsUnit (algebraMap (MvPolynomial (Fin Q.n) ℂ) (locPt p) f) :=
      IsLocalization.map_units (locPt p) (⟨f, hfp⟩ : (ptIdeal p).primeCompl)
    have := (hu.map (Ideal.Quotient.mk (Ideal.map (algebraMap _ (locPt p)) Q.K))).ne_zero
    exact this hf
  have h𝔮𝔮' : 𝔮 ≤ 𝔮' := by
    obtain ⟨Q', hQ'min, hQ'le⟩ := Ideal.exists_minimalPrimes_le hK𝔮'
    obtain ⟨q0, -, -, hu, -⟩ := regular_point_unique_minimalPrime Q.K p
    rw [hu 𝔮 h𝔮min h𝔮x, ← hu Q' hQ'min (hQ'le.trans h𝔮'p)]
    exact hQ'le
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  set F := S.h * ∏ l ∈ S.J, S.r l with hF
  have hFbd : F ∈ Q.bdIdeal w.Zb := S.mem_bd
  have hFq : F ∉ 𝔮 := by
    intro hmem
    rcases h𝔮prime.mem_or_mem hmem with hh | hprod
    · exact S.eval_h (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hh)
    · haveI := h𝔮prime
      obtain ⟨l, -, hl⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
      have h0 : algebraMap _ (locRing Q.K p) (S.r l) = 0 := h𝔮𝔮' hl
      exact ne_zero_of_span_eq_maximalIdeal hdL (fun l => algebraMap _ (locRing Q.K p) (S.r l))
        (S.span_eq.trans hmax) l h0

  have hGq : G ∉ 𝔮 := fun hG𝔮 => hG (by simpa [ptIdeal, RingHom.mem_ker] using h𝔮x hG𝔮)
  have hFGq : F * G ∉ 𝔮 := fun hm => (h𝔮prime.mem_or_mem hm).elim hFq hGq
  obtain ⟨y, hy𝔮, hyFG⟩ : ∃ y : Fin Q.n → ℂ, (∀ f ∈ 𝔮, eval y f = 0) ∧ eval y (F * G) ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hFGq
    have : F * G ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
      rw [mem_vanishingIdeal_iff]
      intro y hy
      exact hno y (fun f hf => by simpa using hy f hf)
    rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮prime.radical] at this
  obtain ⟨x'', ⟨hx''V, hcl, hco⟩, -⟩ :=
    Q.existsUnique_closed_coord y (fun f hf => hy𝔮 f (h𝔮min.1.2 hf))
  have hyF : eval y F ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, zero_mul])
  have hyG : eval y G ≠ 0 := fun h0 => hyFG (by rw [eval_mul, h0, mul_zero])
  refine ⟨⟨x'', hcl⟩, hx''V, ?_, ?_, by rw [hco]; exact hyG⟩
  · intro f hf
    show f ∈ ptIdeal (Q.coord x'' hx''V)
    rw [hco, ptIdeal, RingHom.mem_ker]
    exact hy𝔮 f hf
  · intro hB
    have hsupp : x'' ∈ (w.Zb.support : Set w.W) := by
      rw [w.support_Zb]; exact hB
    have := (Q.zero_bdIdeal_iff w.Zb x'' hx''V hcl).mpr hsupp F hFbd
    rw [hco] at this
    exact hyF this

set_option backward.isDefEq.respectTransparency.types false in

theorem WData.ringKrullDim_stalk_off (w : WData P D hP) (e : ℕ)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e)
    (y : w.M) (hy : w.π.base y.1 ∉ (projB P D hP : Set (projX P hP))) :
    ringKrullDim (w.W.presheaf.stalk y.1) = e := by
  have := w.lft
  have := w.isIso_off
  have hU : y.1 ∈ w.π ⁻¹ᵁ projBCompl P D hP := hy
  have hiso : IsIso (w.π.stalkMap y.1) := by
    have h := (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap w.π (projBCompl P D hP) ⟨y.1, hU⟩)
    haveI hoi : IsOpenImmersion (w.π ∣_ projBCompl P D hP) := IsOpenImmersion.of_isIso _
    have h2 : IsIso ((w.π ∣_ projBCompl P D hP).stalkMap ⟨y.1, hU⟩) := inferInstance
    exact h.mp h2
  rw [← ringKrullDim_eq_of_ringEquiv (asIso (w.π.stalkMap y.1)).commRingCatIsoToRingEquiv]
  have hcl : IsClosed ({w.π.base y.1} : Set (projX P hP)) :=
    (val_comp (w.π ≫ toSpecC hP) (toSpecC hP) w.π rfl (U := ⊤) (V := ⊤) (by simp) 0 y.1 trivial
      y.2).1
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base y.1)
  obtain ⟨z, hz, -, ⟨ψ⟩⟩ := exists_closedPoint_stalk hP p _ hp hcl
  rw [ringKrullDim_eq_of_ringEquiv ψ]
  exact hdim p z hz

theorem WData.ringKrullDim_stalk (w : WData P D hP) (e : ℕ) (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (hdim : ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval z h = 0) →
      ringKrullDim (chartLocRing P p z) = e) :
    ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e := by

  have offB : ∀ y : w.M, w.π.base y.1 ∉ (projB P D hP : Set (projX P hP)) →
      ringKrullDim (w.W.presheaf.stalk y.1) = e :=
    w.ringKrullDim_stalk_off e hdim
  intro x
  obtain ⟨c, hc⟩ := w.cover x
  have hxV : x.1 ∈ (w.pres c.1 c.2).V := hc
  rw [(w.pres c.1 c.2).ringKrullDim_stalk x.1 hxV x.2]
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x.1 hxV x.2).mp (w.regular x.1)
  obtain ⟨𝔮, h𝔮min, h𝔮x, -, -⟩ :=
    regular_point_unique_minimalPrime (w.pres c.1 c.2).K ((w.pres c.1 c.2).coord x.1 hxV)

  obtain ⟨x', hx'V, h𝔮x', hx'B, -⟩ :=
    w.exists_closed_off (w.pres c.1 c.2) x hxV 𝔮 h𝔮min h𝔮x 1 (by simp)
  have := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x'.1 hx'V x'.2).mp (w.regular x'.1)
  rw [ringKrullDim_locRing_eq_of_minimalPrime (w.pres c.1 c.2).K _ _ 𝔮 h𝔮min h𝔮x h𝔮x',
    ← (w.pres c.1 c.2).ringKrullDim_stalk x'.1 hx'V x'.2]
  exact offB x' hx'B

theorem WData.dim_coord (w : WData P D hP) {e : ℕ}
    (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx) (x : w.M)
    (hx : x ∈ w.src c) : ringKrullDim (locRing (w.pres c.1 c.2).K (w.coord c x)) = e := by
  have h1 : w.coord c x = (w.pres c.1 c.2).coord x.1 hx := by
    unfold WData.coord
    exact dif_pos hx
  rw [h1, ← (w.pres c.1 c.2).ringKrullDim_stalk x.1 hx x.2]
  exact he x

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

namespace WData

variable (w : WData P D hP)

theorem jacobsonSpace_W : JacobsonSpace w.W := by
  have := w.lft
  exact LocallyOfFiniteType.jacobsonSpace (w.π ≫ toSpecC hP)

theorem exists_mem_pres_V (x : w.W) : ∃ c : w.Idx, x ∈ (w.pres c.1 c.2).V := by
  obtain ⟨p, hp⟩ := chartOpen_cover hP (w.π.base x)
  have hx : x ∈ w.π ⁻¹ᵁ (chartOpen hP p).1 := hp
  rw [← w.iSup_pres p] at hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨⟨p, i⟩, hi⟩

theorem exists_closed_off_of_isOpen (N : Set w.W) (hN : IsOpen N) (hne : N.Nonempty) :
    ∃ x' : w.M, x'.1 ∈ N ∧ w.π.base x'.1 ∉ (projB P D hP : Set (projX P hP)) := by
  haveI := w.jacobsonSpace_W
  obtain ⟨x0, hx0N, hx0c⟩ := nonempty_inter_closedPoints hne hN.isLocallyClosed
  obtain ⟨c, hc⟩ := w.exists_mem_pres_V x0
  haveI := ((w.pres c.1 c.2).isRegularLocalRing_stalk_iff x0 hc hx0c).mp (w.regular x0)
  obtain ⟨𝔮, h𝔮min, h𝔮x, -, -⟩ :=
    regular_point_unique_minimalPrime (w.pres c.1 c.2).K ((w.pres c.1 c.2).coord x0 hc)
  obtain ⟨T, hT⟩ := (w.pres c.1 c.2).exists_basicOpen_cover ⟨N, hN⟩
  obtain ⟨G, hGT, hx0G⟩ := (hT x0 hc).mp hx0N
  have hG0 : eval ((w.pres c.1 c.2).coord x0 hc) G ≠ 0 := by
    have := (w.mem_basicOpen_iff c ⟨x0, hx0c⟩ hc G).mp hx0G
    rwa [w.coord_of_mem c ⟨x0, hx0c⟩ hc] at this
  obtain ⟨x', hx'V, -, hx'B, hx'G⟩ :=
    w.exists_closed_off (w.pres c.1 c.2) ⟨x0, hx0c⟩ hc 𝔮 h𝔮min h𝔮x G hG0
  refine ⟨x', ?_, hx'B⟩
  have hmem : x'.1 ∈ w.W.basicOpen ((w.pres c.1 c.2).secHom G) := by
    rw [w.mem_basicOpen_iff c x' hx'V G, w.coord_of_mem c x' hx'V]; exact hx'G
  exact (hT x'.1 hx'V).mpr ⟨G, hGT, hmem⟩

theorem eval_bind_lift_ne_zero (hD : IsMultiHomogIdeal D) (f : MvPolynomial (Σ k, ι k) ℂ)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D)
    (c : w.Idx) (x : w.M) (hx : x ∈ w.src c)
    (hxB : w.π.base x.1 ∉ (projB P D hP : Set (projX P hP))) :
    eval (w.coord c x) (bind₁ (w.lift c) f) ≠ 0 := by
  have h1 : eval (w.coord c x) (bind₁ (w.lift c) f) =
      eval (fun q => eval (w.coord c x) (w.lift c q)) f := by
    show aeval (w.coord c x) (bind₁ (w.lift c) f) = aeval (fun q => aeval (w.coord c x) (w.lift c q)) f
    exact aeval_bind₁ _ _ _
  rw [h1]
  intro h0
  exact hxB ((w.mem_projB_iff_lift hD c x hx).mpr (hzero _ (w.lift_mem c x hx) h0))

theorem germ_lift_ne_zero (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D)
    (c : w.Idx) (x : w.W) (hx : x ∈ (w.pres c.1 c.2).V) :
    w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) ≠ 0 := by
  intro h0
  have h0' : w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) =
      w.W.presheaf.germ _ x hx 0 := by rw [h0, map_zero]
  obtain ⟨O, hxO, iO, iO', hO⟩ := TopCat.Presheaf.germ_eq w.W.presheaf x hx hx _ _ h0'
  obtain ⟨x', hx'O, hx'B⟩ := w.exists_closed_off_of_isOpen O O.isOpen ⟨x, hxO⟩
  have hx'V : x'.1 ∈ (w.pres c.1 c.2).V := iO.le hx'O
  have hnot : x'.1 ∉ w.W.basicOpen ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) := by
    intro hm
    have hres : x'.1 ∈ w.W.basicOpen
        (w.W.presheaf.map iO.op ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))) := by
      rw [Scheme.basicOpen_res]; exact ⟨hx'O, hm⟩
    rw [hO, map_zero, Scheme.basicOpen_zero] at hres
    exact hres
  apply w.eval_bind_lift_ne_zero hD f hzero c x' hx'V hx'B
  by_contra hne
  exact hnot ((w.mem_basicOpen_iff c x' hx'V _).mpr hne)

theorem germ_lift_isUnit (hD : IsMultiHomogIdeal D)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D)
    (c : w.Idx) (x : w.W) (hx : x ∈ (w.pres c.1 c.2).V)
    (hxB : w.π.base x ∉ (projB P D hP : Set (projX P hP))) :
    IsUnit (w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))) := by
  haveI := w.jacobsonSpace_W
  refine (w.W.mem_basicOpen _ x hx).mp ?_
  by_contra hxs
  let U : w.W.Opens := (w.pres c.1 c.2).V ⊓ w.π ⁻¹ᵁ projBCompl P D hP
  have hZ : (closure {x} ∩ (U : Set w.W)).Nonempty := ⟨x, subset_closure rfl, hx, hxB⟩
  have hZlc : IsLocallyClosed (closure {x} ∩ (U : Set w.W)) :=
    isClosed_closure.isLocallyClosed.inter U.isOpen.isLocallyClosed
  obtain ⟨y, ⟨hyx, hyV, hyB⟩, hyc⟩ := nonempty_inter_closedPoints hZ hZlc
  have hys : y ∉ w.W.basicOpen ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) := by
    intro hm
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hyx _ (w.W.basicOpen _).isOpen hm
    rw [Set.mem_singleton_iff.mp hz] at hzU
    exact hxs hzU
  apply w.eval_bind_lift_ne_zero hD f hzero c ⟨y, hyc⟩ hyV hyB
  by_contra hne
  exact hys ((w.mem_basicOpen_iff c ⟨y, hyc⟩ hyV _).mpr hne)

end WData

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem appLE_constSec_eq {S T : Scheme.{0}} (t : T ⟶ Spec (.of ℂ)) (g : S ⟶ T) {U : T.Opens}
    {V : S.Opens} (h : V ≤ g ⁻¹ᵁ U) (c : ℂ) :
    g.appLE U V h (constSec t U c) = constSec (g ≫ t) V c := by
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE g t ⊤ U V le_top h)

theorem constSec_map_res {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) {U V : S.Opens} (h : V ≤ U) (c : ℂ) :
    S.presheaf.map (homOfLE h).op (constSec s U c) = constSec s V c := by
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_map s (le_top : U ≤ s ⁻¹ᵁ ⊤) (homOfLE h).op)

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem map_eval₂_constSec {S : Scheme.{0}} (s : S ⟶ Spec (.of ℂ)) {U V : S.Opens} (h : V ≤ U)
    {σ : Type} (u : σ → Γ(S, U)) (f : MvPolynomial σ ℂ) :
    S.presheaf.map (homOfLE h).op (eval₂ (constSec s U) u f) =
      eval₂ (constSec s V) (fun q => S.presheaf.map (homOfLE h).op (u q)) f := by
  have e := MvPolynomial.eval₂_comp_left (S.presheaf.map (homOfLE h).op).hom (constSec s U) u f
  refine e.trans ?_
  congr 1
  exact RingHom.ext fun c => constSec_map_res s h c

theorem chart_eval₂_overlap (p p' : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ)
    (hf : IsMultiHomog f a) :
    ∃ u : Γ(projX P hP, (chartOpen hP p).1 ⊓ (chartOpen hP p').1), IsUnit u ∧
      (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP p').1) (chartCoord hP p') f) =
        u * (projX P hP).presheaf.map
          (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) f) := by
  have hinv : ∀ k,
      (projX P hP).presheaf.map (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p' ⟨k, p k⟩) *
        (projX P hP).presheaf.map (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p ⟨k, p' k⟩) = 1 := by
    intro k
    have h := chartCoord_overlap hP p p' ⟨k, p' k⟩
    dsimp only at h
    rw [mul_comm, h, chartCoord_self, map_one]
  refine ⟨∏ k, ((projX P hP).presheaf.map
      (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
        (chartCoord hP p' ⟨k, p k⟩)) ^ a k, ?_, ?_⟩
  · have h1 : (∏ k, ((projX P hP).presheaf.map
        (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p' ⟨k, p k⟩)) ^ a k) * (∏ k, ((projX P hP).presheaf.map
        (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
          (chartCoord hP p ⟨k, p' k⟩)) ^ a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← mul_pow, hinv k, one_pow]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  · rw [map_eval₂_constSec, map_eval₂_constSec]
    have hco : (fun q => (projX P hP).presheaf.map
        (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op (chartCoord hP p' q)) =
        fun q => (projX P hP).presheaf.map
          (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
            (chartCoord hP p' ⟨q.1, p q.1⟩) *
          (projX P hP).presheaf.map
            (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
              (chartCoord hP p q) := by
      funext q
      rw [← chartCoord_overlap hP p p' q, mul_comm]
    have key := eval₂_smul_of_isMultiHomog' (R := Γ(projX P hP, (chartOpen hP p).1 ⊓ (chartOpen hP p').1))
      (constSec (toSpecC hP) ((chartOpen hP p).1 ⊓ (chartOpen hP p').1)) hf
      (fun k => (projX P hP).presheaf.map
          (homOfLE (inf_le_right : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
            (chartCoord hP p' ⟨k, p k⟩))
      (fun q => (projX P hP).presheaf.map
            (homOfLE (inf_le_left : (chartOpen hP p).1 ⊓ (chartOpen hP p').1 ≤ _)).op
              (chartCoord hP p q))
    rw [hco]
    exact key

namespace WData

variable (w : WData P D hP)

theorem secHom_bind_lift (c : w.Idx) (f : MvPolynomial (Σ k, ι k) ℂ) :
    (w.pres c.1 c.2).secHom (bind₁ (w.lift c) f) =
      w.π.appLE _ (w.pres c.1 c.2).V (w.le_pres c.1 c.2)
        (eval₂ (constSec (toSpecC hP) (chartOpen hP c.1).1) (chartCoord hP c.1) f) := by
  have h : ((w.pres c.1 c.2).secHom).comp (bind₁ (w.lift c)).toRingHom =
      (w.π.appLE _ (w.pres c.1 c.2).V (w.le_pres c.1 c.2)).hom.comp
        (eval₂Hom (constSec (toSpecC hP) (chartOpen hP c.1).1) (chartCoord hP c.1)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, bind₁_C_right,
        coe_eval₂Hom, eval₂_C]
      rw [AffPres.secHom_C, appLE_constSec_eq]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, bind₁_X_right,
        coe_eval₂Hom, eval₂_X]
      by_cases hq : q.2 = c.1 q.1
      · have e : w.lift c q = 1 := by simp [lift, hq]
        rw [e, map_one]
        obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        rw [chartCoord_self, map_one]
      · have e : w.lift c q = X (w.yq c.1 c.2 q) := by simp [lift, hq]
        rw [e, w.sec_yq]
  exact RingHom.congr_fun h f

theorem germ_lift_ratio (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (c c' : w.Idx) (x : w.W) (hx : x ∈ (w.pres c.1 c.2).V) (hx' : x ∈ (w.pres c'.1 c'.2).V) :
    ∃ u : (w.W.presheaf.stalk x)ˣ,
      w.W.presheaf.germ _ x hx ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f)) =
        u * w.W.presheaf.germ _ x hx' ((w.pres c'.1 c'.2).secHom (bind₁ (w.lift c') f)) := by
  obtain ⟨u, hu, he⟩ := chart_eval₂_overlap (hP := hP) c.1 c'.1 f a hf
  have hVO : (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V ≤
      w.π ⁻¹ᵁ ((chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1) := fun y hy =>
    ⟨w.le_pres c.1 c.2 hy.1, w.le_pres c'.1 c'.2 hy.2⟩
  have hxx : x ∈ (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V := ⟨hx, hx'⟩
  have hU : IsUnit (w.W.presheaf.germ _ x hxx (w.π.appLE _ _ hVO u)) :=
    (hu.map (w.π.appLE _ _ hVO).hom).map _
  refine ⟨hU.unit⁻¹, ?_⟩
  have e1 : ∀ (d : w.Idx) (hd : (w.pres c.1 c.2).V ⊓ (w.pres c'.1 c'.2).V ≤ (w.pres d.1 d.2).V)
      (hO : (chartOpen hP c.1).1 ⊓ (chartOpen hP c'.1).1 ≤ (chartOpen hP d.1).1)
      (hxd : x ∈ (w.pres d.1 d.2).V),
      w.W.presheaf.germ _ x hxd ((w.pres d.1 d.2).secHom (bind₁ (w.lift d) f)) =
        w.W.presheaf.germ _ x hxx (w.π.appLE _ _ hVO ((projX P hP).presheaf.map (homOfLE hO).op
          (eval₂ (constSec (toSpecC hP) (chartOpen hP d.1).1) (chartCoord hP d.1) f))) := by
    intro d hd hO hxd
    rw [w.secHom_bind_lift d f, ← TopCat.Presheaf.germ_res_apply w.W.presheaf (homOfLE hd) x hxx]
    congr 1
    show (w.π.appLE _ _ _ ≫ w.W.presheaf.map (homOfLE hd).op).hom _ =
      ((projX P hP).presheaf.map (homOfLE hO).op ≫ w.π.appLE _ _ hVO).hom _
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  rw [e1 c inf_le_left inf_le_left hx, e1 c' inf_le_right inf_le_right hx', he, map_mul, map_mul,
    ← mul_assoc]
  rw [hU.val_inv_mul, one_mul]

end WData

end

end ReciprocityTheory.AnForm.R
end

section
namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}

theorem projBCompl_mem {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {hP : IsMultiHomogIdeal P}
    (y : projX P hP) : y ∈ projBCompl P D hP ↔ y ∉ (projB P D hP : Set (projX P hP)) := Iff.rfl

namespace WData

variable (w : WData P D hP)

theorem zero_bd (hD : IsMultiHomogIdeal D) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    (∀ h ∈ w.bd c, eval (w.coord c x) h = 0) ↔
      (fun q => eval (w.coord c x) (w.lift c q)) ∈ conePts D := by
  rw [← w.mem_projB_iff_lift hD c x hx, w.coord_of_mem c x hx]
  have h1 := (w.pres c.1 c.2).zero_bdIdeal_iff w.Zb x.1 hx x.2
  rw [w.support_Zb] at h1
  exact h1

theorem surj (hD : IsMultiHomogIdeal D) (z : (Σ k, ι k) → ℂ) (hz : z ∈ conePts P)
    (hzD : z ∉ conePts D) :
    ∃ c, ∃ x ∈ w.src c, SameOrbit (fun q => eval (w.coord c x) (w.lift c q)) z := by
  exact w.surj' hD z hz hzD

theorem inj (hD : IsMultiHomogIdeal D) (c c' : w.Idx) (x : w.M) (hx : x ∈ w.src c) (x' : w.M)
    (hx' : x' ∈ w.src c') (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D)
    (ho : SameOrbit (fun q => eval (w.coord c x) (w.lift c q))
      (fun q => eval (w.coord c' x') (w.lift c' q))) : x = x' := by
  exact w.inj' hD c c' x hx x' hx' hxD ho

theorem inv (hD : IsMultiHomogIdeal D) (c : w.Idx) (x : w.M) (hx : x ∈ w.src c)
    (hxD : (fun q => eval (w.coord c x) (w.lift c q)) ∉ conePts D) (p : (k : K) → ι k)
    (hp : ∀ k, eval (w.coord c x) (w.lift c ⟨k, p k⟩) ≠ 0) :
    ∃ O : Set w.M, IsOpen O ∧ x ∈ O ∧ O ⊆ w.src c ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
      (F : Fin (w.pres c.1 c.2).n → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
        (∀ k, eval (w.coord c y) (w.lift c ⟨k, p k⟩) ≠ 0) ∧
        eval (affCoord p fun q => eval (w.coord c y) (w.lift c q)) q ≠ 0 ∧
        ∀ l, w.coord c y l * eval (affCoord p fun q => eval (w.coord c y) (w.lift c q)) q =
          eval (affCoord p fun q => eval (w.coord c y) (w.lift c q)) (F l) := by
  have hx' : x.1 ∈ (w.pres c.1 c.2).V := hx
  have hxp : w.π.base x.1 ∈ (chartOpen hP p).1 := (w.mem_chartOpen_iff c x hx p).2 hp
  have hxU : w.π.base x.1 ∈ projBCompl P D hP :=
    (projBCompl_mem _).2 fun h => hxD ((w.mem_projB_iff_lift hD c x hx).1 h)
  haveI := w.isIso_off
  have hu : ∀ t : Γ(projX P hP, (chartOpen hP p).1), ∃ F : MvPolynomial (Σ k, ι k) ℂ,
      t = eval₂ (constSec (toSpecC hP) (chartOpen hP p).1) (chartCoord hP p) F := by
    intro t
    obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective (gammaChart hP p t)
    exact ⟨F, by rw [← gammaChart_symm_mk, hF, RingEquiv.symm_apply_apply]⟩
  obtain ⟨O, hxO, hOle, q, F, -, hOF⟩ := exists_coord_inv (sW := w.π ≫ toSpecC hP) (sX := toSpecC hP) w.π rfl (projBCompl P D hP)
    (w.pres c.1 c.2) (chartOpen hP p).1 (chartOpen hP p).2 (chartCoord hP p) hu x.1 hx' hxp hxU x.2
  have hmem : ∀ y : w.M, y.1 ∈ O → y.1 ∈ (w.pres c.1 c.2).V ∧ w.π.base y.1 ∈ (chartOpen hP p).1 := by
    intro y hy
    have h := TopologicalSpace.Opens.mem_inf.1 (hOle hy)
    exact ⟨h.1, (TopologicalSpace.Opens.mem_inf.1 h.2).2⟩
  refine ⟨{y | y.1 ∈ O}, w.isOpen_zariski O, hxO, fun y hy => (hmem y hy).1, q, F, fun y hy => ?_⟩
  have hyV : y.1 ∈ (w.pres c.1 c.2).V := (hmem y hy).1
  have hyp : w.π.base y.1 ∈ (chartOpen hP p).1 := (hmem y hy).2
  have hval : (fun t => val (toSpecC hP) (chartCoord hP p t) (w.π.base y.1) hyp) =
      affCoord p (fun q => eval (w.coord c y) (w.lift c q)) :=
    funext fun t => w.val_chartCoord c y hyV p hyp t
  obtain ⟨h1, h2⟩ := hOF y.1 hyV hyp hy y.2
  have hc : w.coord c y = (w.pres c.1 c.2).coord y.1 hyV := w.coord_of_mem c y hyV
  refine ⟨(w.mem_chartOpen_iff c y hyV p).1 hyp, ?_, fun l => ?_⟩
  · rw [← hval]; exact h1
  · rw [← hval, hc]; exact h2 l

theorem exists_sncData_w {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    ∃ S : SncData (w.pres c.1 c.2).K (w.bd c) (w.coord c x) e w.rc,
      (∀ l ∈ S.J, ∃ k, S.σ l = some k ∧ ∃ hx' : x.1 ∈ (w.pres c.1 c.2).V,
        IsBranch (w.Zb.support : Set w.W) ((w.pres c.1 c.2).secHom (S.r l)) x.1
          (w.compEquiv k)) ∧
      ∃ O : Set w.M, IsOpen O ∧ x ∈ O ∧ O ⊆ w.src c ∧ ∀ k,
        w.comp k ∩ O = {y ∈ O | ∃ l, S.σ l = some k ∧ eval (w.coord c y) (S.r l) = 0} := by
  have hx' : x.1 ∈ (w.pres c.1 c.2).V := hx
  obtain ⟨S, hS, O, hxO, hOV, hO⟩ :=
    exists_sncData w.snc_Zb (w.pres c.1 c.2) w.compEquiv e x.1 hx' x.2 (he x)
  rw [w.coord_of_mem c x hx]
  refine ⟨S, fun l hl => ?_, {y | y.1 ∈ O}, w.isOpen_zariski O, hxO, fun y hy => hOV hy,
    fun k => ?_⟩
  · obtain ⟨k, hk, hb⟩ := hS l hl
    exact ⟨k, hk, hx', hb⟩
  · ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hyk, hyO⟩
      have hyV : y.1 ∈ (w.pres c.1 c.2).V := hOV hyO
      refine ⟨hyO, ?_⟩
      rw [w.coord_of_mem c y hyV]
      exact (hO k y.1 hyV hyO y.2).1 hyk
    · rintro ⟨hyO, hl⟩
      have hyV : y.1 ∈ (w.pres c.1 c.2).V := hOV hyO
      rw [w.coord_of_mem c y hyV] at hl
      exact ⟨(hO k y.1 hyV hyO y.2).2 hl, hyO⟩

def sncAt {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx)
    (x : w.M) (hx : x ∈ w.src c) : SncData (w.pres c.1 c.2).K (w.bd c) (w.coord c x) e w.rc :=
  Classical.choose (w.exists_sncData_w he c x hx)

theorem sncAt_branch {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (c : w.Idx) (x : w.M) (hx : x ∈ w.src c) :
    ∀ l ∈ (w.sncAt he c x hx).J, ∃ k, (w.sncAt he c x hx).σ l = some k ∧
      ∃ hx' : x.1 ∈ (w.pres c.1 c.2).V,
        IsBranch (w.Zb.support : Set w.W) ((w.pres c.1 c.2).secHom ((w.sncAt he c x hx).r l)) x.1
          (w.compEquiv k) :=
  (Classical.choose_spec (w.exists_sncData_w he c x hx)).1

theorem comp_eq {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e) (c : w.Idx)
    (x : w.M) (hx : x ∈ w.src c) :
    ∃ O : Set w.M, IsOpen O ∧ x ∈ O ∧ O ⊆ w.src c ∧ ∀ k,
      w.comp k ∩ O = {y ∈ O | ∃ l, (w.sncAt he c x hx).σ l = some k ∧
        eval (w.coord c y) ((w.sncAt he c x hx).r l) = 0} :=
  (Classical.choose_spec (w.exists_sncData_w he c x hx)).2

theorem exists_divIdeal (hD : IsMultiHomogIdeal D)
    (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) :
    ∃ G : w.W.IdealSheafData, FinalTheorems.EffCartier G ∧ (G.support : Set w.W) ⊆ w.Zb.support ∧
      ∀ (c : w.Idx) (x : w.M) (hx : x.1 ∈ (w.pres c.1 c.2).V),
        FinalTheorems.stalkId G x.1 = Ideal.span {w.W.presheaf.germ (w.pres c.1 c.2).V x.1 hx
          ((w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))} := by
  obtain ⟨G, hG⟩ := exists_idealSheaf_of_locGen (fun c : w.Idx => (w.pres c.1 c.2).V)
    w.exists_mem_pres_V (fun c => (w.pres c.1 c.2).secHom (bind₁ (w.lift c) f))
    (fun c c' x hx hx' => w.germ_lift_ratio f a hf c c' x hx hx')
  refine ⟨G, effCartier_of_stalkId G (fun x => ?_), fun x hxG => ?_, fun c x hx => hG c x.1 hx⟩
  · obtain ⟨c, hc⟩ := w.exists_mem_pres_V x
    haveI := w.regular x
    haveI : IsDomain (w.W.presheaf.stalk x) := isDomain_of_isRegularLocalRing
    exact ⟨_, mem_nonZeroDivisors_of_ne_zero (w.germ_lift_ne_zero hD hcomp f a hf hzero c x hc),
      hG c x hc⟩
  · by_contra hxZ
    rw [w.support_Zb] at hxZ
    obtain ⟨c, hc⟩ := w.exists_mem_pres_V x
    have hu := w.germ_lift_isUnit hD f a hf hzero c x hc hxZ
    rw [mem_support_iff_stalkId, hG c x hc, Ideal.span_singleton_eq_top.2 hu] at hxG
    exact hxG rfl

theorem mult {e : ℕ} (he : ∀ x : w.M, ringKrullDim (w.W.presheaf.stalk x.1) = e)
    (hD : IsMultiHomogIdeal D) (hcomp : ∀ Q ∈ P.minimalPrimes, IsRelevant Q → ¬ D ≤ Q)
    (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (hf : IsMultiHomog f a) (hfP : f ∉ P)
    (hzero : ∀ z ∈ conePts P, eval z f = 0 → z ∈ conePts D) :
    ∃ m : Fin w.rc → ℕ, ∀ c (x : w.M) (hx : x ∈ w.src c),
      ∃ u : locRing (w.pres c.1 c.2).K (w.coord c x), IsUnit u ∧
        algebraMap _ (locRing (w.pres c.1 c.2).K (w.coord c x)) (bind₁ (w.lift c) f) =
          u * ∏ l ∈ (w.sncAt he c x hx).J,
            algebraMap _ (locRing (w.pres c.1 c.2).K (w.coord c x)) ((w.sncAt he c x hx).r l) ^
              ((w.sncAt he c x hx).σ l).elim 0 m := by
  obtain ⟨G, hG, hGZ, hGx⟩ := w.exists_divIdeal hD hcomp f a hf hzero
  refine ⟨fun k => ordAlong G (w.compEquiv k), fun c x hx => ?_⟩
  have hx' : x.1 ∈ (w.pres c.1 c.2).V := hx
  haveI := w.regular x.1
  exact monomial_chart hG hGZ (w.pres c.1 c.2) w.compEquiv e x.1 hx' x.2 (he x)
    (w.coord_of_mem c x hx).symm (w.sncAt he c x hx)
    (fun l hl => by
      obtain ⟨k, hk, _, hb⟩ := w.sncAt_branch he c x hx l hl
      exact ⟨k, hk, hb⟩) _ (hGx c x hx')

end WData

end

end ReciprocityTheory.AnForm.R
end
