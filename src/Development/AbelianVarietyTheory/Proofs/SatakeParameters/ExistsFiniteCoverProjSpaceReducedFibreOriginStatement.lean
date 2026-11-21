import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSmoothFiniteCoverOfFormsNoCommonZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsTransversalAtComplexPointsStatement

section
namespace GlobalTheory

open scoped BigOperators

theorem quotient_maximal_le_sq {A : Type} [CommRing A] (I : Ideal A)
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2)
    (M : Ideal (A ⧸ I)) (hM : M.IsMaximal) : M ≤ M ^ 2 := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set m := M.comap (Ideal.Quotient.mk I) with hm
  have hmax : m.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hsurj
  have hIm : I ≤ m := by
    intro x hx
    simp [hm, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have key := Ideal.map_mono (f := Ideal.Quotient.mk I) (h m hmax hIm)
  rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_quotient_self, bot_sup_eq,
    hm, Ideal.map_comap_of_surjective _ hsurj] at key
  exact key

theorem pow_eq_self_of_le_sq {R : Type} [CommRing R] (M : Ideal R) (h : M ≤ M ^ 2) :
    ∀ k : ℕ, M ^ (k + 1) = M := by
  have h2 : M * M = M := by
    rw [← sq]; exact le_antisymm (Ideal.pow_le_self two_ne_zero) h
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, h2]

theorem isReduced_quotient_of_artinian_of_maximal_le (A : Type) [CommRing A] (I : Ideal A)
    (hart : IsArtinianRing (A ⧸ I))
    (h : ∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) : IsReduced (A ⧸ I) := by
  classical
  set R := A ⧸ I
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  set J : Ideal R := ∏ M : MaximalSpectrum R, M.asIdeal with hJ
  have hJinf : J = ⨅ M ∈ (Finset.univ : Finset (MaximalSpectrum R)), M.asIdeal := by
    rw [hJ]
    apply Ideal.prod_eq_iInf_of_pairwise_isCoprime
    intro a _ b _ hab
    exact Ideal.isCoprime_of_isMaximal (fun e => hab (MaximalSpectrum.ext e))
  have hpow : ∀ k : ℕ, J ^ (k + 1) = J := by
    intro k
    rw [hJ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun M _ => ?_)
    exact pow_eq_self_of_le_sq _ (quotient_maximal_le_sq I h M.asIdeal M.isMaximal) k
  have hJjac : J ≤ Ideal.jacobson ⊥ := by
    rw [hJinf]
    intro x hx
    rw [Ideal.mem_jacobson_bot]
    intro y
    by_contra hu
    obtain ⟨M, hMmax, hM⟩ := Ideal.exists_le_maximal (Ideal.span {x * y + 1})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have hxM : x ∈ M := by
      have := (Submodule.mem_iInf _).mp hx ⟨M, hMmax⟩
      simpa using this
    have h1 : x * y + 1 ∈ M := hM (Ideal.subset_span rfl)
    have : (1 : R) ∈ M := by
      have := M.sub_mem h1 (M.mul_mem_right y hxM)
      simpa using this
    exact hMmax.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hJbot : J = ⊥ := by
    rw [← hpow n]
    refine le_bot_iff.mp ?_
    calc J ^ (n + 1) ≤ (Ideal.jacobson ⊥) ^ (n + 1) := Ideal.pow_right_mono hJjac _
      _ ≤ (Ideal.jacobson ⊥) ^ n := Ideal.pow_le_pow_right (Nat.le_succ n)
      _ = ⊥ := hn
  refine ⟨fun x hx => ?_⟩
  have hxJ : x ∈ J := by
    rw [hJinf]
    refine (Submodule.mem_iInf _).mpr (fun M => (Submodule.mem_iInf _).mpr (fun _ => ?_))
    exact (hx.map (Ideal.Quotient.mk M.asIdeal)).eq_zero |> Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hJbot] at hxJ
  exact (Submodule.mem_bot R).mp hxJ

end GlobalTheory
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' : ∀ (A : Type) [CommRing A] (I : Ideal A), IsArtinianRing (A ⧸ I) →
    (∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) → IsReduced (A ⧸ I) := by
  first | (exact @GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (exact GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (intros; apply GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le  <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

theorem exists_cxPts_ker_eq : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  intro X p _ U hU m hm
  have h1 := LocallyOfFiniteType.finiteType_of_affine_subset p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : m.IsMaximal := hm
  letI : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, U) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, U) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, U) →+* ℂ := (e.symm : (Γ(X, U) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p U a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, U) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  refine ⟨CxPts.ofHom hU φ hφ, CxPts.ofHom_mem hU φ hφ, ?_⟩
  have hev : CxPts.evHom (CxPts.ofHom_mem hU φ hφ) = φ := by
    ext f
    rw [← CxPts.ev_eq, CxPts.ev_ofHom]
  rw [hev]
  ext f
  rw [RingHom.mem_ker]
  show f ∈ m ↔ e.symm (Ideal.Quotient.mk m f) = 0
  rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPt
end
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  first | (exact @GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (exact GlobalTheory.MaxPt.exists_cxPts_ker_eq) | (intros; apply GlobalTheory.MaxPt.exists_cxPts_ker_eq  <;> assumption)
end

section
open GlobalTheory.PD

namespace GlobalTheory

theorem finite_quotient_of_integral {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra.FiniteType k S] (f : R →ₐ[k] S) (hi : (f : R →+* S).IsIntegral) (I : Ideal S)
    (hc : ∀ r, ∃ c : k, f r - algebraMap k S c ∈ I) : Module.Finite k (S ⧸ I) := by
  classical
  letI : Algebra R S := (f : R →+* S).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  haveI : Algebra.IsIntegral R S := ⟨hi⟩
  haveI : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨⟨G.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hs : s ∈ Submodule.span R (G : Set S) := hG ▸ Submodule.mem_top
  induction hs using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    obtain ⟨c, hc⟩ := hc r
    have e : Ideal.Quotient.mk I (r • a) = c • Ideal.Quotient.mk I a := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]
      congr 1
      exact Ideal.Quotient.eq.2 hc
    rw [e]
    exact Submodule.smul_mem _ _ ha

end GlobalTheory

namespace GlobalTheory.PD

theorem isArtinianRing_fib_quot : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  intro k K _ _ _ F _ _ _ _ d x h
  haveI := h.smooth 0
  set I := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) with hI
  let f : rA k x {0} →ₐ[k] rB k K x {0} :=
    ((IsScalarTower.toAlgHom k F K).comp (rA k x {0}).val).codRestrict (rB k K x {0})
      (fun a => (integralClosure (rA k x {0}) K).algebraMap_mem a)
  have hi : (f : rA k x {0} →+* rB k K x {0}).IsIntegral := by
    intro s
    obtain ⟨p, hm, hp⟩ := s.2
    refine ⟨p, hm, Subtype.val_injective ?_⟩
    have e := Polynomial.hom_eval₂ p (f : rA k x {0} →+* rB k K x {0}) (rB k K x {0}).val.toRingHom s
    refine e.trans ?_
    exact hp
  have hc : ∀ r, ∃ c : k, f r - algebraMap k _ c ∈ I := by
    rintro ⟨r, hr⟩
    induction hr using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi0, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi0
      subst hi0
      cases j using Fin.cases with
      | zero =>
        refine ⟨1, ?_⟩
        convert I.zero_mem using 1
        rw [map_one, sub_eq_zero]
        refine Subtype.ext ?_
        show algebraMap F K (x 0 / x 0) = 1
        rw [div_self (h.pd.ne 0), map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, sub_zero]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap r =>
      refine ⟨r, ?_⟩
      have : f ⟨algebraMap k F r, _⟩ = algebraMap k _ r := f.commutes r
      rw [this, sub_self]
      exact I.zero_mem
    | add a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ + c₂, ?_⟩
      have : f ⟨a + b, add_mem ha hb⟩ = f ⟨a, ha⟩ + f ⟨b, hb⟩ := map_add f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_add]
      convert add_mem h₁ h₂ using 1
      ring
    | mul a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ * c₂, ?_⟩
      have : f ⟨a * b, mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := map_mul f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_mul]
      convert add_mem (I.mul_mem_right (f ⟨b, hb⟩) h₁) (I.mul_mem_left (algebraMap k _ c₁) h₂) using 1
      ring
  haveI := GlobalTheory.finite_quotient_of_integral f hi I hc
  exact IsArtinianRing.of_finite k _

end GlobalTheory.PD
end

section
open GlobalTheory.PD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  first | (exact @GlobalTheory.PD.isArtinianRing_fib_quot) | (exact GlobalTheory.PD.isArtinianRing_fib_quot) | (intros; apply GlobalTheory.PD.isArtinianRing_fib_quot  <;> assumption)
end

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.PD.FibRed

theorem quotEquiv_of_germ {X : Scheme.{0}} [IsIntegral X] [Algebra ℂ X.functionField] {F : Type} [Field F] [Algebra ℂ F]
    [Algebra F X.functionField] [IsScalarTower ℂ F X.functionField] {d : ℕ} (x : Fin (d + 1) → F) (U : X.Opens)
    (hg : genericPoint X ∈ U) (t : Fin d → Γ(X, U))
    (hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔ ∃ f : Γ(X, U), (X.presheaf.germ U (genericPoint X) hg).hom f = y)
    (ht : ∀ j, (X.presheaf.germ U (genericPoint X) hg).hom (t j) = algebraMap F X.functionField (x j.succ / x 0)) :
    Nonempty ((Γ(X, U) ⧸ Ideal.span (Set.range t)) ≃+*
      (rB ℂ X.functionField x {0} ⧸ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) := by
  set g := (X.presheaf.germ U (genericPoint X) hg).hom
  have hinj : Function.Injective g := germ_injective_of_isIntegral X _ hg
  let g' : Γ(X, U) →+* rB ℂ X.functionField x {0} :=
    g.codRestrict (rB ℂ X.functionField x {0}).toSubring fun f => (hring _).2 ⟨f, rfl⟩
  have hbij : Function.Bijective g' := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (hring y).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  let e := RingEquiv.ofBijective g' hbij
  refine ⟨Ideal.quotientEquiv _ _ e ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact Subtype.ext (ht j).symm

theorem exists_finCover_fibre_reduced : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → IsProjOver p → ∀ S : Finset (CxPts p (RingHom.id ℂ)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F) (U : Fin (d + 1) → X.Opens), IsFinCover ℂ X.functionField x ∧ IsAffCover p U (rB ℂ X.functionField x) ∧ IsReduced ((rB ℂ X.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) ∧ ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (U 0) ∧ ∀ j : Fin d, ∀ (hg : genericPoint X ∈ U 0) (f : Sec p (U 0)), (X.presheaf.germ (U 0) (genericPoint X) hg).hom f = algebraMap F X.functionField (x j.succ / x 0) → CxPts.ev p (RingHom.id ℂ) (U 0) f y = 0 := by
  intro X _ p d _ inst hinst hproj S
  obtain ⟨N, ι, hι, hιp⟩ := hproj
  obtain ⟨n, f, hf, hn, hcov, hgen, hS, htr⟩ := GlobalTheory.T.exists_forms_transversal_at_complexPoints X p d N ι hι hιp S
  obtain ⟨F, x, hFC, hAC, hx⟩ := GlobalTheory.T.exists_finiteCover_affineCover_of_forms_no_commonZero X p d hinst N ι hι hιp n f hf hn hcov hgen
  set U0 := GlobalTheory.EtProj.fOpen ι (f 0) with hU0
  set t : Fin d → Γ(X, U0) := fun j => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0) with ht_def
  have hx0 : x 0 = 1 := by
    apply (algebraMap F X.functionField).injective
    rw [hx 0, GlobalTheory.EtProj.fRatio_self, map_one, map_one]
  have ht : ∀ j, (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom (t j) =
      algebraMap F X.functionField (x j.succ / x 0) := by
    intro j
    rw [hx0, div_one, hx j.succ]
  have hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔
      ∃ g : Γ(X, U0), (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom g = y := by
    intro y
    have hle : ({0} : Finset (Fin (d + 1))).inf (fun i => GlobalTheory.EtProj.fOpen ι (f i)) = U0 := by simp [hU0]
    rw [hAC.ring {0} (Finset.singleton_nonempty 0) y]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.ge).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.ge) _ _ g
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.le).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.le) _ _ g
  obtain ⟨E⟩ := quotEquiv_of_germ x U0 (hgen 0) t hring ht
  have hU0aff : IsAffineOpen U0 := by
    simpa [hU0] using hAC.affine {0} (Finset.singleton_nonempty 0)
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI hart : IsArtinianRing (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    haveI := GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover ℂ X.functionField F d x hFC
    exact RingEquiv.isArtinianRing E.symm
  have hred : IsReduced (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    refine GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' _ _ hart fun m hm hIm => ?_
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal X p U0 hU0aff m hm
    refine htr y hy fun j => ?_
    exact hIm (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨F, x, fun i => GlobalTheory.EtProj.fOpen ι (f i), hFC, hAC, ?_, fun y hyS => ⟨(hS y hyS).1, ?_⟩⟩
  · haveI := hred
    exact isReduced_of_injective E.symm E.symm.injective
  · intro j hg g hgj
    have : g = t j := by
      apply germ_injective_of_isIntegral X _ hg
      exact hgj.trans (ht j).symm
    rw [this]
    exact (hS y hyS).2 j

end GlobalTheory.PD.FibRed
end
end

section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential
theorem _root_.GlobalTheory.T.exists_finiteCover_projSpace_reduced_fibre_origin : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → IsProjOver p → ∀ S : Finset (CxPts p (RingHom.id ℂ)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F) (U : Fin (d + 1) → X.Opens), IsFinCover ℂ X.functionField x ∧ IsAffCover p U (rB ℂ X.functionField x) ∧ IsReduced ((rB ℂ X.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) ∧ ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (U 0) ∧ ∀ j : Fin d, ∀ (hg : genericPoint X ∈ U 0) (f : Sec p (U 0)), (X.presheaf.germ (U 0) (genericPoint X) hg).hom f = algebraMap F X.functionField (x j.succ / x 0) → CxPts.ev p (RingHom.id ℂ) (U 0) f y = 0 := by
  first | exact @GlobalTheory.PD.FibRed.exists_finCover_fibre_reduced | exact GlobalTheory.PD.FibRed.exists_finCover_fibre_reduced | exact @GlobalTheory.PD.FibRed.quotEquiv_of_germ | exact GlobalTheory.PD.FibRed.quotEquiv_of_germ
end
