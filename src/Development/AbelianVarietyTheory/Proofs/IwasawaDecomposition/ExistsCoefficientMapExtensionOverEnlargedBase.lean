import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseWeightEqForcedLiftWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharactersTypePrimesEqOfExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarMulSelfOfPair

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

open Formalism.DivisionValues

variable {D : D7}

theorem exists_unit_of_pow (a : D.what₂.LL) (n : ℕ) (hn : n ≠ 0) (ha : a ^ n = 1) :
    ∃ u : (𝓞 D.what₂.LL)ˣ, ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = a ∧ a ∈ Formalism.DivisionValues.cmMax D.what₂.LL ∧ star a * a = 1 := by
  have hσ : ∀ σ : D.what₂.LL →+* ℂ, ‖σ a‖ = 1 := fun σ => by
    have h : (σ a) ^ n = 1 := by rw [← map_pow, ha, map_one]
    exact Complex.norm_eq_one_of_pow_eq_one h hn
  have hconj : ∀ z : ℂ, ‖z‖ = 1 → starRingEnd ℂ z = z⁻¹ := fun z hz => by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  have a0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at ha
    exact zero_ne_one ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 a0
  have h2 : star a * a = 1 := D.what₂.embLL.injective (by
    rw [map_mul, D.starLL_cx, hconj _ (hσ _), inv_mul_cancel₀ m0, map_one])
  have hs : star a = a⁻¹ := eq_inv_of_mul_eq_one_left h2
  have h1 : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL := by
    change ∀ σ : D.what₂.LL →+* ℂ, σ (star a) = starRingEnd ℂ (σ a)
    intro σ
    rw [hs, map_inv₀, hconj _ (hσ σ)]
  have hi : IsIntegral (𝓞 D.what₂.LL) a := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [ha]
    exact isIntegral_one
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hx1 : x ^ n = 1 := IsFractionRing.injective (𝓞 D.what₂.LL) D.what₂.LL (by rw [map_pow, hx, ha, map_one])
  refine ⟨(IsUnit.of_pow_eq_one hx1 hn).unit, ?_, h1, h2⟩
  rw [IsUnit.unit_spec]
  exact hx

theorem coefMapTie_smul {V C lam c0 rho} (h : Formalism.IndefR.Bridge.CoefMapTie (D := D) V C (lam := lam) c0 rho) {μ : ℂ} (hμ : μ ≠ 0) :
    Formalism.IndefR.Bridge.CoefMapTie V C (μ • c0) rho := by
  obtain ⟨a1, a2, a3⟩ := h
  refine ⟨fun γ γE hγ v => by simp [a1 γ γE hγ v], a2.units_smul fun _ => Units.mk0 _ hμ, ?_⟩
  rw [eq_top_iff, ← a3, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have := Submodule.smul_mem _ μ⁻¹ (Submodule.subset_span (R := ℂ)
    (s := Set.range fun i => (μ • c0) (bVV D.what₂.LL lam i)) ⟨i, rfl⟩)
  exact Set.mem_of_eq_of_mem (inv_smul_smul₀ hμ (c0 _)).symm this

theorem coefTie_smul {V C S J χ P lam c0 pair nab del}
    (h : Formalism.IndefR.Bridge.CoefTie (D := D) V C (S := S) (J := J) (χ := χ) P lam c0 pair nab del)
    (l : D.what₂.LL) (u : (𝓞 D.what₂.LL)ˣ) (hu : ((u : 𝓞 D.what₂.LL) : D.what₂.LL) = l) (h1 : l ∈ Formalism.DivisionValues.cmMax D.what₂.LL)
    (h2 : star l * l = 1) :
    Formalism.IndefR.Bridge.CoefTie V C P lam (D.what₂.embLL l • c0) pair nab del := by
  have l0 : l ≠ 0 := right_ne_zero_of_mul_eq_one h2
  have m0 : D.what₂.embLL l ≠ 0 := (map_ne_zero _).2 l0
  have li : (((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) : D.what₂.LL) = l⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← hu, ← map_mul (algebraMap (𝓞 D.what₂.LL) D.what₂.LL), Units.inv_mul, map_one])
  obtain ⟨e, a1, a2, a3, a4, a5⟩ := h
  let s := LinearEquiv.smulOfNeZero D.what₂.LL (VV D.what₂.LL lam) l⁻¹ (inv_ne_zero l0)
  have hs : ∀ x, (e.trans s) x = l⁻¹ • e x := fun _ => rfl
  have hm : ∀ N : Submodule (𝓞 D.what₂.LL) S.V,
      N.map ((e.trans s).toLinearMap.restrictScalars (𝓞 D.what₂.LL)) =
        N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := fun N => by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨((u⁻¹ : (𝓞 D.what₂.LL)ˣ) : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      exact (map_smul e _ _).trans (congrArg (· • e v) li)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(u : 𝓞 D.what₂.LL) • v, N.smul_mem _ hv, ?_⟩
      rw [← algebraMap_smul D.what₂.LL]
      show (e.trans s) ((algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL)) • v) = e v
      rw [show algebraMap (𝓞 D.what₂.LL) D.what₂.LL (u : 𝓞 D.what₂.LL) = l from hu]
      exact (hs _).trans ((congrArg (l⁻¹ • ·) (map_smul e l v)).trans (inv_smul_smul₀ l0 _))
  refine ⟨e.trans s, fun i j => ?_, fun x => ?_, fun x x' => ?_, fun c => (hm _).trans (a4 c), fun c => (hm _).trans (a5 c)⟩
  · rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem (inv_mem h1) (a1 i j)
  · rw [hs, LinearMap.smul_apply, map_smulₛₗ, map_inv₀, smul_inv_smul₀ m0, a2]
  · rw [hs, hs, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, a3, smul_smul, starRingEnd_apply, star_inv₀,
      ← mul_inv, mul_comm, h2, inv_one, one_smul]

end GlobalTheory.Mem.R3.Rw.OmExt.RootUpd

namespace GlobalTheory.Mem.R3.Rw.OmExt

set_option maxHeartbeats 1000000 in

theorem coefFam_update_root : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W),
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R c0L → ∀ (i : Fin D.R.m) (a : D.what₂.LL) (n : ℕ), n ≠ 0 → a ^ n = 1 →
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R (Function.update c0L i (D.what₂.embLL a • c0L i)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R c0L hc i a n hn ha
  obtain ⟨u, hu, h1, h2⟩ := RootUpd.exists_unit_of_pow a n hn ha
  have m0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 (right_ne_zero_of_mul_eq_one h2)
  obtain ⟨gramR, c0R, ht⟩ := hc
  refine ⟨gramR, c0R, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ht.ok, ht.gramR_eq, ht.mapR, fun j => ?_,
    ht.coefR, fun j t => ?_⟩⟩
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefMapTie_smul (ht.mapL j) m0
    · rw [Function.update_of_ne hj]
      exact ht.mapL j
  · rcases eq_or_ne j i with rfl | hj
    · rw [Function.update_self]
      exact RootUpd.coefTie_smul (ht.coefL j t) a u hu h1 h2
    · rw [Function.update_of_ne hj]
      exact ht.coefL j t

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteFamilyCoefficientMaps_mul_rootOfUnity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W),
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R c0L → ∀ (i : Fin D.R.m) (a : D.what₂.LL) (n : ℕ), n ≠ 0 → a ^ n = 1 →
    GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R (Function.update c0L i (D.what₂.embLL a • c0L i)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.OmExt.coefFam_update_root | exact GlobalTheory.Mem.R3.Rw.OmExt.coefFam_update_root | (intros; apply GlobalTheory.Mem.R3.Rw.OmExt.coefFam_update_root <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

def mapVVι {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {T : Type} [Fintype T] {n : ℕ} (lam : T → DomWeight n)
    (v : VV K lam) : VV K' lam :=
  ⟨MvPolynomial.map ι v.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV ι lam _ v.2⟩

theorem exists_smul_eq_enl {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {K' : Type} [Field K'] (ι : D.what₂.LL →+* K')
    (emb' : K' →+* ℂ) (hι : ∀ x, emb' (ι x) = D.what₂.embLL x) (tau : D.what₂.Tau → D.host.E →+* D.what₂.LL)
    (tau' : D.what₂.Tau → D.host.E →+* K') (htau : ∀ τ, emb'.comp (tau' τ) = D.what₂.embLL.comp (tau τ))
    {lam : D.what₂.Tau → DomWeight V.rank}
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W) (h0 : Bridge.CoefMapTie V c.coef c0 (rhoVr tau lam))
    (c' : CoefA V) (hcc : c' = c) (c0' : VV K' lam →ₛₗ[emb'] c'.W)
    (h1 : ∀ γ γE, Bridge.IsRatMat V γ γE → ∀ v, c0' (rhoVr tau' lam γE v) = c'.coef.ρ γ (c0' v)) :
    ∃ μ : ℂ, ∀ (v : VV D.what₂.LL lam) (v' : VV K' lam),
      MvPolynomial.map emb' v'.1 = MvPolynomial.map D.what₂.embLL v.1 → HEq (c0' v') (μ • c0 v) := by
  subst c'
  have hcomp : emb'.comp ι = D.what₂.embLL := RingHom.ext hι
  have hinj : ∀ a b : VV K' lam, MvPolynomial.map emb' a.1 = MvPolynomial.map emb' b.1 → a = b := fun a b h =>
    Subtype.ext (MvPolynomial.map_injective emb' emb'.injective h)
  have hmap : ∀ v : VV D.what₂.LL lam, MvPolynomial.map emb' (mapVVι ι lam v).1 = MvPolynomial.map D.what₂.embLL v.1 := fun v => by
    show MvPolynomial.map emb' (MvPolynomial.map ι v.1) = _
    rw [MvPolynomial.map_map, hcomp]
  have hsm : ∀ (a : D.what₂.LL) (v : VV D.what₂.LL lam), mapVVι ι lam (a • v) = ι a • mapVVι ι lam v := fun a v =>
    Subtype.ext (by
      show MvPolynomial.map ι (a • v.1) = ι a • MvPolynomial.map ι v.1
      rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul])
  let c1 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.W :=
    { toFun := fun v => c0' (mapVVι ι lam v)
      map_add' := fun a b => by
        rw [← map_add]
        congr 1
        exact Subtype.ext (map_add _ _ _)
      map_smul' := fun a v => by
        show c0' (mapVVι ι lam (a • v)) = D.what₂.embLL a • c0' (mapVVι ι lam v)
        rw [hsm, map_smulₛₗ, hι] }
  have hrho : ∀ γE v, mapVVι ι lam (rhoVr tau lam γE v) = rhoVr tau' lam γE (mapVVι ι lam v) := fun γE v => by
    refine hinj _ _ ?_
    rw [hmap]
    have e1 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr D.what₂.embLL tau lam γE v)
    have e2 := congrArg Subtype.val (GlobalTheory.ConjTwist.mapVV_rhoVr emb' tau' lam γE (mapVVι ι lam v))
    rw [GlobalTheory.CoefModel.mapVV_coe] at e1 e2
    rw [e1, e2]
    have e3 : (fun τ => emb'.comp (tau' τ)) = fun τ => D.what₂.embLL.comp (tau τ) := funext htau
    have e4 : GlobalTheory.CoefModel.mapVV emb' lam (mapVVι ι lam v) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam v :=
      Subtype.ext (hmap v)
    rw [e3, e4]
  obtain ⟨μ, hμ⟩ := RowCoord.exists_smul_eq c hc h0 c1 fun γ γE hγ v => by
    show c0' (mapVVι ι lam (rhoVr tau lam γE v)) = c.coef.ρ γ (c0' (mapVVι ι lam v))
    rw [hrho]
    exact h1 γ γE hγ _
  refine ⟨μ, fun v v' hv => heq_of_eq ?_⟩
  have : v' = mapVVι ι lam v := hinj _ _ (hv.trans (hmap v).symm)
  subst this
  exact hμ v

end GlobalTheory.Mem.R3.Rw.OmExt
end

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem coefA_eq {D : D7} {V : HSp D} (c c' : CoefA V) (hW : HEq c'.W c.W) (hρ : HEq c'.ρ c.ρ) (hn : HEq c'.nW c.nW)
    (hi : HEq c'.iW c.iW) : c' = c := by
  cases c
  cases c'
  dsimp only at hW hρ hn hi
  cases hW
  cases hn
  cases hi
  cases hρ
  rfl

set_option maxHeartbeats 4000000 in

theorem coef_schur : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hff hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hRS i i' hii c0L hc c0L'' hc''
  obtain ⟨gR, c0R, ht⟩ := hc
  obtain ⟨gR', c0R', ht'⟩ := hc''
  obtain ⟨hW, hρ, hnW, hiW, -⟩ := hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii
  have hcI := z.pins.char.base.models.cV i
  have hmapL := ht.mapL i
  have hmapL' := ht'.mapL i'
  have htau := ht.tauL_ok
  have htau' := ht'.tauL_ok
  obtain ⟨hpre, -, -, hR⟩ := hE
  cases B with | mk P => cases B' with | mk P' =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i = i' := Fin.ext hii
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (enlEmb hR)
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (enlEmb_spec hR)
  let c'' : CoefA (Vc (w.st Z).toD7 i) :=
    { W := (R'.cV i).W, nW := (R'.cV i).nW, iW := (R'.cV i).iW, fW := (R'.cV i).fW, ρ := (R'.cV i).ρ }
  have hcc : c'' = z.R.cV i := coefA_eq _ _ hW hρ hnW hiW
  obtain ⟨μ, hμ⟩ := exists_smul_eq_enl (z.R.cV i) hcI ι (w'.st Z').toD7.what₂.embLL hι (labLL (w.st Z).toD7)
    (labLL (w'.st Z').toD7) (fun τ => (htau' τ).trans (htau τ).symm) (c0L i) hmapL c'' hcc (c0L'' i) hmapL'.1
  exact ⟨μ, fun v v' hv => hμ v v' (eq_of_heq hv)⟩

end GlobalTheory.Mem.R3.Rw.OmExt
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientMap_enlargedBase_eq_complexMultiple : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  first | exact @GlobalTheory.Mem.R3.Rw.OmExt.coef_schur | exact GlobalTheory.Mem.R3.Rw.OmExt.coef_schur | (intros; apply GlobalTheory.Mem.R3.Rw.OmExt.coef_schur <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LiftUnit

open Formalism.DivisionValues Formalism.L2.Col

theorem exists_cast {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι]
    {a n : ℕ} (h : n = a) (emb : ι → E →+* K) (lam : ι → DomWeight a) (lam' : ι → DomWeight n)
    (hw : ∀ τ (i : Fin a) (i' : Fin n), (i : ℕ) = i' → (lam τ).w i = (lam' τ).w i') :
    ∃ e0 : VV K lam' ≃ₗ[K] VV K lam,
      (∀ (σ : K →+* ℂ) v, HEq (MvPolynomial.map σ (e0 v).1) (MvPolynomial.map σ v.1)) ∧
      (∀ i j, (bVV K lam).repr (e0 (bVV K lam' i)) j ∈ cmMax K) ∧
      (∀ x y, pairVr emb lam 1 (e0 x) (e0 y) = pairVr emb lam' 1 x y) ∧
      (∀ γ : GL (Fin a) E, ∃ g, MatEq γ g ∧ ∀ v, e0 (rhoVr emb lam' g v) = rhoVr emb lam γ (e0 v)) ∧
      ∀ L L', (∀ x, x ∈ L ↔ (fun i => x (Fin.cast h i)) ∈ L') →
        (nabAtr emb lam' L').map ((e0 : VV K lam' →ₗ[K] VV K lam).restrictScalars (𝓞 K)) = nabAtr emb lam L := by
  subst h
  obtain rfl : lam = lam' := funext fun τ => by
    have : (lam τ).w = (lam' τ).w := funext fun i => hw τ i i rfl
    revert this
    cases lam τ
    cases lam' τ
    rintro rfl
    rfl
  refine ⟨LinearEquiv.refl _ _, fun σ v => HEq.rfl, fun i j => ?_, fun _ _ => rfl,
    fun γ => ⟨γ, ⟨rfl, fun i j i' j' a b => ?_⟩, fun _ => rfl⟩, fun L L' hL => ?_⟩
  · classical
    rw [LinearEquiv.refl_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Fin.ext a, Fin.ext b]
  · obtain rfl : L = L' := Submodule.ext hL
    exact Submodule.map_id _

theorem root_of_pres {D : D7} {V : HSp D} (C : Bridge.CoefDat D V) (S : GSD D.what₂.LL) (hG : S.Good 1) (hR : S.Rat) {J χ}
    (P : Bridge.ClassPres (Bridge.ratF V) (S.toCSD hG.ok) D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W) (hli : LinearIndependent ℂ fun i => c0 (bVV _ lam i)) {pair nab del}
    (ht : Bridge.CoefTie V C P lam c0 pair nab del)
    (e0 : S.V ≃ₗ[D.what₂.LL] VV D.what₂.LL lam) (er0 : ∀ i j, (bVV _ lam).repr (e0 (S.bV i)) j ∈ cmMax D.what₂.LL)
    (pe0 : ∀ x y, pair (e0 x) (e0 y) = S.pair x y) (d : Bridge.Gf V → S.D)
    (hd : ∀ h, (S.Nab (d h)).map (e0.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) = nab (Bridge.hLat V h)) (μ : ℂ)
    (H : ∀ (φ : S.EqFun) h, P.extL (S.res hG.ok φ) h = μ • c0 (e0 (φ.1 (d h)))) (φ : S.EqFun) (hφ : φ ≠ 0) :
    ∃ (u : D.what₂.LL) (n : ℕ), n ≠ 0 ∧ u ^ n = 1 ∧ D.what₂.embLL u = μ := by
  obtain ⟨e, a1, a2, a3, a4, -⟩ := ht
  have pos : ∀ x : S.V, x ≠ 0 → 0 < (D.what₂.embLL (S.pair x x)).re := fun x hx => by
    have h1 : P.coef x ≠ 0 := fun h => hx (GlobalTheory.PresBasic.coef_injective P (h.trans (map_zero _).symm))
    have h2 := P.coef_pair x x
    exact h2 ▸ (re_inner_self_pos (𝕜 := ℂ)).2 h1
  obtain ⟨c, hc⟩ : ∃ c, φ.1 (S.outSec.rep c) ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ ((S.res hG.ok).map_eq_zero_iff.1 (Subtype.ext (funext h)))
  obtain ⟨u, u1, u2, u3⟩ := RowCoord.exists_unit S hG hR
    (fun x hx => by_contra fun h => (pos x h).ne' (by rw [hx, map_zero, Complex.zero_re])) _ (bVV _ lam) c0
    hli _ e e0 c (d (P.y c)) μ
    (fun ψ => ((a2 _).symm.trans (GlobalTheory.PresBasic.ext_y P (S.res hG.ok ψ) c).symm).trans (H ψ _))
    φ hc a1 er0 a3 pe0 ((a4 c).trans (hd _).symm)
  obtain ⟨n, hn, h⟩ := GlobalTheory.CoefUniq.pow_eq_one_of_cmMax u2 u3 (NumberField.RingOfIntegers.isIntegral_coe _)
  exact ⟨_, n, hn, h, u1⟩

theorem gram_eq_one (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) (i : Fin X.toD7.R.m) :
    (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := hI.spaces
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.B.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.B.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem decoOf_lat {X : Formalism.L2.Col.Fields} (hc : CMData X.F X.E) (n : ℕ) [NeZero n] (S : Finset (Pl X.E)) (y : UAd hc n) :
    (decoOf (F := X.F) (E := X.E) ∅ S y.1).1.N = Formalism.UG.CS.globLat y.1 (Formalism.L2.Col.stdLat X.E n) := by
  have hok := decorated_lattice_exists hc n ∅ S y.1 y.2
  have e : (decoOf (F := X.F) (E := X.E) ∅ S y.1).1 = decoRaw ∅ S y.1 := congrArg Subtype.val (dif_pos hok)
  rw [e]
  rfl

set_option maxHeartbeats 4000000 in

theorem exists_root_reading (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R : RealDat X.toD7 (famR X I hX U Xg tr).A Ks) (hI : I.Ok) (hL : LevOf X I U R.toLevCh) (i : Fin X.toD7.R.m)
    (hc : (R.cV i).Is) (c0L) (hT : OmExt.CoefFam R c0L)
    (hS : BrgStdV X I hX U Xg tr R.toLevCh i (R.cV i) fun t φ => R.B.jL i t φ) (t : TupU I U)
    (φ : (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (hφ : φ ≠ 0) :
    ∃ (u : X.toD7.what₂.LL) (n : ℕ), n ≠ 0 ∧ u ^ n = 1 ∧
      ∀ (ψ : (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i))
        (y : UAd X.toD7.sp.cm X.B.R.nV), MatEq (matIn (Vc X.toD7 i) 1 h) (y : GL (Fin X.B.R.nV) _) →
        ∃ v : Formalism.IndefR.FWT.VsV X.toD7 i X.toD7.what₂.LL,
          HEq (MvPolynomial.map X.toD7.what₂.embLL v.1) (MvPolynomial.map (X.B.embLL : X.B.fields.K →+* ℂ)
            (ψ.1 (decoOf (F := X.B.fields.F) (E := X.B.fields.E) ∅ (rowSG (X.B.primes px) I.sel t.1) y.1)).1) ∧
          R.B.jL i t ((mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _) ψ) h =
            X.toD7.what₂.embLL u • c0L i v := by
  obtain ⟨gram, c0R, hT⟩ := hT
  obtain ⟨c, hcI, hcR, -⟩ := hS
  have hG := gram_eq_one X I hI i
  have hβ := hL.beta.1 i
  have hr : (Vc X.toD7 i).rank = X.B.R.nV := (LiftBrg.rkEq X i).symm
  obtain ⟨e0, k1, k2, k3, k4, k5⟩ := exists_cast (K := X.toD7.what₂.LL) hr.symm (labLL X.toD7)
    (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) (X.B.wts.lamV ((i : ℕ) + 1))
    (fun τ a a' e => LiftWt.lamLdef_eq_lamV X _ (by omega) i.2 τ a a' e)
  have hR : ∀ (ψ : (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i))
      (y : UAd X.toD7.sp.cm X.B.R.nV), MatEq (matIn (Vc X.toD7 i) 1 h) (y : GL (Fin X.B.R.nV) _) →
      R.B.jL i t ((mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _) ψ) h =
        c (ψ.1 (decoOf (F := X.B.fields.F) (E := X.B.fields.E) ∅ (rowSG (X.B.primes px) I.sel t.1) y.1)) := fun ψ h y hy => by
    refine (hcR X.toD7.sp.cm t (⟨mtKOk _ _ _ _ hX _⟩, ψ) h y (by rw [hβ]; exact hy)).trans ?_
    exact congrArg (fun d => c (ψ.1 d)) (decoPt_mk _ _ _ _ y)
  let c1 : Formalism.IndefR.FWT.VsV X.toD7 i X.toD7.what₂.LL →ₛₗ[X.toD7.what₂.embLL] (R.cV i).W :=
    (show VV X.toD7.what₂.LL (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.toD7.what₂.embLL] (R.cV i).W from c).comp e0.symm.toLinearMap
  have hc1 : ∀ v, c1 (e0 v) = c v := fun v => congrArg c (e0.symm_apply_apply v)
  obtain ⟨μ, hμ⟩ := RowCoord.exists_smul_eq (R.cV i) hc (hT.mapL i) c1 fun γ γE hγ v => by
    obtain ⟨v, rfl⟩ := e0.surjective v
    obtain ⟨g, g1, g2⟩ := k4 γE
    rw [← g2, hc1, hc1]
    exact hcI γ γE g hγ g1 v
  choose x hx using RowCoord.exists_matEq (D := X.toD7) (Vc X.toD7 i) hr hG
  have hneg : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  have ht := hT.coefL i t
  have hgr : (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram) = 1 := by
    rw [hneg, if_neg (by simp)]
    exact hG
  rw [hgr] at ht
  have hΛ := hL.is.βV i
  rw [hβ] at hΛ
  obtain ⟨u, n, hn, hu, u1⟩ := root_of_pres (R.cV i).coef (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1))
    (mtK_good _ _ _ _ hX _) (mtK_rat _ _ _ _ hX _) (R.B.L i t).pres (c0L i) (hT.mapL i).2.1 ht e0 k2 k3
    (fun h => decoOf (F := X.B.fields.F) (E := X.B.fields.E) ∅ (rowSG (X.B.primes px) I.sel t.1) (x h).1)
    (fun h => k5 _ _ fun v => (RowCoord.mem_hLat_iff hΛ h hr.symm _ (hx h) v).trans
      (SetLike.ext_iff.1 (decoOf_lat (X := X.B.fields) X.toD7.sp.cm X.B.R.nV (rowSG (X.B.primes px) I.sel t.1) (x h)) _).symm) μ
    (fun ψ h => (hR ψ h _ (hx h)).trans ((hc1 _).symm.trans (hμ _))) φ hφ
  refine ⟨u, n, hn, hu, fun ψ h y hy => ⟨e0 _, k1 _ _, ?_⟩⟩
  rw [u1]
  exact (hR ψ h y hy).trans ((hc1 _).symm.trans (hμ _))

theorem exists_form_enl {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hE : Enl0 B B') (hf : HEq f' f) (hpx : HEq w'.px w.px)
    (j j' : ℕ) (hj : j = j')
    (φ : (mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).EqFun) :
    ∃ φ' : (mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').EqFun,
      ∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1) := by
  subst hj
  obtain ⟨hpre, -, -, hrange⟩ := hE
  obtain ⟨ι, hι⟩ := exists_iota_comp B.embLL B'.embLL hrange
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have ef : f' = f := eq_of_heq hf
  have ep : w'.px = w.px := eq_of_heq hpx
  have hv : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  refine (liftRound_reidx (baseOfColW w).fields ι (baseOfColW w').tauLL ?_ _ ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hι).2 φ
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    rw [RingHom.comp_apply, hι]
    exact h1.trans h2.symm
  · exact (rowLevelPrimes_colTuples_eq_vGs w' W').trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w W).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w W) (twistRamifiedPrimes_empty_colTuples w' W') _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of ι p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    rw [hι]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    have eC : w'.I.C = w.I.C := w'.C_eq.trans (ef.trans w.C_eq.symm)
    rw [eC] at e1
    exact e1.trans e2.symm

theorem heq_decoOf {X : Formalism.L2.Col.Fields} {n : ℕ} [NeZero n] {S S' : Finset (Pl X.E)} (h : S' = S) (y) :
    HEq (decoOf (F := X.F) (E := X.E) (n := n) ∅ S' y) (decoOf (F := X.F) (E := X.E) (n := n) ∅ S y) := by
  subst h
  rfl

theorem heq_apply {α β β' : Type} {g : α → β} {g' : α → β'} (e : β' = β) (h : HEq g' g) (a : α) : HEq (g' a) (g a) := by
  subst e
  cases h
  rfl

set_option maxHeartbeats 8000000 in

theorem exists_agree_root : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x ≠ 0 →
    ∃ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL)
      (u : (w.st Z).toD7.what₂.LL) (u' : (w'.st Z').toD7.what₂.LL) (n n' : ℕ), n ≠ 0 ∧ u ^ n = 1 ∧ n' ≠ 0 ∧ u' ^ n' = 1 ∧
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) ∧ c0L i v ≠ 0 ∧
      HEq ((w'.st Z').toD7.what₂.embLL u' • c0L'' i' v') ((w.st Z).toD7.what₂.embLL u • c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hRS i i' hii c0L hc c0L'' hc'' x hx
  obtain ⟨φ, rfl⟩ := ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
    ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _)).surjective x
  have hφ : φ ≠ 0 := fun h0 => hx (h0 ▸ map_zero _)
  obtain ⟨h, hh⟩ : ∃ h, z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))
      ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
        ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _) φ) h ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (GlobalTheory.PresBasic.extL_injective (z.R.B.L i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))).pres
      ((funext hn).trans (map_zero _).symm))
  obtain ⟨φ', hφφ⟩ := exists_form_enl w w' Wt Wt' hE hf hpx ((i : ℕ) + 1) ((i' : ℕ) + 1) (by rw [hii]) φ
  have hj := hRS.2.2.2.2.2.2.2.2.2.2.2.2.2 i i' hii (mtKOk _ _ _ _ hX _) (mtKOk _ _ _ _ hX' _) φ φ' hφφ
  have hW := (hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hii).1
  obtain ⟨u, n, hn, hu, H⟩ := exists_root_reading (w.st Z) w.I hX _ z.Xg z.tr z.R.toRealDat w.ok z.lev i
    (z.pins.char.base.models.cV i) c0L hc (hstd.2 i) _ φ hφ
  obtain ⟨y, hy⟩ := RowCoord.exists_matEq (D := (w.st Z).toD7) (Vc (w.st Z).toD7 i) (LiftBrg.rkEq (w.st Z) i).symm
    (gram_eq_one (w.st Z) w.I w.ok i) h
  obtain ⟨v, hv1, hv2⟩ := H φ h y hy
  have H' := exists_root_reading (w'.st Z') w'.I hX' _ Xg tr R'.toRealDat w'.ok hL i'
    (hP.char.base.models.cV i') c0L'' hc'' (hB.2 i') _ φ'
  have hS := rowLevelPrimes_colTuples_eq_vGs w Wt
  have hS' := rowLevelPrimes_colTuples_eq_vGs w' Wt'
  clear H hRS hB hP hL hstd hc hc''
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i' = i := Fin.ext hii.symm
  have ep : w'.px = w.px := eq_of_heq hpx
  have hvG : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  have hjh := heq_apply (eq_of_heq hW) hj h
  have hSS := hS'.trans (hvG.trans hS.symm)
  have hd := hφφ _ _ (heq_decoOf (X := (baseOfColW w).fields) hSS y.1)
  have h0 : c0L i' v ≠ 0 := fun e => hh (hv2.trans ((congrArg _ e).trans (smul_zero (A := (z.R.cV i').W) _)))
  have hφ' : φ' ≠ 0 := fun e => hφ (Subtype.ext (funext fun d => Subtype.ext (by
    have e1 := eq_of_heq (hφφ d (cast (congrArg (DecoSet (baseOfColW w).fields.E (baseOfColW w).R.nV ∅) hSS.symm) d) (cast_heq _ _))
    rw [e] at e1
    exact MvPolynomial.map_injective _ (baseOfColW w).embLL.injective (e1.symm.trans ((map_zero _).trans (map_zero _).symm)))))
  obtain ⟨u', n', hn', hu', H⟩ := H' hφ'
  obtain ⟨v', hv1', hv2'⟩ := H φ' h y hy
  exact ⟨v, v', u, u', n, n', hn, hu, hn', hu', hv1'.trans (hd.trans hv1.symm), h0,
    (heq_of_eq hv2'.symm).trans (hjh.trans (heq_of_eq hv2))⟩

end GlobalTheory.Mem.R3.Rw.LiftUnit

end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientMaps_agree_rootOfUnity_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
    ∀ c0L'', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' →
    ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x ≠ 0 →
    ∃ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL)
      (u : (w.st Z).toD7.what₂.LL) (u' : (w'.st Z').toD7.what₂.LL) (n n' : ℕ), n ≠ 0 ∧ u ^ n = 1 ∧ n' ≠ 0 ∧ u' ^ n' = 1 ∧
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) ∧ c0L i v ≠ 0 ∧
      HEq ((w'.st Z').toD7.what₂.embLL u' • c0L'' i' v') ((w.st Z).toD7.what₂.embLL u • c0L i v) := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftUnit.exists_agree_root | exact GlobalTheory.Mem.R3.Rw.LiftUnit.exists_agree_root | (intros; apply GlobalTheory.Mem.R3.Rw.LiftUnit.exists_agree_root <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmCoef

theorem smul_eq_of_heq {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ a b : ℂ}
    (h1 : HEq x' (μ • y)) (h2 : HEq (a • x') (b • y)) : (a * μ) • y = b • y := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]
  exact eq_of_heq h2

theorem heq_smul {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ : ℂ}
    (h1 : HEq x' (μ • y)) (a : ℂ) : HEq (a • x') ((a * μ) • y) := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]

end GlobalTheory.Mem.R3.Rw.OmCoef

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
      (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) ∨
      ∃ c0L', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L' ∧
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hR i i' hii c0L hc
  obtain ⟨g'', c0R'', c0L'', hT''⟩ := hP.char.base.fam.tie
  have hc'' : GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' := ⟨g'', c0R'', hT''⟩
  by_cases h0 : ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
      (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0
  · exact Or.inl h0
  right
  push_neg at h0
  obtain ⟨x, hx⟩ := h0
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.coefficientMap_enlargedBase_eq_complexMultiple z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc''
  obtain ⟨v, v', u, u', n, n', hn, hun, hn', hun', hvv, hv0, hrel⟩ :=
    GlobalTheory.T.exists_coefficientMaps_agree_rootOfUnity_enlarged z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc'' x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcv, -⟩ := hR
  obtain ⟨hW, -, hnW, hiW, -⟩ := hcv i i' hii
  have key := GlobalTheory.Mem.R3.Rw.OmCoef.smul_eq_of_heq (eq_of_heq hW) hnW hiW (hμ v v' hvv) hrel
  have hμe : (w'.st Z').toD7.what₂.embLL u' * μ = (w.st Z).toD7.what₂.embLL u := smul_left_injective ℂ hv0 key
  have hu0 : (w.st Z).toD7.what₂.embLL u ≠ 0 := (map_ne_zero _).2 fun h => by
    rw [h, zero_pow hn] at hun
    exact zero_ne_one hun
  obtain ⟨b, hb⟩ : (w.st Z).toD7.what₂.embLL u ∈ Set.range (w'.st Z').toD7.what₂.embLL := hE.2.2.2 ⟨u, rfl⟩
  have hb1 : b ^ n = 1 := (w'.st Z').toD7.what₂.embLL.injective (by rw [map_pow, hb, ← map_pow, hun, map_one, map_one])
  have ha : (u' * b⁻¹) ^ (n * n') = 1 := by
    have e1 : u' ^ (n * n') = 1 := by rw [mul_comm, pow_mul, hun', one_pow]
    have e2 : b ^ (n * n') = 1 := by rw [pow_mul, hb1, one_pow]
    rw [mul_pow, inv_pow, e1, e2, inv_one, mul_one]
  refine ⟨Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i'),
    GlobalTheory.T.definiteFamilyCoefficientMaps_mul_rootOfUnity R'.toRealDat c0L'' hc'' i' (u' * b⁻¹) (n * n') (mul_ne_zero hn hn') ha, fun v1 v1' h => ?_⟩
  have eu : Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i') i' =
      (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i' := Function.update_self _ _ _
  refine (heq_of_eq ((congrArg (fun g => g v1') eu).trans (LinearMap.smul_apply _ _ _))).trans ?_
  refine (GlobalTheory.Mem.R3.Rw.OmCoef.heq_smul (eq_of_heq hW) hnW hiW (hμ v1 v1' h) _).trans (heq_of_eq ?_)
  have e1 : (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = 1 := by
    calc (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = ((w'.st Z').toD7.what₂.embLL u' * μ) * ((w.st Z).toD7.what₂.embLL u)⁻¹ := by
          rw [map_mul, map_inv₀, hb]; ring
      _ = 1 := by rw [hμe, mul_inv_cancel₀ hu0]
  rw [e1, one_smul]

end
end
