import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjWeilDatumExchangedPairStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConstantTermSourceTargetConjAdjointCorr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntegrandPeriodic
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFundamentalDomainEqIteratedDecomp

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

variable {D : D7}

theorem exists_split (W : HSp D) {s : ℕ} (I : Matrix (Fin W.rank) (Fin s) D.host.E) (hI : IsIsoFrame W I) :
    ∃ (W' : HSp D) (ι : W'.V →ₗ[D.host.E] W.V), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I (frameMat W W' ι) := by
  obtain ⟨e, rfl⟩ := GlobalTheory.BesselCompare.eMat_surj W I
  have he : LinearIndependent D.host.E e :=
    LinearIndependent.of_comp W.frame.equivFun.toLinearMap hI.2.1
  have hiso : ∀ a b, W.hT (e a) (e b) = 0 := fun a b => by
    rw [← GlobalTheory.BesselCompare.cT_mul, hI.2.2]; rfl
  obtain ⟨W', ι, h1, h2, h3⟩ := GlobalTheory.WittLow.exists_lower Examples₂.star_isIntegral W e he hiso
  refine ⟨W', ι, ⟨hI, ?_, ?_, by omega⟩⟩
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul]
    exact h2 _ _
  · refine Matrix.ext fun a b => ?_
    unfold GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj
    rw [GlobalTheory.BesselCompare.frameMat_eq, GlobalTheory.BesselCompare.cT_mul, ← W.herm.eq, h3]
    simp

theorem decomp {W W' : HSp D} {s k : ℕ} {I : Matrix (Fin W.rank) (Fin s) D.host.E}
    {B : Matrix (Fin W.rank) (Fin W'.rank) D.host.E} (hsp : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit W W' I B) (x : Mx D W.rank k)
    (hx : rat (Iᴴ * W.gram) ⬝ x = 0) : ∃ (z : Mx D s k) (w : Mx D W'.rank k), x = rat I ⬝ z + rat B ⬝ w := by
  obtain ⟨d, hde, hdi, -⟩ := GlobalTheory.WittSect.exists_hypDec_mem_NI D W W' s I B hsp
  have h := d.sum_eq_one_rat
  simp only [GlobalTheory.MixModel.HypDec.qX, GlobalTheory.MixModel.HypDec.qY, GlobalTheory.MixModel.HypDec.q0, hde, hdi] at h
  have h1 : rat (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) ⬝ x = x := by
    rw [GlobalTheory.MixModel.rat_one, Matrix.one_mul]
  rw [← h, GlobalTheory.MixModel.rat_add, GlobalTheory.MixModel.rat_add, Matrix.add_mul, Matrix.add_mul] at h1
  have h2 : rat (d.e' * (Iᴴ * W.gram)) ⬝ x = 0 := by
    rw [GlobalTheory.MixModel.rat_mul, Matrix.mul_assoc, hx, Matrix.mul_zero]
  rw [h2, add_zero] at h1
  rw [GlobalTheory.MixModel.rat_mul I, GlobalTheory.MixModel.rat_mul B, Matrix.mul_assoc (rat I), Matrix.mul_assoc (rat B)] at h1
  exact ⟨_, _, h1.symm⟩

theorem periodic {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {g : WO V W → ℂ} (hg : IsThetaFunO ψ V W g) {s : ℕ}
    (I : Matrix (Fin W.rank) (Fin s) D.host.E) (p : WO V W) (hp : rat (Iᴴ * W.gram) ⬝ p = 0)
    (γ : Matrix (Fin s) (Fin V.rank) D.host.E) : g (rat I ⬝ rat γ + p) = g p := by
  have e1 : rat I ⬝ rat γ = ratW W V (I * γ) := by rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.rat_mul]
  have e2 : GlobalTheory.MixModel.adj p ⬝ rat (W.gram * I) = 0 := by
    have := congrArg GlobalTheory.MixModel.adj hp
    rwa [GlobalTheory.MixModel.adj_mul, GlobalTheory.MixModel.adj_zero, ← GlobalTheory.MixModel.rat_conjTranspose, conjTranspose_mul,
      GlobalTheory.MixModel.gram_conjTranspose, conjTranspose_conjTranspose] at this
  have e3 : GlobalTheory.MixModel.adj p ⬝ (GlobalTheory.MixModel.gA W ⬝ ratW W V (I * γ)) = 0 := by
    have e2' : GlobalTheory.MixModel.adj p ⬝ (rat W.gram ⬝ rat I) = 0 := by rw [← GlobalTheory.MixModel.rat_mul]; exact e2
    rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.gA, GlobalTheory.MixModel.rat_mul I γ, ← Matrix.mul_assoc (rat W.gram) (rat I) (rat γ),
      ← Matrix.mul_assoc, e2', Matrix.zero_mul]
  rw [e1, hg.quasi, GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, e3, Matrix.mul_zero, Matrix.trace_zero,
    map_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.TargetUnipMean

namespace GlobalTheory.TargetUnipMean

open GlobalTheory.MixModel (rat)
open scoped GlobalTheory.MixModel

theorem mean_unip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ n ∈ NI W I, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, om (1, n) f (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f (HMul.hMul (I.map (incA D)) y + x) ∂ν := by
  intro D ψ V W χV χW om hom s I hI ν 𝓨 hν n hn f hf x hx
  obtain ⟨W', ι, hsp⟩ := exists_split W I hI
  obtain ⟨omt, hmt, hsw⟩ := GlobalTheory.T.exists_conj_weilDatum_exchangedPair D ψ V W χV χW om hom
  obtain ⟨μ', 𝓖', hμ', he⟩ := (GlobalTheory.T.weilConstantTerm_source_target_conjAdjoint_corr D V W W' s ι I).1 ν 𝓨 hν
  have hlaw := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W'
  have hlawW := GlobalTheory.T.hermitianAdjoint_laws_standardCharacter D ψ hom.std V W
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f) = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f := by
    have h1 := GlobalTheory.UnipRes.res_unip D W W' V s I (frameMat W W' ι) hsp ψ χW χV omt hmt μ' 𝓖' hμ' ⟨n, hn⟩
      (GlobalTheory.PairLift.dag V W f) (hlawW.theta f hf)
    have h2 : GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 (om (1, n) f)) =
        GlobalTheory.PairLift.dag V W' (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 f) := by
      rw [← he, ← he, ← hsw]
      exact h1
    funext w
    have h3 := congrFun h2 (GlobalTheory.PairLift.adjO W' V w)
    simp only [GlobalTheory.PairLift.dag, hlaw.invol] at h3
    exact (starRingEnd ℂ).injective h3
  have hII : Iᴴ * W.gram * I = 0 := hI.2.2
  have hIB : Iᴴ * W.gram * frameMat W W' ι = 0 := hsp.orth
  obtain ⟨z, w, hz⟩ := decomp hsp x hx
  have hred : ∀ g, IsThetaFunO ψ V W g → ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + x) ∂ν =
      GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.resT V W W' ι I ν 𝓨 g w := by
    intro g hg
    have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D s V.rank, ∀ a : Mx D s V.rank,
        g (rat I ⬝ (γ + a) + rat (frameMat W W' ι) ⬝ w) = g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w) := by
      intro γ hγ a
      obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
      rw [Matrix.mul_add, add_assoc]
      refine periodic hg I _ ?_ γ0
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hII,
        hIB, GlobalTheory.MixModel.rat_zero, GlobalTheory.MixModel.rat_zero, Matrix.zero_mul, Matrix.zero_mul, add_zero]
    have := GlobalTheory.MixModel.covolOne_integral_add hν (fun a => g (rat I ⬝ a + rat (frameMat W W' ι) ⬝ w)) hper z
    rw [hz]
    calc ∫ y in 𝓨, g (HMul.hMul (I.map (incA D)) y + (rat I ⬝ z + rat (frameMat W W' ι) ⬝ w)) ∂ν
        = ∫ y in 𝓨, g (rat I ⬝ (y + z) + rat (frameMat W W' ι) ⬝ w) ∂ν := by
          congr 1
          funext y
          show g (rat I ⬝ y + _) = _
          rw [Matrix.mul_add, add_assoc]
      _ = _ := this
  rw [hred (om (1, n) f) (hom.om_pres (1, n) f hf), hred f hf, hr]

end GlobalTheory.TargetUnipMean
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFun_isotropic_mean_unipotent_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ n ∈ NI W I, ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, om (1, n) f (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f (HMul.hMul (I.map (incA D)) y + x) ∂ν := by
  atlas_forward_decl GlobalTheory.TargetUnipMean.mean_unip
end

section
section
namespace GlobalTheory

open Matrix

theorem exists_adapted_frame_of_isotropic_columns :
    ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))),
      Module.finrank E Y = r →
      ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E),
        Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y →
        ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose →
          (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) →
          ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E)
            (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E),
            C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧
              J * L + K * M = 1 := by
  intro E _ r Y _ C hspan s I hI hmem

  have hc : ∀ j, ∃ c : Fin r → E,
      ∑ k, c k • ((fun a => C.1 a k), (fun a => C.2 a k)) = ((fun a => I a j), (0 : Fin r → E)) := by
    intro j
    have := hmem j
    rw [← hspan] at this
    exact (Submodule.mem_span_range_iff_exists_fun E).mp this
  choose c hc using hc
  let J : Matrix (Fin r) (Fin s) E := Matrix.of fun k j => c j k
  have h1 : C.1 * J = I := by
    ext a j
    have := congrFun (congrArg Prod.fst (hc j)) a
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : C.2 * J = 0 := by
    ext a j
    have := congrFun (congrArg Prod.snd (hc j)) a
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

  have hIinj : Function.Injective I.mulVec := Matrix.mulVec_injective_iff.mpr hI
  have hJinj : Function.Injective J.mulVec := by
    intro x y hxy
    apply hIinj
    rw [← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  let jL : (Fin s → E) →ₗ[E] (Fin r → E) := Matrix.toLin' J
  have hker : LinearMap.ker jL = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y hxy; exact hJinj (by simpa [jL, Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective jL hker
  let Wk := LinearMap.ker g
  let b := Module.finBasis E Wk
  let kL : (Fin (Module.finrank E Wk) → E) →ₗ[E] (Fin r → E) :=
    Wk.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hgP : ∀ x, g (x - jL (g x)) = 0 := by
    intro x
    rw [map_sub]
    have := LinearMap.congr_fun hg (g x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let ψ : (Fin r → E) →ₗ[E] Wk :=
    LinearMap.codRestrict Wk (LinearMap.id - jL ∘ₗ g) (fun x => by
      simpa [Wk, LinearMap.mem_ker] using hgP x)
  let mL : (Fin r → E) →ₗ[E] (Fin (Module.finrank E Wk) → E) := b.equivFun.toLinearMap ∘ₗ ψ
  have hJ : J = LinearMap.toMatrix' jL := by simp [jL]
  refine ⟨Module.finrank E Wk, J, LinearMap.toMatrix' kL, LinearMap.toMatrix' g,
    LinearMap.toMatrix' mL, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have : g ∘ₗ kL = 0 := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, kL]
      exact (b.equivFun.symm y).2
    rw [this, map_zero]
  · rw [hJ, ← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ jL = 0 := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, mL]
      have : ψ (jL x) = 0 := by
        apply Subtype.ext
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, ZeroMemClass.coe_zero]
        have := LinearMap.congr_fun hg x
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        rw [this, sub_self]
      rw [this, map_zero]
    rw [this, map_zero]
  · rw [← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ kL = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mL]
      have : ψ (kL y) = b.equivFun.symm y := by
        apply Subtype.ext
        have hk : g (kL y) = 0 := (b.equivFun.symm y).2
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, hk, map_zero, sub_zero]
        rfl
      rw [this]
      exact b.equivFun.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id]
  · rw [hJ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_add,
      ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, mL, kL]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, ψ,
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' : ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))), Module.finrank E Y = r → ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E), Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y → ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose → (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) → ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E) (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E), C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧ J * L + K * M = 1 := by
  atlas_forward_decl GlobalTheory.exists_adapted_frame_of_isotropic_columns
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.CoordUnfold

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem integral_fundamentalDomain_eq_iterated_split : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  intro D r m s t J K L M hLJ hLK hMJ hMK hJLKM μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.MixModel.lattice_Mx D s m
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := GlobalTheory.MixModel.lattice_Mx D t m
  obtain ⟨l1, l2, l3, l4, l5, KK, hKK, hKKc⟩ := GlobalTheory.MixModel.lattice_Mx D r m
  haveI : BorelSpace (Mx D s m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D t m) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r m) := ⟨rfl⟩
  haveI : Countable (GlobalTheory.MixModel.ratMx D s m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D t m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable (GlobalTheory.MixModel.ratMx D r m) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ.1
  haveI := hν.1
  haveI := hη.1
  haveI : IsFiniteMeasure (ν.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hν.2.2]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (η.restrict 𝓥) := ⟨by rw [Measure.restrict_apply_univ, hη.2.2]; exact ENNReal.one_lt_top⟩
  set rJ : Mx D r s := J.map (incA D) with hrJ
  set rK : Mx D r t := K.map (incA D) with hrK
  set rL : Mx D s r := L.map (incA D) with hrL
  set rM : Mx D t r := M.map (incA D) with hrM
  have hLJ' : rL * rJ = 1 := by rw [hrL, hrJ, ← Matrix.map_mul, hLJ]; exact GlobalTheory.MixModel.rat_one
  have hLK' : rL * rK = 0 := by rw [hrL, hrK, ← Matrix.map_mul, hLK]; exact GlobalTheory.MixModel.rat_zero
  have hMJ' : rM * rJ = 0 := by rw [hrM, hrJ, ← Matrix.map_mul, hMJ]; exact GlobalTheory.MixModel.rat_zero
  have hMK' : rM * rK = 1 := by rw [hrM, hrK, ← Matrix.map_mul, hMK]; exact GlobalTheory.MixModel.rat_one
  have hJLKM' : rJ * rL + rK * rM = 1 := by
    rw [hrJ, hrL, hrK, hrM, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add, hJLKM]
    · exact GlobalTheory.MixModel.rat_one
    · exact fun a b => map_add (incA D) a b
  let Ec : (Mx D t m × Mx D s m) ≃ₜ+ Mx D r m :=
    { toFun := fun p => rJ * p.2 + rK * p.1
      invFun := fun u => (rM * u, rL * u)
      left_inv := by
        rintro ⟨v, y⟩
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', hMJ', hMK', Matrix.one_mul, Matrix.zero_mul,
          add_zero, zero_add]
      right_inv := by
        intro u
        show rJ * (rL * u) + rK * (rM * u) = u
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.add_mul, hJLKM', Matrix.one_mul]
      map_add' := by
        rintro ⟨v, y⟩ ⟨v', y'⟩
        simp only [Prod.mk_add_mk, Matrix.mul_add]
        abel
      continuous_toFun := ((continuous_const.matrix_mul continuous_snd).add (continuous_const.matrix_mul continuous_fst))
      continuous_invFun := (continuous_const.matrix_mul continuous_id).prodMk (continuous_const.matrix_mul continuous_id) }
  have hEapp : ∀ v y, Ec (v, y) = rJ * y + rK * v := fun _ _ => rfl
  let Me : (Mx D t m × Mx D s m) ≃ᵐ Mx D r m := Ec.toHomeomorph.toMeasurableEquiv
  have hMe : ∀ p, Me p = Ec p := fun _ => rfl
  set lam : Measure (Mx D t m × Mx D s m) := η.prod ν with hlam
  haveI : lam.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set mm : Measure (Mx D r m) := lam.map Me with hm
  haveI : mm.IsAddHaarMeasure := Ec.isAddHaarMeasure_map lam
  have hμm := Measure.isAddLeftInvariant_eq_smul μ mm
  set c := Measure.addHaarScalarFactor μ mm with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ mm
  set Γ : AddSubgroup (Mx D t m × Mx D s m) :=
    (GlobalTheory.MixModel.ratMx D t m).prod (GlobalTheory.MixModel.ratMx D s m) with hΓ
  have hmemΓ : ∀ p, p ∈ Γ ↔ Ec p ∈ GlobalTheory.MixModel.ratMx D r m := by
    rintro ⟨v, y⟩
    rw [hEapp]
    simp only [Γ, AddSubgroup.mem_prod]
    constructor
    · rintro ⟨hv, hy⟩
      exact add_mem (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem J) hy)
        (GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem K) hv)
    · intro h
      have h1 : rM * (rJ * y + rK * v) = v := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hMJ', hMK', Matrix.one_mul, Matrix.zero_mul, zero_add]
      have h2 : rL * (rJ * y + rK * v) = y := by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, hLJ', hLK', Matrix.one_mul, Matrix.zero_mul, add_zero]
      refine ⟨?_, ?_⟩
      · rw [← h1]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem M) h
      · rw [← h2]; exact GlobalTheory.MixModel.ratMx_mul (GlobalTheory.MixModel.rat_mem L) h
  have hFDP : IsAddFundamentalDomain Γ (𝓥 ×ˢ 𝓨) lam := isAddFundamentalDomain_prod hη.2.1 hν.2.1
  have hac : lam.map Me ≪ μ := by
    intro A hA
    rw [hμm, Measure.smul_apply] at hA
    exact (smul_eq_zero.1 hA).resolve_left hc.ne'
  have hqmp : Measure.QuasiMeasurePreserving Me lam μ := ⟨Me.measurable, hac⟩
  let eΓ : GlobalTheory.MixModel.ratMx D r m → Γ := fun g => ⟨Ec.symm g, (hmemΓ _).2 (by simpa using g.2)⟩
  have heΓ : Function.Bijective eΓ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun p => ⟨⟨Ec p, (hmemΓ p).1 p.2⟩, Subtype.ext ?_⟩⟩
    · have := congrArg (fun q : Γ => Ec q.1) h
      simpa [eΓ] using this
    · simp [eΓ]
  haveI : Countable Γ := heΓ.2.countable
  have hFDE : IsAddFundamentalDomain Γ (Me ⁻¹' 𝓕) lam :=
    hμ.2.1.preimage_of_equiv hqmp heΓ (fun g p => by
      show Me ((Ec.symm g : _) + p) = (g : Mx D r m) + Me p
      rw [hMe, hMe, map_add, Ec.apply_symm_apply])
  refine ⟨(c : ℝ), fun T hT hper => ?_⟩
  obtain ⟨C, hC⟩ := hKK.exists_bound_of_continuousOn hT.continuousOn
  have hbd : ∀ x, ‖T x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hx⟩ := hKKc x
    rw [← hper γ hγ x]
    exact hC _ hx
  have hTE : Continuous fun p => T (Me p) := hT.comp Ec.continuous
  have e1 : ∫ u in 𝓕, T u ∂μ = (c : ℝ) • ∫ u in 𝓕, T u ∂mm := by
    rw [hμm, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def]
  have e2 : ∫ u in 𝓕, T u ∂mm = ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam := setIntegral_map_equiv Me T 𝓕
  have e3 : ∫ p in Me ⁻¹' 𝓕, T (Me p) ∂lam = ∫ p in 𝓥 ×ˢ 𝓨, T (Me p) ∂lam :=
    hFDE.setIntegral_eq hFDP (fun g p => by
      show T (Me ((g : _) + p)) = T (Me p)
      rw [hMe, hMe, map_add]
      exact hper _ ((hmemΓ _).1 g.2) _)
  have e4 : lam.restrict (𝓥 ×ˢ 𝓨) = (η.restrict 𝓥).prod (ν.restrict 𝓨) := by
    rw [Measure.prod_restrict]
  rw [e1, e2, e3, e4, integral_prod _ (Integrable.of_bound hTE.aestronglyMeasurable C (ae_of_all _ fun p => hbd _)),
    Complex.real_smul]
  rfl

end GlobalTheory.CoordUnfold

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting : ∀ (D : D7) (r m s t : ℕ) (J : Matrix (Fin r) (Fin s) D.host.E) (K : Matrix (Fin r) (Fin t) D.host.E) (L : Matrix (Fin s) (Fin r) D.host.E) (M : Matrix (Fin t) (Fin r) D.host.E), L * J = 1 → L * K = 0 → M * J = 0 → M * K = 1 → J * L + K * M = 1 → ∀ (μ : Measure (Mx D r m)) (𝓕 : Set (Mx D r m)), IsCovolOne (GlobalTheory.MixModel.ratMx D r m) μ 𝓕 → ∀ (ν : Measure (Mx D s m)) (𝓨 : Set (Mx D s m)), IsCovolOne (GlobalTheory.MixModel.ratMx D s m) ν 𝓨 → ∀ (η : Measure (Mx D t m)) (𝓥 : Set (Mx D t m)), IsCovolOne (GlobalTheory.MixModel.ratMx D t m) η 𝓥 → ∃ κ : ℝ, ∀ T : Mx D r m → ℂ, Continuous T → (∀ γ ∈ GlobalTheory.MixModel.ratMx D r m, ∀ u, T (γ + u) = T u) → ∫ u in 𝓕, T u ∂μ = κ * ∫ v in 𝓥, (∫ y in 𝓨, T (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) ∂ν) ∂η := by
  atlas_forward_decl GlobalTheory.CoordUnfold.integral_fundamentalDomain_eq_iterated_split
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section
namespace GlobalTheory.LagMeans

set_option maxHeartbeats 400000 in

theorem lagTerm_eq_of_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  intro D ψ hψ V W μ 𝓕 hμ Y C hC s I hI hspan ν 𝓨 hν f₁ f₁' f₂ h₁ h₁' h₂ hmean
  have hmem : ∀ j, ((fun a => I a j), (0 : Fin W.rank → D.host.E)) ∈ Y.1 := fun j => by
    have : (fun a => I a j) ∈ Y.1.comap (LinearMap.inl D.host.E _ _) := hspan ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  have mcol : ∀ k, ((fun a => C.1 a k), (fun a => C.2 a k)) ∈ Y.1 := fun k => hC ▸ Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨t, J, K, L, M, e1, e2, e3, e4, e5, e6, e7⟩ := GlobalTheory.T.exists_adapted_frame_of_isotropic_columns' D.host.E W.rank Y.1 Y.2.1 C hC s I hI.2.1 hmem
  obtain ⟨η, 𝓥, hη⟩ := GlobalTheory.MixModel.exists_isCovolOne D t V.rank
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_iterated_rationalSplitting D W.rank V.rank s t J K L M e3 e4 e5 e6 e7 μ 𝓕 hμ ν 𝓨 hν η 𝓥 hη
  have hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram * C.1 = 0 := by
    rw [Matrix.mul_assoc]
    funext j k
    have := Y.2.2 _ (hmem j) _ (mcol k)
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero] at this
    simpa only [Matrix.mul_apply, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_apply, Matrix.zero_apply] using this
  have hψ' : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have per : ∀ f, IsThetaFunO ψ V W f → ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank V.rank, ∀ u : Mx D W.rank V.rank,
      f (ratMul C.1 (γ + u)) * star (f₂ (ratMul C.2 (γ + u))) = f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) := by
    rintro f hf _ ⟨γ, rfl⟩ u
    exact GlobalTheory.RawLift.Model.integrand_periodic hψ' hC hf h₂ γ u
  have cont : ∀ f, IsThetaFunO ψ V W f → Continuous fun u : Mx D W.rank V.rank => f (ratMul C.1 u) * star (f₂ (ratMul C.2 u)) :=
    fun f hf => (hf.cont.comp (continuous_const.matrix_mul continuous_id)).mul
      (continuous_star.comp (h₂.cont.comp (continuous_const.matrix_mul continuous_id)))
  unfold lagTerm
  rw [hκ _ (cont f₁ h₁) (per f₁ h₁), hκ _ (cont f₁' h₁') (per f₁' h₁')]
  congr 1
  congr 1
  funext v
  have r1 : ∀ y : Mx D s V.rank, ratMul C.1 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul (I.map (incA D)) y + HMul.hMul ((C.1 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e1]
  have r2 : ∀ y : Mx D s V.rank, ratMul C.2 (HMul.hMul (J.map (incA D)) y + HMul.hMul (K.map (incA D)) v) =
      HMul.hMul ((C.2 * K).map (incA D)) v := fun y => by
    unfold ratMul
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul, e2,
      Matrix.map_zero (incA D) (map_zero (incA D))]
    simp only [Matrix.zero_mul, zero_add]
  simp only [r1, r2]
  rw [integral_mul_const, integral_mul_const]
  congr 1
  refine hmean _ ?_
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mul_assoc, hB, Matrix.zero_mul, Matrix.map_zero (incA D) (map_zero (incA D))]
  exact Matrix.zero_mul _

end GlobalTheory.LagMeans
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ (Y : Lag W) (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), IsLagFrame W Y C → ∀ (s : ℕ) (I : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W I → Submodule.span D.host.E (Set.range I.transpose) = Y.1.comap (LinearMap.inl D.host.E _ _) → ∀ (ν : Measure (Mx D s V.rank)) (𝓨 : Set (Mx D s V.rank)), IsCovolOne (GlobalTheory.MixModel.ratMx D s V.rank) ν 𝓨 → ∀ f₁ f₁' f₂ : WO V W → ℂ, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₁' → IsThetaFunO ψ V W f₂ → (∀ x : WO V W, HMul.hMul ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) I * W.gram).map (incA D)) x = (0 : Mx D s V.rank) → ∫ y in 𝓨, f₁ (HMul.hMul (I.map (incA D)) y + x) ∂ν = ∫ y in 𝓨, f₁' (HMul.hMul (I.map (incA D)) y + x) ∂ν) → lagTerm μ 𝓕 C f₁ f₂ = lagTerm μ 𝓕 C f₁' f₂ := by
  atlas_forward_decl GlobalTheory.LagMeans.lagTerm_eq_of_means
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TermInvProof

theorem termInv : ∀ D : D7, TermInv D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y s I hI hY n hn f₁ f₂ hf₁ hf₂
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne (D := D) (m := s) (n := V.rank)
  exact GlobalTheory.T.doubledLagrangian_term_depends_only_on_isotropic_means D ψ hS.weil.std V W μ 𝓕 hS.covol Y (fr Y) (hS.frame Y) s I hI hY ν 𝓨 hν _ _ f₂
    (hS.weil.om_pres _ f₁ hf₁) hf₁ hf₂
    (fun x hx => GlobalTheory.T.thetaFun_isotropic_mean_unipotent_invariant D ψ V W χV χW om hS.weil s I hI ν 𝓨 hν n hn f₁ hf₁ x hx)

end GlobalTheory.TermInvProof

end
end
