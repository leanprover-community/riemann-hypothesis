import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.SumKfMulZREqZero

section
noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW.NRatW

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem ratN_of_AF (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (h : HAd X.B.I)
    (hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
      γ.map (inclR (AF X.B.I.F)))
    (hN : h ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :
    RatN X.eR (Kf X X.eR) γ := by
  obtain ⟨h1, h2⟩ := hN
  have hlin : ∀ x : Fin X.B.I.n → X.B.I.E,
      lin (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h (ratV (F := X.B.I.F) (AF X.B.I.F) x) -
        ratV (F := X.B.I.F) (AF X.B.I.F) x = fun i => inclR (AF X.B.I.F) (((γ - 1) *ᵥ x) i) := by
    intro x
    rw [← map_sub_one_mulVec (inclR (AF X.B.I.F)) γ x]
    simp only [lin, Matrix.mulVecLin_apply, hM, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  refine ⟨fun a => ?_, fun y hy => ?_⟩
  · have := h1 a
    rw [hlin] at this
    exact down_span (inclR (AF X.B.I.F)) (inclR_injective X) X.eR (Kf X X.fR) (hK_e X u) _ _ this
  · have hperp : InXperp (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) (ratV (F := X.B.I.F) (AF X.B.I.F) y) := by
      intro a
      rw [hR_ratV_left]
      have h' := congrArg (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) (hy a)
      simp only [Kf, map_sum, map_mul, map_zero] at h'
      simp only [ratV, map_sum, map_mul]
      exact h'
    have := h2 _ hperp
    rw [hlin] at this
    have h3 := down_span (inclR (AF X.B.I.F)) (inclR_injective X) X.eR (Kf X X.fR) (hK_e X u) Set.univ _ this
    rwa [Set.image_univ] at h3

theorem ratN_of_fin (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (x : X.B.I.Gf)
    (hx : X.B.I.fmat x = γ.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) (hN : x ∈ X.NfinU u) :
    RatN X.eR (Kf X X.eR) γ := by
  simp only [HidaSetting.NfinU, Nfin, Set.mem_ofPred_eq] at hN
  obtain ⟨h1, -, h3⟩ := hN
  have hlin : ∀ y : Fin X.B.I.n → X.B.I.E, (X.B.I.fmat x - 1) *ᵥ incl X.B.I y =
      fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ - 1) *ᵥ y) i) := by
    intro y
    rw [hx]
    exact map_sub_one_mulVec _ γ y
  refine ⟨fun a => ?_, fun y hy => ?_⟩
  · have := h1 a
    rw [hlin] at this
    exact down_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (inclE_injective X) X.eR (Kf X X.fR) (hK_e X u)
      {b | b < a} _ this
  · have hperp : ∀ a, hA X.B.I (incl X.B.I (X.eR a)) (incl X.B.I y) = 0 := by
      intro a
      rw [hA_incl_left]
      have h' := congrArg (Formalism.UG.inclE (F := X.B.I.F) (E := X.B.I.E) (Af X.B.I.F)) (hy a)
      simp only [Kf, map_sum, map_mul, map_zero] at h'
      simpa only [incl, map_sum, map_mul] using h'
    have := h3 _ hperp
    rw [hlin, ← Set.image_univ] at this
    have h4 := down_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) (inclE_injective X) X.eR (Kf X X.fR)
      (hK_e X u) Set.univ _ this
    rwa [Set.image_univ] at h4

theorem nfin_of_ratN (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (x : X.B.I.Gf)
    (hx : X.B.I.fmat x = γ.map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) (hR : RatN X.eR (Kf X X.eR) γ) :
    x ∈ X.NfinU u := by
  simp only [HidaSetting.NfinU, Nfin, Set.mem_ofPred_eq]
  have hlin : ∀ y : Fin X.B.I.n → X.B.I.E, (X.B.I.fmat x - 1) *ᵥ incl X.B.I y =
      fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (((γ - 1) *ᵥ y) i) := by
    intro y
    rw [hx]
    exact map_sub_one_mulVec _ γ y
  refine ⟨fun a => ?_, ?_, fun y hy => ?_⟩
  · rw [hlin]
    exact up_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) X.eR {b | b < a} (hR.1 a)
  · rw [hlin]
    have := up_span (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) X.eR Set.univ (w := (γ - 1) *ᵥ X.zR u)
      (by rw [Set.image_univ]; exact hR.2 _ (sum_Kf_mul_zR_eq_zero X u))
    rwa [Set.image_univ] at this
  · rw [hx]
    exact perp_up (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) γ X.eR X.fR (Kf X X.eR) (hKf_f X u) hR.2 y
      (fun a => by have := hy a; rw [hA_incl_left] at this; exact this)

theorem hJ_rv (v : InfinitePlace X.B.I.F) (x : Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε v) (rv X.B.I v x) y =
      ∑ j, X.B.I.φ v (∑ i, star (x i) * X.B.I.J i j) * (X.B.I.P v *ᵥ y) j := by
  have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hPP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hst : ∀ a : X.B.I.E, star (X.B.I.φ v a) = X.B.I.φ v (star a) := by
    intro a
    rw [X.B.I.cm.cmUnram.2.1]
    rfl
  unfold hJ rv
  rw [← X.B.I.P_spec v, Matrix.star_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.conjTranspose_mul, hPP, Matrix.conjTranspose_one,
    Matrix.vecMul_one]
  set w := X.B.I.P v *ᵥ y
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply, hst, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring

theorem ninf_of_ratN (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (s : X.B.I.Ginf)
    (hs : ∀ v, Formalism.MainNotions.S.uMat (s v) = (X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v) (hR : RatN X.eR (Kf X X.eR) γ) :
    s ∈ X.NinfU u := by
  simp only [HidaSetting.NinfU, Ninf, Set.mem_ofPred_eq]
  intro v
  rw [hs v]
  have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hPP : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hPP' : (X.B.I.P v)⁻¹ * X.B.I.P v = 1 := Matrix.nonsing_inv_mul _ hdet
  have key1 : ∀ y : Fin X.B.I.n → ℂ, ((X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v - 1) *ᵥ y =
      (X.B.I.P v)⁻¹ *ᵥ ((γ.map (X.B.I.φ v) - 1) *ᵥ (X.B.I.P v *ᵥ y)) := by
    intro y
    have hmat : (X.B.I.P v)⁻¹ * (γ.map (X.B.I.φ v) - 1) * X.B.I.P v =
        (X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v - 1 := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hPP']
    conv_rhs => rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat]
  have key2 : ∀ x : Fin X.B.I.n → ℂ, ((X.B.I.P v)⁻¹ * γ.map (X.B.I.φ v) * X.B.I.P v - 1) *ᵥ ((X.B.I.P v)⁻¹ *ᵥ x) =
      (X.B.I.P v)⁻¹ *ᵥ ((γ.map (X.B.I.φ v) - 1) *ᵥ x) := by
    intro x
    have hx : X.B.I.P v *ᵥ ((X.B.I.P v)⁻¹ *ᵥ x) = x := by rw [Matrix.mulVec_mulVec, hPP, Matrix.one_mulVec]
    rw [key1, hx]
  have spanP : ∀ (t : Set (Fin D.R.rS)) (w : Fin X.B.I.n → ℂ),
      w ∈ Submodule.span ℂ ((fun b i => X.B.I.φ v (X.eR b i)) '' t) →
      (X.B.I.P v)⁻¹ *ᵥ w ∈ Submodule.span ℂ ((fun b => rv X.B.I v (X.eR b)) '' t) := by
    intro t w hw
    have := Submodule.apply_mem_span_image_of_mem_span (Matrix.mulVecLin (X.B.I.P v)⁻¹) hw
    rw [Set.image_image] at this
    exact this
  have hu : {b : Fin D.R.rS | b.1 < D.R.rS} = Set.univ := Set.eq_univ_of_forall fun b => b.2
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · show _ *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (X.eR a i)) ∈ _
    rw [key2, map_sub_one_mulVec]
    exact spanP _ _ (up_span (X.B.I.φ v) X.eR _ (hR.1 a))
  · show _ *ᵥ ((X.B.I.P v)⁻¹ *ᵥ fun i => X.B.I.φ v (X.zR u i)) ∈ _
    rw [key2, map_sub_one_mulVec]
    have h := up_span (X.B.I.φ v) X.eR Set.univ (w := (γ - 1) *ᵥ X.zR u)
      (by rw [Set.image_univ]; exact hR.2 _ (sum_Kf_mul_zR_eq_zero X u))
    unfold spanLt
    rw [hu]
    exact spanP _ _ h
  · rw [key1]
    have h := perp_up (X.B.I.φ v) γ X.eR X.fR (Kf X X.eR) (hKf_f X u) hR.2 (X.B.I.P v *ᵥ y)
      (fun a => by have := hy a; rw [hJ_rv] at this; exact this)
    rw [← Set.image_univ] at h
    unfold spanLt
    rw [hu]
    exact spanP _ _ h

theorem nsub_of_ratN (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (h : HAd X.B.I)
    (hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h : GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
      Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
      γ.map (inclR (AF X.B.I.F)))
    (hR : RatN X.eR (Kf X X.eR) γ) :
    h ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) := by
  have hlin : ∀ y, lin (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h y - y = (γ.map (inclR (AF X.B.I.F)) - 1) *ᵥ y := by
    intro y
    simp only [lin, Matrix.mulVecLin_apply, hM, Matrix.sub_mulVec, Matrix.one_mulVec]
  show _ ∧ _
  refine ⟨fun a => ?_, fun y hy => ?_⟩
  · rw [hlin]
    have := up_span (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) X.eR {b | b < a} (hR.1 a)
    have e : (γ.map (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) - 1) *ᵥ
        ratV (F := X.B.I.F) (AF X.B.I.F) ((frameOf X u).e a) =
        fun i => inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F) (((γ - 1) *ᵥ X.eR a) i) :=
      map_sub_one_mulVec _ γ (X.eR a)
    rw [e]
    exact this
  · rw [hlin]
    have := perp_up (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) γ X.eR X.fR (Kf X X.eR) (hKf_f X u) hR.2 y
      (fun a => by have := hy a; rw [hR_ratV_left] at this; exact this)
    rw [← Set.image_univ] at this
    exact this

end MassDataMassesW.NRatW
end
end

section
noncomputable section

open scoped TensorProduct
open Matrix NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

namespace MassDataMassesW

def NRatBridge : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (δ : X.B.I.GA),
    (toHA X.B.I hb δ ∈ (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J :
        Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      toHA X.B.I hb δ ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) ↔
    (δ ∈ X.B.I.GFset ∧ δ.1 ∈ X.NinfU u ∧ δ.2 ∈ X.NfinU u)

open NRatW in
theorem nRatBridge_holds : NRatBridge := by
  intro D X hb u δ
  obtain ⟨hinfB, hfinB⟩ := toHA_isBridge X.B.I hb δ
  constructor
  · rintro ⟨hF, hN⟩
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hF)
    have hmat : HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ) =
        Formalism.UG.bc (inclR (AF X.B.I.F)) γ := hγe.symm
    have hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ) :
        GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F)) := by
      rw [hmat]; rfl
    have hRat := ratN_of_AF X u _ _ hM hN
    have hinf : ∀ v, Formalism.MainNotions.S.uMat (δ.1 v) =
        (X.B.I.P v)⁻¹ * (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) * X.B.I.P v :=
      fun v => (hinfB v).trans (ofHAInf_rat X.B.I _ γ hmat v)
    have hfin : X.B.I.fmat δ.2 =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) :=
      hfinB.trans (ofHAFin_rat X.B.I _ γ hmat)
    exact ⟨⟨γ, hγ, hinf, hfin⟩, ninf_of_ratN X u _ δ.1 hinf hRat, nfin_of_ratN X u _ δ.2 hfin hRat⟩
  · rintro ⟨⟨γ, hγ, hinf, hfin⟩, -, hNf⟩
    have hRat := ratN_of_fin X u _ δ.2 hfin hNf
    have hU : Formalism.UG.bc (inclR (F := X.B.I.F) (E := X.B.I.E) (AF X.B.I.F)) γ ∈
        HR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J := by
      have hγ' : Formalism.UG.cT (starRingEnd X.B.I.E) (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * X.B.I.J *
          (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := hγ
      have e1 : Formalism.UG.cT (sigR (AF X.B.I.F) X.B.I.cm.sig)
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) =
          (Formalism.UG.cT (starRingEnd X.B.I.E) (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)).map
            (inclR (AF X.B.I.F)) := by
        ext i j
        simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]
        rfl
      show Formalism.UG.cT (sigR (AF X.B.I.F) X.B.I.cm.sig)
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) * JR (AF X.B.I.F) X.B.I.J *
          ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F))) = JR (AF X.B.I.F) X.B.I.J
      rw [e1, JR, ← Matrix.map_mul, ← Matrix.map_mul, hγ']
    obtain ⟨h, hmat⟩ : ∃ h : HAd X.B.I, HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h =
        Formalism.UG.bc (inclR (AF X.B.I.F)) γ :=
      ⟨(⟨_, hU⟩ : HR (AF X.B.I.F) X.B.I.cm.sig X.B.I.J), rfl⟩
    have hq : (toHA X.B.I hb).symm h = δ := by
      obtain ⟨a1, a2⟩ := toHA_isBridge X.B.I hb ((toHA X.B.I hb).symm h)
      rw [ContinuousMulEquiv.apply_symm_apply] at a1 a2
      refine Prod.ext (funext fun v => ?_) ?_
      · exact Subtype.ext (Units.ext ((a1 v).trans ((ofHAInf_rat X.B.I h γ hmat v).trans (hinf v).symm)))
      · exact Subtype.ext (Units.ext (a2.trans ((ofHAFin_rat X.B.I h γ hmat).trans hfin.symm)))
    have hδ : toHA X.B.I hb δ = h := by
      rw [← hq]
      exact (toHA X.B.I hb).apply_symm_apply h
    rw [hδ]
    refine ⟨Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ, hγ, hmat.symm⟩), ?_⟩
    have hM : ((HA.mat (AF X.B.I.F) X.B.I.cm.sig X.B.I.J h :
        GL (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) :
          Matrix (Fin X.B.I.n) (Fin X.B.I.n) (AF X.B.I.F ⊗[X.B.I.F] X.B.I.E)) =
        (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (inclR (AF X.B.I.F)) := by
      rw [hmat]; rfl
    exact nsub_of_ratN X u _ h hM hRat

end MassDataMassesW
end
end

section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

section Level

variable {D : D7} (X : HidaSetting D)

theorem kset_mul {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset) : x * y ∈ X.B.I.Kset :=
  (Formalism.UG.stabGL X.B.I.Lf).mul_mem hx hy

theorem kset_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : x⁻¹ ∈ X.B.I.Kset :=
  (Formalism.UG.stabGL X.B.I.Lf).inv_mem hx

theorem gf_eq_one (hb : AdBridgeIso X.B.I) (δ : X.B.I.GA) (hδ : δ ∈ X.B.I.GFset) (h1 : δ.1 = 1) : δ = 1 := by
  obtain ⟨g, -, hinf, hfin⟩ := hδ
  obtain v := (inferInstance : Nonempty (InfinitePlace X.B.I.F)).some
  have hdet : IsUnit (X.B.I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit v)
  have hP' : X.B.I.P v * (X.B.I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hv := hinf v
  rw [h1] at hv
  have hone : Formalism.MainNotions.S.uMat ((1 : X.B.I.Ginf) v) = 1 := rfl
  rw [hone] at hv
  have hM : (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) = 1 := by
    calc (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v)
        = X.B.I.P v * ((X.B.I.P v)⁻¹ * (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *
            X.B.I.P v) * (X.B.I.P v)⁻¹ := by
          simp only [Matrix.mul_assoc, hP', Matrix.mul_one]
          rw [← Matrix.mul_assoc, hP', Matrix.one_mul]
      _ = 1 := by rw [← hv, Matrix.mul_one, hP']
  have hg : (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1 := by
    ext i j
    have := congrFun (congrFun hM i) j
    rw [Matrix.map_apply, Matrix.one_apply] at this
    rw [Matrix.one_apply]
    apply (X.B.I.φ v).injective
    rw [this]
    split_ifs <;> simp
  refine Prod.ext h1 ?_
  apply Subtype.ext
  apply Units.ext
  show X.B.I.fmat δ.2 = 1
  rw [hfin, hg]
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  split_ifs <;> simp

end Level

theorem fundamental_domain_of_compact_open (hKo : KCompactOpen) (hRB : NRatBridge) : UnipotentFundamentalDomain := by
  intro hSA hNL hBK hS D X hb hK u FdN hTie hL hF
  have : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  have : BorelSpace (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩

  have core : ∀ γ : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      γ ∈ (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) →
      γ ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) →
      ∀ (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) (s s' : X.B.I.Ginf), s ∈ FdN → s' ∈ FdN →
      (splitA X.B.I.cm.sig X.B.I.J n).1 = X.toInf hb s → (splitA X.B.I.cm.sig X.B.I.J n).2 ∈ KX X →
      (splitA X.B.I.cm.sig X.B.I.J (γ * n)).1 = X.toInf hb s' →
      (splitA X.B.I.cm.sig X.B.I.J (γ * n)).2 ∈ KX X → γ = 1 := by
    intro γ hγF hγN n s s' hs hs' h1 h2 h1' h2'
    set δ := (toHA X.B.I hb).symm γ with hδdef
    have hδ : toHA X.B.I hb δ = γ := (toHA X.B.I hb).apply_symm_apply γ
    obtain ⟨hGF, hinf, hfin⟩ := (hRB X hb u δ).1 ⟨by rw [hδ]; exact hγF, by rw [hδ]; exact hγN⟩
    have hsp : splitA X.B.I.cm.sig X.B.I.J γ = (X.toInf hb δ.1, finHA X hb δ.2) := by
      rw [← hδ]
      exact split_toHA X hb hS δ
    have hmul : splitA X.B.I.cm.sig X.B.I.J (γ * n) =
        splitA X.B.I.cm.sig X.B.I.J γ * splitA X.B.I.cm.sig X.B.I.J n := map_mul _ _ _
    rw [hsp] at hmul
    have hfinK : finHA X hb δ.2 ∈ KX X := by
      have e2 : finHA X hb δ.2 = (splitA X.B.I.cm.sig X.B.I.J (γ * n)).2 *
          ((splitA X.B.I.cm.sig X.B.I.J n).2)⁻¹ := by
        rw [hmul]
        simp
      rw [e2]
      exact (KX X).mul_mem h2' ((KX X).inv_mem h2)
    have hKs : δ.2 ∈ X.B.I.Kset := (hBK X hb δ.2).2 hfinK
    have hK2 := hNL X u δ.2 hfin hKs
    have hNO : δ.1 ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u := ⟨δ, hGF, rfl, hinf, hfin, hK2⟩
    have hreal : X.toInf hb s' = X.toInf hb (δ.1 * s) := by
      rw [toInf_mul, ← h1', hmul, ← h1]
      rfl
    have hs'' : s' = δ.1 * s := toInf_injective X hb hS hreal
    have hδ1 : δ.1 = 1 := hF.2.2 s hs δ.1 hNO (hs'' ▸ hs')
    have hδ1' : δ = 1 := gf_eq_one X hb δ hGF hδ1
    rw [← hδ, hδ1', map_one]

  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  have hm : Measurable (splitA X.B.I.cm.sig X.B.I.J) :=
    (continuous_fst.comp hc).measurable.prodMk (continuous_snd.comp hc).measurable
  have hTm : MeasurableSet (X.toInf hb '' FdN) := measurableSet_image_toInf X hb hS hF.1
  have hKm : MeasurableSet (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := (hKo X).2.measurableSet
  have hRm : MeasurableSet ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hTm.prod hKm
  have hFd : FdA X hb u FdN = Subtype.val ⁻¹' (splitA X.B.I.cm.sig X.B.I.J ⁻¹'
      ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))) := by
    ext n
    simp only [FdA, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_prod, Set.mem_image]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨⟨s, hs, h1.symm⟩, h2⟩
    · rintro ⟨⟨s, hs, h1⟩, h2⟩
      exact ⟨s, hs, h1.symm, h2⟩
  have hmeas : MeasurableSet (FdA X hb u FdN) := by
    rw [hFd]
    exact measurable_subtype_coe (hm hRm)

  have cover : ∀ n : ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      ∃ g : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)), g • n ∈ FdA X hb u FdN := by
    intro n
    obtain ⟨γ, hγF, hγN, hγK⟩ := hSA X u n n.2
    obtain ⟨t, ht⟩ := toInf_surjective X hb hS (splitA X.B.I.cm.sig X.B.I.J (γ * n)).1
    obtain ⟨s, hsNO, hst⟩ := hF.2.1 t
    obtain ⟨δ, hGF, hδs, hinf, hfin, hK2⟩ := hsNO
    obtain ⟨hγ'F, hγ'N⟩ := (hRB X hb u δ).2 ⟨hGF, hinf, hfin⟩
    have hKs : δ.2 ∈ X.B.I.Kset := by
      have hx := X.xu_K u
      have h2 := hL.2.1 _ hK2
      have : δ.2 = X.xu u * ((X.xu u)⁻¹ * δ.2 * X.xu u) * (X.xu u)⁻¹ := by group
      rw [this]
      exact kset_mul X (kset_mul X hx h2) (kset_inv X hx)
    have hfinK : finHA X hb δ.2 ∈ KX X := (hBK X hb δ.2).1 hKs
    refine ⟨⟨⟨toHA X.B.I hb δ * γ, (Nsub _ _ _ _).mul_mem hγ'N hγN⟩,
      Subgroup.mem_comap.2 (Subgroup.mul_mem _ hγ'F hγF)⟩, ?_⟩
    have hsp : splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ * γ * (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
        (X.toInf hb δ.1, finHA X hb δ.2) * splitA X.B.I.cm.sig X.B.I.J (γ * n) := by
      rw [mul_assoc, map_mul, split_toHA X hb hS δ]
    refine ⟨s * t, hst, ?_, ?_⟩
    · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ * γ * (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J))).1 = _
      rw [hsp, toInf_mul, Prod.fst_mul, ← ht, hδs]
    · show (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb δ * γ * (n : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J))).2 ∈ _
      rw [hsp, Prod.snd_mul]
      exact (KX X).mul_mem hfinK hγK
  refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet fun n => ?_
  obtain ⟨g0, hg0⟩ := cover n
  refine ⟨g0, hg0, fun g hg => ?_⟩

  obtain ⟨s, hs, h1, h2⟩ := hg0
  obtain ⟨s', hs', h1', h2'⟩ := hg
  have hγF : (((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) ∈
      (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    Subgroup.mem_comap.1 (g * g0⁻¹).2
  have hγN := ((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))).2
  have hgn0 : ((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) * (g0 • n) = g • n := by
    rw [Subgroup.smul_def, Subgroup.smul_def, smul_eq_mul, smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      mul_assoc, inv_mul_cancel_left]
  have hgn : (((g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) *
      ((g0 • n : ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) =
      ((g • n : ↥(Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    congrArg Subtype.val hgn0
  have h1g : (g * g0⁻¹ : ratOf (K := Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) = 1 := by
    have := core _ hγF hγN _ s s' hs hs' h1 h2 (by rw [hgn]; exact h1') (by rw [hgn]; exact h2')
    exact Subtype.ext (Subtype.ext this)
  exact mul_inv_eq_one.1 h1g

end MassDataMassesW
end
end
