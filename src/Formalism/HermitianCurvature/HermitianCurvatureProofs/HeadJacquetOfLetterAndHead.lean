import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJ
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WordInd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpFromBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem kapJ_eq (P : M.Par) (j : ℕ) : kapJ P j = levelZeroKernel P.k P.r j := rfl

theorem headJ_of (hW : WordInd) (hB : HeadBridge) : HeadJ := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  obtain ⟨X, _, μ, ℓ, Zx, Fx, Dm, φx, hDm, hDmsub, hR, hZ, hφx, hL, hRt⟩ :=
    hB Wp Wq P p F j hj w h hh γ hF hw hγ hγ' φ hφ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (by simp)).2
  rw [hL, hRt]
  congr 1
  funext x
  rw [hW P.k P.r j hj _ _ (Wq →L[ℂ] Wp) Dm (Fx x) p.T.base.z_mem p.T.base.z'_mem hDm hDmsub (hR x) (Zx x) γ
    (hZ x).1 hγ (hZ x).2 w (φx x) (hφx x) t ht0 e, kapJ_eq]

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBP

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem act_one_variable_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Type} [Fintype S] [DecidableEq S]
    (M : Wd.SlopeTestRemainingChoices S (Pr (V1 E))) (s : ℂ) (x : Wd.Ix S → V1 E) :
    act1 M (fun b => s • x b) = fun e => s • act1 M x e := by
  funext e
  simp only [act1, map_smul, Finset.smul_sum]

theorem kapM_eq (P : M.Par) (j : ℕ) : kapM (P.r - j) P.k = kapJ P j := by
  unfold kapM kapJ
  push_cast
  ring

theorem headPic_of (hJ : HeadJ) : HeadPic := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh X μ L st Φ hD hF hw hΦ t ht e y hy
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega
  have hc : y.1 ∈ OmX (P.r - (j + 1)) := hy.1
  have hdom := fun τ (hτ : τ ≠ 0) => base_point_mem_domain hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj) hy hτ
  have hL : IsActualLevel X L := hD.2.2.1

  set gg : ℝ := ∏ a : Fin (P.r - (j + 1)),
    (if a.val < (Fin.last (P.r - (j + 1))).val then ‖y.1 a‖ ^ (Mdim P.k (P.r - (j + 1)) a - 1) else 1) with hgg
  have hgg0 : gg ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => by
    split_ifs
    · exact pow_ne_zero _ (norm_ne_zero_iff.2 (hc a))
    · exact one_ne_zero
  set γ := wCell P.k (P.r - (j + 1)) (Fin.last _) y.1 * y.2 with hγdef
  have hγ : γ ∈ B.GV P.k (P.r - (j + 1)) := Formalism.FourierDecayAlt.P.PBF.wCell_mul_GV hc hy.2.1
  have hΩ : γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus (p.T.bs (j + 1)).z_mem (p.T.bs (j + 1)).z'_mem hy.1 hy.2.1 hy.2.2

  let Rd := rdL (k := P.k) (π := (p.T.bs j).π) (π' := (p.T.bs j).π') hn y hdom
  let φ : Wd.Ix (Fin w.length) → V1 (Wq →L[ℂ] Wp) := fun b => (((gg⁻¹ : ℝ)) : ℂ) • Rd (Φ b)
  have hφ : ∀ b τ, τ ≠ 0 → (φ b).1 τ =
      B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b) (mLev P j hj τ γ) := by
    intro b τ hτ
    have hr := pic_read (k := P.k) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
      (Subtype.val (Φ b)) (B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)) (hΦ b) hτ y hy
    have hraw := raw_eq hn y hdom (Φ b) hτ
    change (((gg⁻¹ : ℝ)) : ℂ) • (Rd (Φ b)).1 τ = _
    have hpos : ‖τ‖ ^ (2 * (P.r - j) + P.k) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hτ)
    have hR : (Rd (Φ b)).1 τ = Q.resG P.k (P.r - (j + 1)) (Fin.last _)
        (fun γ' => B.JF (p.T.bs j) (KB.slv p.T F j (by omega) w h hh.2 b)
          (D.castM hn (U.mMap P.k 1 (P.r - (j + 1)) (Matrix.of fun _ _ => τ) γ'))) y.1 y.2 := by
      have h2 := hraw.symm.trans hr
      have h3 := congrArg (fun v => (((‖τ‖ ^ (2 * (P.r - j) + P.k))⁻¹ : ℝ) : ℂ) • v) h2
      simp only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hpos, Complex.ofReal_one, one_smul] at h3
      exact h3
    rw [hR]
    unfold resG
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hgg0, Complex.ofReal_one, one_smul]
    rfl
  have hRφ : (fun b => Rd (Φ b)) = fun b => ((gg : ℝ) : ℂ) • φ b := by
    funext b
    simp only [φ, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hgg0, Complex.ofReal_one, one_smul]
  have hJe := hJ Wp Wq P p F j hj w h hh γ hF hw hγ hΩ φ hφ t ht e

  have hraw := raw_eq hn y hdom (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Φ e) ht0
  have hact := rd_act hn y hc hdom X hL (D.positionted w) Φ e
  refine hraw.trans ?_
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (Rd (P5.act _ Φ e)).1 t = _
  rw [hact, hRφ]
  unfold oneBT
  rw [act_one_variable_smul, kapM_eq]
  change ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) • (((gg : ℝ) : ℂ) • (oneBT (kapJ P j) (D.positionted w) φ e).1 t) = _
  rw [← hJe]
  congr 1

end Formalism.FourierDecayAlt.P.PBP

namespace Formalism.FourierDecayAlt.P

theorem pb_radHead_of_headJ (hJ : LevelPointCoordinates.HeadJ) : KB.RadHead := pb_radHead_of_headPic (PBP.headPic_of hJ)

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {j : ℕ}

theorem cont_ofSnd : Continuous fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := continuous_snd

theorem contDiff_ofSnd : ContDiff ℝ ∞ fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := contDiff_snd

theorem contDiff_pair (τ : ℂ) : ContDiff ℝ ∞ fun Z : MJ j => ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) :=
  contDiff_const.prodMk contDiff_id

theorem isOpen_inv : IsOpen {Z : MJ j | Z.det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem diffAt_fst {G : ℂ × (Fin j → Fin j → ℂ) → E} {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ U) :
    DifferentiableAt ℝ (fun τ : ℂ => G (τ, q.2)) q.1 := by
  have hd : DifferentiableAt ℝ G q := (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  exact hd.comp q.1 ((differentiableAt_id).prodMk (differentiableAt_const _))

theorem dz_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dz (fun s => F s + G s) τ = PBP.dz F τ + PBP.dz G τ := by
  unfold PBP.dz
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dzb_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dzb (fun s => F s + G s) τ = PBP.dzb F τ + PBP.dzb G τ := by
  unfold PBP.dzb
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dz_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dz (fun s => c • F s) τ = c • PBP.dz F τ := by
  unfold PBP.dz
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dzb_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dzb (fun s => c • F s) τ = c • PBP.dzb F τ := by
  unfold PBP.dzb
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dz_const (v : E) (τ : ℂ) : PBP.dz (fun _ : ℂ => v) τ = 0 := by simp [PBP.dz]

theorem dzb_const (v : E) (τ : ℂ) : PBP.dzb (fun _ : ℂ => v) τ = 0 := by simp [PBP.dzb]

theorem zop_id : ZOp (E := E) (j := j) (fun h => h) := by
  refine ⟨fun h₁ h₂ Z h => h.eq_of_nhds, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro U κ _ _ hκ
  exact ⟨hκ, fun q _ => ⟨rfl, rfl⟩⟩

theorem zop_zero : ZOp (E := E) (j := j) (fun _ _ => 0) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ => by simp, ?_⟩
  intro U κ _ _ _
  exact ⟨contDiffOn_const, fun q _ => ⟨dz_const _ _, dzb_const _ _⟩⟩

theorem ZOp.smooth {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {V : Set (MJ j)} (hV : IsOpen V)
    (hVi : V ⊆ {Z | Z.det ≠ 0}) {h : MJ j → E} (hh : ContDiffOn ℝ ∞ h V) : ContDiffOn ℝ ∞ (T h) V := by
  let U : Set (ℂ × (Fin j → Fin j → ℂ)) := {q | (Matrix.of q.2 : MJ j) ∈ V}
  have hU : IsOpen U := hV.preimage cont_ofSnd
  have hUi : U ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hVi hq
  have hκ : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (fun _ : ℂ => h) q.1 (Matrix.of q.2)) U :=
    hh.comp contDiff_ofSnd.contDiffOn (fun q hq => hq)
  have h1 := (hT.par U (fun _ => h) hU hUi hκ).1
  exact h1.comp (contDiff_pair 0).contDiffOn (fun Z hZ => hZ)

theorem ZOp.add' {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) :
    ZOp (fun h Z => T h Z + S h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h, hS.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, hS.add V h₁ h₂ hV hVi s₁ s₂ Z hZ]; abel
  · intro V c h hV hVi s Z hZ
    rw [hT.smul V c h hV hVi s Z hZ, hS.smul V c h hV hVi s Z hZ, smul_add]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    refine ⟨t1.add s1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    have d2 := diffAt_fst hU s1 hq
    refine ⟨?_, ?_⟩
    · rw [dz_add d1 d2, (t2 q hq).1, (s2 q hq).1]
    · rw [dzb_add d1 d2, (t2 q hq).2, (s2 q hq).2]

theorem ZOp.cmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {c : MJ j → ℂ}
    (hc : ContDiffOn ℝ ∞ c {Z | Z.det ≠ 0}) : ZOp (fun h Z => c Z • T h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, smul_add]
  · intro V c' h hV hVi s Z hZ
    rw [hT.smul V c' h hV hVi s Z hZ, smul_comm]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    have hc' : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => c (Matrix.of q.2)) U :=
      hc.comp contDiff_ofSnd.contDiffOn (fun q hq => hUi hq)
    refine ⟨hc'.smul t1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    exact ⟨by rw [dz_smul d1, (t2 q hq).1], by rw [dzb_smul d1, (t2 q hq).2]⟩

theorem ZOp.csmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (c : ℂ) : ZOp (fun h Z => c • T h Z) :=
  hT.cmul (c := fun _ => c) contDiffOn_const

theorem ZOp.comp {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) : ZOp (fun h => T (S h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h₁ h₂ Z h
    apply hT.loc
    filter_upwards [h.eventually_nhds] with Z' hZ'
    exact hS.loc _ _ Z' hZ'
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    have e : S (h₁ + h₂) =ᶠ[𝓝 Z] S h₁ + S h₂ := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.add V h₁ h₂ hV hVi s₁ s₂ Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.add V (S h₁) (S h₂) hV hVi (hS.smooth hV hVi s₁) (hS.smooth hV hVi s₂) Z hZ
  · intro V c h hV hVi s Z hZ
    have e : S (c • h) =ᶠ[𝓝 Z] c • S h := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.smul V c h hV hVi s Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.smul V c (S h) hV hVi (hS.smooth hV hVi s) Z hZ
  · intro U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U (fun τ => S (κ τ)) hU hUi s1
    refine ⟨t1, fun q hq => ?_⟩
    have hsl : IsOpen {Z : MJ j | ((q.1, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (contDiff_pair q.1).continuous
    have e1 : (fun Z => PBP.dz (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dz (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).1
    have e2 : (fun Z => PBP.dzb (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).2
    exact ⟨by rw [(t2 q hq).1, hT.loc _ _ _ e1], by rw [(t2 q hq).2, hT.loc _ _ _ e2]⟩

theorem zop_sum {ι : Type*} (s : Finset ι) {T : ι → (MJ j → E) → MJ j → E} (hT : ∀ i ∈ s, ZOp (T i)) :
    ZOp (fun h Z => ∑ i ∈ s, T i h Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zop_zero (E := E) (j := j))
  | insert a s ha ih =>
    have h1 := (hT a (by simp)).add' (ih (fun i hi => hT i (by simp [hi])))
    simpa [Finset.sum_insert ha] using h1

theorem zop_foldr : ∀ L : List ((MJ j → E) → MJ j → E), (∀ T ∈ L, ZOp T) →
    ZOp (fun f => L.foldr (fun T h => T h) f)
  | [], _ => zop_id
  | T :: L, h => by
    simp only [List.foldr_cons]
    exact (h T (by simp)).comp (zop_foldr L (fun T' hT' => h T' (by simp [hT'])))

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

def TopG {ι X : Type} [DecidableEq ι] (Eop : ι → ι → (X → E) → (X → E)) (u : ℂ) (a b : ι) (f : X → E) : X → E :=
  fun g => (if a = b then u • f g else 0) + Eop a b f g

def qminG {ι X : Type} [DecidableEq ι] {t : ℕ} (Eop : ι → ι → (X → E) → (X → E)) (a b : Fin t → ι) (u : ℂ)
    (f : X → E) : X → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => TopG Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f)

def EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : (MJ j → E) → MJ j → E :=
  if hp : p.val < j then (if hq : q.val < j then EZ ⟨p.val, hp⟩ ⟨q.val, hq⟩ else fun _ _ => 0)
  else if hp' : 2 * r + k < p.val + j then
    (if hq' : 2 * r + k < q.val + j then
      EZs ⟨2 * r + k - p.val, by omega⟩ ⟨2 * r + k - q.val, by omega⟩ else fun _ _ => 0)
  else fun _ _ => 0

def cZ {j N : ℕ} (Z : MJ j) (p : Fin N) (a : Fin j) : ℂ := if hp : p.val < j then Z a ⟨p.val, hp⟩ else 0

def cvZ (k r : ℕ) {j : ℕ} (Z : MJ j) (p : Fin (2 * r + k + 1)) (a : Fin j) : ℂ :=
  if hp : 2 * r + k < p.val + j then conj (Z a ⟨2 * r + k - p.val, by omega⟩) else 0

open scoped Classical in

def AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ c : Fin m → Fin (2 * r + k + 1),
    if StrictMono c then
      (Matrix.of fun a l : Fin m => cZ Z (c l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) (C3.xR k r m hm) c u h Z
    else 0

open scoped Classical in

def AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) (h : MJ j → E) : MJ j → E := fun Z =>
  ∑ B : Fin m → Fin (2 * r + k + 1),
    if StrictMono (fun l => C3.keyS k r (B l)) then
      (Matrix.of fun a l : Fin m => cvZ k r Z (B l) (Fin.castLE hmj a)).det •
        qminG (EopZ (E := E) k r j) B (C3.sR k r m hm) (ell + (m : ℂ) - 1) h Z
    else 0

def Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) (h : MJ j → E) : MJ j → E := fun Z =>
  if e = 1 ∧ j = 0 then 0 else
  if l.1 then
    (Z.det)⁻¹ • AZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) h Z
  else
    (conj Z.det)⁻¹ • AvZ k r j (j - e) (by omega) (by omega) ((l.2 : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) h Z

section zop

variable (hR : ZOpRd)
include hR

theorem zop_EZ {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZ a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EZs {j : ℕ} (a b : Fin j) : ZOp (E := E) (EZs a b) :=
  (hR j E _).add' ((hR j E _).csmul Complex.I)

theorem zop_EopZ (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : ZOp (E := E) (EopZ k r j p q) := by
  unfold EopZ
  split_ifs
  · exact zop_EZ hR _ _
  · exact zop_zero
  · exact zop_EZs hR _ _
  · exact zop_zero
  · exact zop_zero

theorem zop_TopG (k r j : ℕ) (u : ℂ) (p q : Fin (2 * r + k + 1)) :
    ZOp (E := E) (TopG (EopZ k r j) u p q) := by
  have h1 : ZOp (E := E) (j := j) (fun f g => if p = q then u • f g else 0) := by
    split_ifs
    · exact zop_id.csmul u
    · exact zop_zero
  exact h1.add' (zop_EopZ hR k r j p q)

theorem zop_qminG (k r j : ℕ) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ) :
    ZOp (E := E) (qminG (EopZ k r j) a b u) := by
  have e : (qminG (E := E) (EopZ k r j) a b u) = fun h Z => ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin t))),
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun k' : Fin t =>
        TopG (EopZ (E := E) k r j) (u - ((k' : ℕ) : ℂ)) (a (σ k')) (b k')).foldr (fun T h => T h) h Z) := by
    funext h Z
    simp [qminG, Finset.sum_apply]
  rw [e]
  refine zop_sum _ (fun σ _ => ?_)
  refine ZOp.csmul ?_ _
  refine zop_foldr _ (fun T hT => ?_)
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hT
  exact zop_TopG hR k r j _ _ _

end zop

theorem contDiff_entry {j : ℕ} (a b : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => Z a b :=
  (contDiff_apply ℝ ℂ b).comp (contDiff_apply ℝ (Fin j → ℂ) a)

theorem contDiff_det_of {j m : ℕ} (M : MJ j → Matrix (Fin m) (Fin m) ℂ) (hM : ∀ a b, ContDiff ℝ ∞ fun Z => M Z a b) :
    ContDiff ℝ ∞ fun Z => (M Z).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum (fun σ _ => ?_)
  simp only [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod (fun i _ => hM _ _))

theorem contDiff_cZ {j N : ℕ} (p : Fin N) (a : Fin j) : ContDiff ℝ ∞ fun Z : MJ j => cZ Z p a := by
  unfold cZ
  split_ifs
  · exact contDiff_entry _ _
  · exact contDiff_const

theorem contDiff_cvZ (k r : ℕ) {j : ℕ} (p : Fin (2 * r + k + 1)) (a : Fin j) :
    ContDiff ℝ ∞ fun Z : MJ j => cvZ k r Z p a := by
  unfold cvZ
  split_ifs
  · exact Complex.conjCLE.contDiff.comp (contDiff_entry _ _)
  · exact contDiff_const

theorem contDiffOn_invDet {j : ℕ} : ContDiffOn ℝ ∞ (fun Z : MJ j => (Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b)).contDiffOn.inv (fun Z hZ => hZ)

theorem contDiffOn_invConjDet {j : ℕ} :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (conj Z.det)⁻¹) {Z | Z.det ≠ 0} :=
  (Complex.conjCLE.contDiff.comp (contDiff_det_of (fun Z => Z) (fun a b => contDiff_entry a b))).contDiffOn.inv
    (fun Z hZ => by simpa using hZ)

section zop2

variable (hR : ZOpRd)
include hR

theorem zop_AZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ) : ZOp (E := E) (AZ k r j m hm hmj u) := by
  classical
  unfold AZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ u).cmul
      (contDiff_det_of _ (fun a l => contDiff_cZ _ _)).contDiffOn
  · exact zop_zero

theorem zop_AvZ (k r j m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (ell : ℂ) : ZOp (E := E) (AvZ k r j m hm hmj ell) := by
  classical
  unfold AvZ
  refine zop_sum _ (fun c _ => ?_)
  split_ifs
  · exact (zop_qminG hR k r j _ _ _).cmul
      (contDiff_det_of _ (fun a l => contDiff_cvZ k r _ _)).contDiffOn
  · exact zop_zero

theorem zop_Aform (k r j : ℕ) (hj : j + 1 ≤ r) (l : C.Letter) (e : Fin 2) :
    ZOp (E := E) (Aform k r j hj l e) := by
  unfold Aform
  split_ifs
  · exact zop_zero
  · exact (zop_AZ hR _ _ _ _ _ _ _).cmul contDiffOn_invDet
  · exact (zop_AvZ hR _ _ _ _ _ _ _).cmul contDiffOn_invConjDet

end zop2
end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

section transfer

variable {k r j : ℕ} (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))

def Good (k r j : ℕ) (p q : Fin (2 * r + k + 1)) : Prop :=
  (p.val < j ∧ q.val < j) ∨ (2 * r + k < p.val + j ∧ 2 * r + k < q.val + j)

theorem rdV_levi (hC : CurveLevi) (x : MJ j) (f : Q.Mx k r → E) (Z : MJ j) :
    RdV (levi k r j x) f (x0 k r j hj Z τ γ) = RdV x (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold RdV
  congr 1
  funext t
  rw [hC k r j hj Z τ γ x t]

theorem EopZ_e (a b : Fin j) :
    EopZ (E := E) k r j (eI k r (Fin.castLE (by omega) a)) (eI k r (Fin.castLE (by omega) b)) = EZ a b := by
  unfold EopZ
  simp [eI]

theorem EopZ_es (a b : Fin j) :
    EopZ (E := E) k r j (esI k r (Fin.castLE (by omega) a)) (esI k r (Fin.castLE (by omega) b)) = EZs a b := by
  unfold EopZ
  have ha := a.isLt
  have hb := b.isLt
  rw [dif_neg (by simp [esI]; omega), dif_pos (by simp [esI]; omega), dif_pos (by simp [esI]; omega)]
  congr 1 <;> ext <;> simp [esI] <;> omega

theorem eab_pull (hC : CurveLevi) (hH : HpartLevi) (p q : Fin (2 * r + k + 1)) (hpq : Good k r j p q)
    (f : Q.Mx k r → E) (Z : MJ j) :
    EabH (Hpk k r) p q f (x0 k r j hj Z τ γ) = EopZ k r j p q (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  have hjr : j ≤ r := by omega
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · obtain ⟨a, rfl⟩ : ∃ a : Fin j, p = eI k r (Fin.castLE hjr a) := ⟨⟨p.val, hp⟩, Fin.ext rfl⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin j, q = eI k r (Fin.castLE hjr b) := ⟨⟨q.val, hq⟩, Fin.ext rfl⟩
    rw [EopZ_e hj]
    unfold EabH EZ
    rw [(hH k r j hjr a b).1, (hH k r j hjr a b).2.1, rdV_levi hj τ γ hC, rdV_levi hj τ γ hC]
  · have hp2 := p.isLt
    have hq2 := q.isLt
    obtain ⟨a, rfl⟩ : ∃ a : Fin j, p = esI k r (Fin.castLE hjr a) :=
      ⟨⟨2 * r + k - p.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩
    obtain ⟨b, rfl⟩ : ∃ b : Fin j, q = esI k r (Fin.castLE hjr b) :=
      ⟨⟨2 * r + k - q.val, by omega⟩, Fin.ext (by simp [esI]; omega)⟩
    rw [EopZ_es hj]
    unfold EabH EZs
    rw [(hH k r j hjr a b).2.2.1, (hH k r j hjr a b).2.2.2, rdV_levi hj τ γ hC, rdV_levi hj τ γ hC]

theorem top_pull (hC : CurveLevi) (hH : HpartLevi) (u : ℂ) (p q : Fin (2 * r + k + 1)) (hpq : Good k r j p q)
    (f : Q.Mx k r → E) (Z : MJ j) :
    QuantumDeterminants.Top (EabH (Hpk k r)) u p q f (x0 k r j hj Z τ γ) =
      TopG (EopZ k r j) u p q (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold QuantumDeterminants.Top TopG
  rw [eab_pull hj τ γ hC hH p q hpq]

def Rel (T : (Q.Mx k r → E) → Q.Mx k r → E) (S : (MJ j → E) → MJ j → E) : Prop :=
  ∀ (f : Q.Mx k r → E) (Z : MJ j), T f (x0 k r j hj Z τ γ) = S (fun Z' => f (x0 k r j hj Z' τ γ)) Z

theorem foldr_pull : ∀ (L₁ : List ((Q.Mx k r → E) → Q.Mx k r → E)) (L₂ : List ((MJ j → E) → MJ j → E)),
    List.Forall₂ (Rel (E := E) hj τ γ) L₁ L₂ →
    ∀ (f : Q.Mx k r → E) (Z : MJ j),
      (L₁.foldr (fun (T : (Q.Mx k r → E) → Q.Mx k r → E) (h : Q.Mx k r → E) => T h) f) (x0 k r j hj Z τ γ) =
      (L₂.foldr (fun (T : (MJ j → E) → MJ j → E) (h : MJ j → E) => T h) (fun Z' => f (x0 k r j hj Z' τ γ))) Z
  | [], [], _ => fun _ _ => rfl
  | T :: L₁, S :: L₂, List.Forall₂.cons h hL => by
    intro f Z
    simp only [List.foldr_cons]
    rw [h]
    congr 1
    funext Z'
    exact foldr_pull L₁ L₂ hL f Z'

theorem forall₂_ofFn {α β : Type*} (R : α → β → Prop) : ∀ (n : ℕ) (F : Fin n → α) (G : Fin n → β),
    (∀ i, R (F i) (G i)) → List.Forall₂ R (List.ofFn F) (List.ofFn G)
  | 0, _, _, _ => by simp
  | n + 1, F, G, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn R n _ _ (fun i => h i.succ))

theorem qmin_pull (hC : CurveLevi) (hH : HpartLevi) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1)) (u : ℂ)
    (hab : ∀ (σ : Equiv.Perm (Fin t)) (i : Fin t), Good k r j (a (σ i)) (b i)) (f : Q.Mx k r → E) (Z : MJ j) :
    qminorOp (EabH (Hpk k r)) a b u f (x0 k r j hj Z τ γ) =
      qminG (EopZ k r j) a b u (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  unfold qminorOp qminG
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  congr 1
  refine foldr_pull hj τ γ _ _ ?_ f Z
  exact forall₂_ofFn (Rel (E := E) hj τ γ) t _ _ (fun i f' Z' => top_pull hj τ γ hC hH _ _ _ (hab σ i) f' Z')

theorem AAop_pull (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (m : ℕ) (hm : m ≤ r) (hmj : m ≤ j) (u : ℂ)
    (f : Q.Mx k r → E) (Z : MJ j) :
    C3.AAop k r m hm u f (x0 k r j hj Z τ γ) = AZ k r j m hm hmj u (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  classical
  unfold C3.AAop AZ
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · have hcoef : (Matrix.of fun a l : Fin m =>
        herm (Hpk k r) (x0 k r j hj Z τ γ *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE hm a)))) =
        Matrix.of fun a l => cZ Z (c l) (Fin.castLE hmj a) := by
      ext a l
      exact hXC k r j hj Z τ γ (Fin.castLE hmj a) (c l)
    rw [hcoef]
    by_cases hall : ∀ l, (c l).val < j
    · rw [qmin_pull hj τ γ hC hH]
      intro σ i
      left
      exact ⟨by simp [C3.xR, eI]; omega, hall i⟩
    · push Not at hall
      obtain ⟨l, hl⟩ := hall
      rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [cZ]; omega)]
      simp
  · rfl

theorem AAvop_pull (hC : CurveLevi) (hH : HpartLevi) (hXV : XiCoefV) (m : ℕ) (hm : m ≤ r) (hmj : m ≤ j)
    (ell : ℂ) (f : Q.Mx k r → E) (Z : MJ j) (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) :
    C3.AAvop k r m hm ell f (x0 k r j hj Z τ γ) = AvZ k r j m hm hmj ell (fun Z' => f (x0 k r j hj Z' τ γ)) Z := by
  classical
  unfold C3.AAvop AvZ
  refine Finset.sum_congr rfl (fun c _ => ?_)
  split_ifs with hc
  · have hcoef : (Matrix.of fun a l : Fin m =>
        ((x0 k r j hj Z τ γ)⁻¹ *ᵥ bvec (eI k r (Fin.castLE hm a))) (c l)) =
        Matrix.of fun a l => cvZ k r Z (c l) (Fin.castLE hmj a) := by
      ext a l
      exact hXV k r j hj Z τ γ hZ hτ hγ (Fin.castLE hmj a) (c l)
    rw [hcoef]
    by_cases hall : ∀ l, 2 * r + k < (c l).val + j
    · rw [qmin_pull hj τ γ hC hH]
      intro σ i
      right
      have := i.isLt
      exact ⟨hall (σ i), by simp [C3.sR, esI]; omega⟩
    · push Not at hall
      obtain ⟨l, hl⟩ := hall
      rw [Matrix.det_eq_zero_of_column_eq_zero l (fun a => by simp [cvZ]; omega)]
      simp
  · rfl

theorem Dmin_pull (hXC : XiCoef) (z z' : Fin (2 * r + k + 1) → ℂ) (Z : MJ j) :
    Dmin k r z z' (x0 k r j hj Z τ γ) ⟨j, by omega⟩ = Z.det := by
  show ((Zhat k r z z' (x0 k r j hj Z τ γ)).submatrix (Fin.castLE (by omega : j ≤ r + 1))
    (Fin.castLE (by omega : j ≤ r + 1))).det = Z.det
  congr 1
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [Matrix.submatrix_apply, Zhat, fvec]
  rw [dif_pos (by simp; omega), dif_pos (by simp; omega)]
  have := hXC k r j hj Z τ γ a (eI k r ⟨b.val, by omega⟩)
  simp only [eI] at this ⊢
  simpa [hb] using this

theorem vLet_pull (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (hXV : XiCoefV)
    (z z' : Fin (2 * r + k + 1) → ℂ) (l : C.Letter) (e : Fin 2) (Φ : Q.Mx k r → E) (Z : MJ j)
    (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) :
    D.vLet k r z z' j (by omega) l e Φ (x0 k r j hj Z τ γ) =
      Aform k r j hj l e (fun Z' => Φ (x0 k r j hj Z' τ γ)) Z := by
  unfold D.vLet Aform
  split_ifs
  · rfl
  · rw [Dmin_pull hj τ γ hXC, AAop_pull hj τ γ hC hH hXC]
  · rw [Dmin_pull hj τ γ hXC, AAvop_pull hj τ γ hC hH hXV _ _ _ _ _ Z hZ hτ hγ]

end transfer

section lin

variable {j : ℕ}

def W (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Z : MJ j) : Submodule ℂ (MJ j → E) where
  carrier := {h | ∃ V : Set (MJ j), IsOpen V ∧ Z ∈ V ∧ ContDiffOn ℝ ∞ h V}
  add_mem' := by
    rintro h₁ h₂ ⟨V₁, o₁, m₁, s₁⟩ ⟨V₂, o₂, m₂, s₂⟩
    exact ⟨V₁ ∩ V₂, o₁.inter o₂, ⟨m₁, m₂⟩, (s₁.mono Set.inter_subset_left).add (s₂.mono Set.inter_subset_right)⟩
  zero_mem' := ⟨Set.univ, isOpen_univ, trivial, contDiffOn_const⟩
  smul_mem' := by
    rintro c h ⟨V, o, m, s⟩
    exact ⟨V, o, m, s.const_smul c⟩

def fW {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (Z : MJ j) (hZ : Z.det ≠ 0) : W E Z →ₗ[ℂ] E where
  toFun h := T h.1 Z
  map_add' := by
    rintro ⟨h₁, V₁, o₁, m₁, s₁⟩ ⟨h₂, V₂, o₂, m₂, s₂⟩
    exact hT.add (V₁ ∩ V₂ ∩ {Z | Z.det ≠ 0}) h₁ h₂ ((o₁.inter o₂).inter isOpen_inv)
      (fun _ h => h.2) (s₁.mono (fun _ h => h.1.1)) (s₂.mono (fun _ h => h.1.2)) Z ⟨⟨m₁, m₂⟩, hZ⟩
  map_smul' := by
    rintro c ⟨h, V, o, m, s⟩
    exact hT.smul (V ∩ {Z | Z.det ≠ 0}) c h (o.inter isOpen_inv) (fun _ h => h.2) (s.mono (fun _ h => h.1)) Z ⟨m, hZ⟩

def linOf {T : (MJ j → E) → MJ j → E} (hT : ZOp T) : (MJ j → E) →ₗ[ℂ] (MJ j → E) :=
  LinearMap.pi fun Z => if hZ : Z.det ≠ 0 then Classical.choose (LinearMap.exists_extend (fW hT Z hZ)) else 0

theorem linOf_eq {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {Z : MJ j} (hZ : Z.det ≠ 0) {h : MJ j → E}
    (hh : h ∈ W E Z) : linOf hT h Z = T h Z := by
  simp only [linOf, LinearMap.pi_apply, dif_pos hZ]
  have := Classical.choose_spec (LinearMap.exists_extend (fW hT Z hZ))
  exact congrArg (fun L : W E Z →ₗ[ℂ] E => L ⟨h, hh⟩) this

theorem dz_congr {F G : ℂ → E} {τ : ℂ} (h : F =ᶠ[𝓝 τ] G) : PBP.dz F τ = PBP.dz G τ := by
  unfold PBP.dz; rw [h.fderiv_eq]

theorem dzb_congr {F G : ℂ → E} {τ : ℂ} (h : F =ᶠ[𝓝 τ] G) : PBP.dzb F τ = PBP.dzb G τ := by
  unfold PBP.dzb; rw [h.fderiv_eq]

theorem linOf_par (hD : DzSlice) {T : (MJ j → E) → MJ j → E} (hT : ZOp T) : ParamComm (linOf hT) := by
  intro U κ hU hUi hκ
  obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
  have hsl : ∀ τ : ℂ, IsOpen {Z : MJ j | ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
    fun τ => hU.preimage (contDiff_pair τ).continuous
  have key : ∀ (τ : ℂ) (Z : MJ j), ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U →
      linOf hT (κ τ) Z = T (κ τ) Z := by
    intro τ Z hτZ
    exact linOf_eq hT (hUi hτZ) ⟨_, hsl τ, hτZ, hκ.comp (contDiff_pair τ).contDiffOn (fun _ h => h)⟩
  refine ⟨t1.congr (fun q hq => key q.1 (Matrix.of q.2) hq), fun q hq => ?_⟩
  have hev : (fun τ => linOf hT (κ τ) (Matrix.of q.2)) =ᶠ[𝓝 q.1] (fun τ => T (κ τ) (Matrix.of q.2)) := by
    have hop : IsOpen {τ : ℂ | ((τ, q.2) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (continuous_id.prodMk continuous_const)
    filter_upwards [hop.mem_nhds (show (q.1, q.2) ∈ U from hq)] with τ hτ
    exact key τ _ hτ
  obtain ⟨d1, d2⟩ := hD j E U κ hU hκ q.1
  refine ⟨?_, ?_⟩
  · rw [dz_congr hev, (t2 q hq).1]
    exact (linOf_eq hT (hUi hq) ⟨_, hsl q.1, hq, d1⟩).symm
  · rw [dzb_congr hev, (t2 q hq).2]
    exact (linOf_eq hT (hUi hq) ⟨_, hsl q.1, hq, d2⟩).symm

end lin

theorem zOnly_of_parts (hC : CurveLevi) (hH : HpartLevi) (hXC : XiCoef) (hXV : XiCoefV) (hXM : XiMem)
    (hXS : XiSmooth) (hR : ZOpRd) (hD : DzSlice) : ZOnly := by
  intro k r j hj z z' E _ _ l e _ _
  refine ⟨linOf (zop_Aform (E := E) hR k r j hj l e), linOf_par hD _, ?_⟩
  intro Dm Φ _ _ hsm Z τ γ hZ hτ hγ hmem
  rw [vLet_pull hj τ γ hC hH hXC hXV z z' l e Φ Z hZ hτ hγ]
  refine (linOf_eq _ hZ ?_).symm
  obtain ⟨UF, F, hUF, hgUF, hF, hΦF⟩ := hsm _ ⟨hXM k r j hj Z τ γ hZ hτ hγ, hmem⟩
  have hcont := (hXS k r j hj τ γ).continuousOn
  refine ⟨{Z' | Z'.det ≠ 0} ∩ (fun Z' => x0 k r j hj Z' τ γ) ⁻¹' UF,
    hcont.isOpen_inter_preimage isOpen_inv hUF, ⟨hZ, hgUF⟩, ?_⟩
  refine (hF.comp ((hXS k r j hj τ γ).mono Set.inter_subset_left) (fun _ h => h.2)).congr ?_
  intro Z' hZ'
  exact hΦF _ hZ'.2 (hXM k r j hj Z' τ γ hZ'.1 hτ hγ)

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem castM_apply' {k a b : ℕ} (h : a = b) (g : B.Mat k a) (p q : Fin (2 * b + k + 1)) :
    D.castM h g p q = g (Fin.cast (by omega) p) (Fin.cast (by omega) q) := by
  subst h; simp [D.castM, Matrix.reindex_apply]

theorem castM_GV' {k a b : ℕ} (h : a = b) {g : B.Mat k a} (hg : g ∈ B.GV k a) : D.castM h g ∈ B.GV k b := by
  subst h; simpa [D.castM] using hg

theorem zfull_apply {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (c d : Fin (j + 1)) :
    zfull Z τ c d = if hc : c.val < j then (if hd : d.val < j then Z ⟨c.val, hc⟩ ⟨d.val, hd⟩ else 0)
      else (if d.val < j then 0 else τ) := by
  simp only [zfull, U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply, fsym]
  split_ifs <;> simp [Matrix.fromBlocks]

theorem det_zfull {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) : (zfull Z τ).det = Z.det * τ := by
  unfold zfull U.blk2
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  simp [Matrix.det_unique]

theorem wMat_mul_apply {d n : ℕ} (M : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (c : Fin n) :
    (G.wMat d * M) i c = M i.rev c := by
  simp [G.wMat, Matrix.mul_apply]

theorem level_point_first_lines (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin j) (q : Fin (2 * r + k + 1)) :
    x0 k r j hj Z τ γ (esI k r (Fin.castLE (by omega) a)) q = if hq : q.val < j then Z a ⟨q.val, hq⟩ else 0 := by
  unfold x0
  rw [castM_apply']
  have hrow : (Fin.cast (by omega) (esI k r (Fin.castLE (by omega) a)) : Fin (2 * (j + 1 + (r - (j + 1))) + k + 1)) =
      U.eB k (j + 1) (r - (j + 1)) (Sum.inr ⟨j - a.val, by omega⟩) := by
    ext; rw [Ux4.block_index_last_val_eq]; simp [esI]; omega
  rw [hrow]
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  rw [← hy]
  unfold U.mMap
  rw [Ux4.block3_apply]
  rcases y with ((c | c) | c)
  · have hq : q.val = c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_first_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inl]
    rw [wMat_mul_apply]
    have hrev : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = ⟨a.val, by omega⟩ := by
      ext; simp [Fin.rev]; omega
    rw [hrev, zfull_apply, dif_pos (by simp)]
    by_cases h : c.val < j
    · rw [dif_pos h, dif_pos (by omega)]
      exact congrArg₂ Z (Fin.ext rfl) (Fin.ext hq.symm)
    · rw [dif_neg h, dif_neg (by omega)]
  · have hq : q.val = j + 1 + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_middle_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromCols_apply_inr, Matrix.zero_apply]
    rw [dif_neg (by omega)]
  · have hq : q.val = j + 1 + (2 * (r - (j + 1)) + k + 1) + c.val := by
      have := congrArg Fin.val hy; rw [Ux4.block_index_last_val_eq] at this; simp at this; omega
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    rw [dif_neg (by omega)]

theorem Hpk_eI_row (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) s = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_eI_col (k r : ℕ) (a : Fin r) (s : Fin (2 * r + k + 1)) :
    Hpk k r s (eI k r a) = if s = esI k r a then 1 else 0 := by
  simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_low (k r : ℕ) (p s : Fin (2 * r + k + 1)) (hs : s.val < r) :
    Hpk k r p s = if p.val + s.val = 2 * r + k then 1 else 0 := by
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem xiCoef : XiCoef := by
  intro k r j hj Z τ γ a p
  have h1 : ∀ v : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) v (bvec (eI k r (Fin.castLE (by omega) a))) =
      ∑ s, Hpk k r (eI k r (Fin.castLE (by omega) a)) s * v s := by
    intro v
    simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [h1]
  simp only [Hpk_eI_row, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.transpose_apply]
  exact level_point_first_lines k r j hj Z τ γ a p

theorem x0_GV (k r j : ℕ) (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (hZ : Z.det ≠ 0) (hτ : τ ≠ 0) (hγ : γ ∈ B.GV k (r - (j + 1))) : x0 k r j hj Z τ γ ∈ B.GV k r := by
  unfold x0
  apply castM_GV'
  exact (Ux2.sliceMem k (j + 1) (r - (j + 1))).1 _ _ (by rw [det_zfull]; exact mul_ne_zero hZ hτ) hγ

theorem xiMem : XiMem := by
  intro k r j hj Z τ γ hZ hτ hγ
  exact ⟨x0_GV k r j hj Z τ γ hZ hτ hγ, fun a ha => absurd ha (by simp)⟩

theorem xiCoefV : XiCoefV := by
  intro k r j hj Z τ γ hZ hτ hγ a p
  have hinv := PBG.inv_GV (x0_GV k r j hj Z τ γ hZ hτ hγ)
  rw [hinv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hH : Hpk k r *ᵥ bvec (eI k r (Fin.castLE (by omega) a)) = bvec (esI k r (Fin.castLE (by omega) a)) := by
    ext s
    simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Hpk_eI_col, Pi.single_apply]
  rw [hH]
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  simp only [Matrix.mulVec, dotProduct]
  simp only [Matrix.col_apply, Matrix.conjTranspose_apply, level_point_first_lines]
  split_ifs with hp
  · rw [Fintype.sum_eq_single ⟨2 * r + k - p.val, by omega⟩]
    · have hH1 : Hpk k r p ⟨2 * r + k - p.val, by omega⟩ = 1 := by
        rw [Hpk_low _ _ _ _ (by simp only [Fin.val_mk]; omega), if_pos (by simp only [Fin.val_mk]; omega)]
      rw [hH1, one_mul, dif_pos (by simp only [Fin.val_mk]; omega)]
      rfl
    · intro s hs
      by_cases h : s.val < j
      · rw [dif_pos h]
        have : Hpk k r p s = 0 := by
          rw [Hpk_low _ _ _ _ (by omega), if_neg (by intro h'; apply hs; ext; simp only [Fin.val_mk]; omega)]
        rw [this, zero_mul]
      · rw [dif_neg h, star_zero, mul_zero]
  · refine Finset.sum_eq_zero fun s _ => ?_
    by_cases h : s.val < j
    · rw [dif_pos h]
      have : Hpk k r p s = 0 := by
        rw [Hpk_low _ _ _ _ (by omega), if_neg (by omega)]
      rw [this, zero_mul]
    · rw [dif_neg h, star_zero, mul_zero]

section smooth

variable {j : ℕ}

theorem contDiff_zfull (τ : ℂ) (c d : Fin (j + 1)) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun Z : MJ j => zfull Z τ c d) := by
  simp only [zfull_apply]
  split_ifs
  · exact contDiff_apply_apply ℝ ℂ _ _
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_const

theorem contDiff_adj_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiff ℝ ⊤ (fun Z : MJ j => (zfull Z τ).adjugate c d) := by
  simp only [Matrix.adjugate_apply]
  apply PBG.contDiff_det'
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_zfull τ a b

theorem contDiffOn_inv_zfull (τ : ℂ) (c d : Fin (j + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => (zfull Z τ)⁻¹ c d) {Z | Z.det ≠ 0} := by
  have he : ∀ Z : MJ j, (zfull Z τ)⁻¹ c d = (Z.det)⁻¹ * τ⁻¹ * (zfull Z τ).adjugate c d := by
    intro Z
    rw [Matrix.inv_def, Matrix.smul_apply, det_zfull, Ring.inverse_eq_inv', mul_inv, smul_eq_mul]
  simp only [he]
  have hdet : ContDiff ℝ ⊤ (fun Z : MJ j => Z.det) :=
    PBG.contDiff_det' (fun Z : MJ j => Z) (fun a b => contDiff_apply_apply ℝ ℂ a b)
  exact ((((hdet.of_le le_top).contDiffOn.inv (fun Z hZ => hZ)).mul contDiffOn_const).mul
    ((contDiff_adj_zfull τ c d).of_le le_top).contDiffOn)

theorem level_point_entry_contDiffOn (k r j : ℕ) (hj : j + 1 ≤ r) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (p q : Fin (2 * r + k + 1)) :
    ContDiffOn ℝ ∞ (fun Z : MJ j => x0 k r j hj Z τ γ p q) {Z | Z.det ≠ 0} := by
  obtain ⟨x, hx⟩ : ∃ x, U.eB k (j + 1) (r - (j + 1)) x = Fin.cast (by omega) p := ⟨_, Equiv.apply_symm_apply _ _⟩
  obtain ⟨y, hy⟩ : ∃ y, U.eB k (j + 1) (r - (j + 1)) y = Fin.cast (by omega) q := ⟨_, Equiv.apply_symm_apply _ _⟩
  have he : ∀ Z : MJ j, x0 k r j hj Z τ γ p q =
      Matrix.fromBlocks (Matrix.fromBlocks 0 0 0 γ) (Matrix.fromRows ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) 0)
        (Matrix.fromCols (G.wMat (j + 1) * zfull Z τ) 0) 0 x y := by
    intro Z
    unfold x0 U.mMap
    rw [castM_apply', ← hx, ← hy, Ux4.block3_apply]
  simp only [he]
  have h13 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => ((zfull Z τ)ᴴ⁻¹ * G.wMat (j + 1)) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply, ← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply]
    exact ContDiffOn.sum fun t _ =>
      (PBG.contDiff_starC.comp_contDiffOn (contDiffOn_inv_zfull τ t c)).mul contDiffOn_const
  have h31 : ∀ c d : Fin (j + 1),
      ContDiffOn ℝ ∞ (fun Z : MJ j => (G.wMat (j + 1) * zfull Z τ) c d) {Z | Z.det ≠ 0} := by
    intro c d
    simp only [Matrix.mul_apply]
    exact ContDiffOn.sum fun t _ => contDiffOn_const.mul (contDiff_zfull τ t d).contDiffOn
  rcases x with ((c | c) | c) <;> rcases y with ((d | d) | d) <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h13 c d
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact h31 c d
  · exact contDiffOn_const
  · exact contDiffOn_const

theorem xiSmooth : XiSmooth := by
  intro k r j hj τ γ
  exact contDiffOn_pi.2 fun p => contDiffOn_pi.2 fun q => level_point_entry_contDiffOn k r j hj τ γ p q

end smooth

end Formalism.FourierDecayAlt.P.WirtingerOperators.XiPf

namespace Formalism.FourierDecayAlt.P

theorem xi_coefficient : WirtingerOperators.XiCoef := WirtingerOperators.XiPf.xiCoef

theorem xi_coefficient_vector : WirtingerOperators.XiCoefV := WirtingerOperators.XiPf.xiCoefV

theorem xiMem_statement : WirtingerOperators.XiMem := WirtingerOperators.XiPf.xiMem

theorem xi_smooth : WirtingerOperators.XiSmooth := WirtingerOperators.XiPf.xiSmooth

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL

abbrev rdzPZ (j : ℕ) : Type := ℂ × (Fin j → Fin j → ℂ)

def rdzLdL {j : ℕ} (x : MJ j) : rdzPZ j →ₗ[ℝ] rdzPZ j where
  toFun q := (0, fun a b => ∑ c, q.2 a c * x c b)
  map_add' p q := Prod.ext (by simp) (by funext a b; simp [add_mul, Finset.sum_add_distrib])
  map_smul' t q := Prod.ext (by simp) (by funext a b; simp [Finset.smul_sum, mul_assoc])

def rdzLd {j : ℕ} (x : MJ j) : rdzPZ j →L[ℝ] rdzPZ j := LinearMap.toContinuousLinearMap (rdzLdL x)

theorem rdzLd_apply {j : ℕ} (x : MJ j) (q : rdzPZ j) : rdzLd x q = (0, fun a b => ∑ c, q.2 a c * x c b) := rfl

theorem rdzLd_inl {j : ℕ} (x : MJ j) (v : ℂ) : rdzLd x ((v, 0) : rdzPZ j) = 0 := by
  rw [rdzLd_apply]
  exact Prod.ext rfl (by funext a b; simp)

theorem rdz_curve {j : ℕ} (x : MJ j) (τ : ℂ) (Z : MJ j) :
    HasDerivAt (fun t : ℝ => ((τ, (Z * NormedSpace.exp ((t : ℂ) • x) : MJ j)) : rdzPZ j)) (rdzLd x (τ, Z)) 0 := by
  refine HasDerivAt.congr_deriv ((hasDerivAt_const (0 : ℝ) τ).prodMk (hasDerivAt_mul_exp_smul_zero Z x)) ?_
  rw [rdzLd_apply]
  exact Prod.ext rfl (funext fun a => funext fun b => Matrix.mul_apply)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rdz_da {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {h : F → E} {V : Set F} (hV : IsOpen V)
    (hh : ContDiffOn ℝ ∞ h V) {Z : F} (hZ : Z ∈ V) : DifferentiableAt ℝ h Z :=
  (hh.contDiffAt (hV.mem_nhds hZ)).differentiableAt (by simp)

theorem rdz_rd {j : ℕ} (x : MJ j) (G : rdzPZ j → E) (τ : ℂ) (Z : MJ j) (hd : DifferentiableAt ℝ G (τ, Z)) :
    RdV x (fun Z' : MJ j => G (τ, Z')) Z = fderiv ℝ G (τ, Z) (rdzLd x (τ, Z)) := by
  have h0 : ((τ, (Z * NormedSpace.exp (((0 : ℝ) : ℂ) • x) : MJ j)) : rdzPZ j) = (τ, Z) := by
    (simp [NormedSpace.exp_zero]; rfl)
  exact (hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (rdz_curve x τ Z) h0.symm).deriv

theorem rdz_loc {j : ℕ} (x : MJ j) (h₁ h₂ : MJ j → E) (Z : MJ j) (h : h₁ =ᶠ[𝓝 Z] h₂) :
    RdV x h₁ Z = RdV x h₂ Z := by
  have ht : Tendsto (fun t : ℝ => Z * NormedSpace.exp ((t : ℂ) • x)) (𝓝 0) (𝓝 Z) := by
    have := (hasDerivAt_mul_exp_smul_zero Z x).continuousAt.tendsto
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, mul_one] at this
    exact this
  unfold RdV
  exact Filter.EventuallyEq.deriv_eq (ht.eventually h)

theorem rdz_hd {j : ℕ} (x : MJ j) {h : MJ j → E} {Z : MJ j} (hd : DifferentiableAt ℝ h Z) :
    HasDerivAt (fun t : ℝ => h (Z * NormedSpace.exp ((t : ℂ) • x))) (fderiv ℝ h Z (Z * x)) 0 := by
  have h0 : Z * NormedSpace.exp (((0 : ℝ) : ℂ) • x) = Z := by simp [NormedSpace.exp_zero]
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_mul_exp_smul_zero Z x) h0.symm

def rdzK {j : ℕ} (κ : ℂ → MJ j → E) : rdzPZ j → E := fun q => κ q.1 (Matrix.of q.2)

theorem rdz_slice {j : ℕ} (κ : ℂ → MJ j → E) (τ₀ : ℂ) (Z₀ : MJ j)
    (hd : DifferentiableAt ℝ (rdzK κ) (τ₀, Z₀)) (v : ℂ) :
    fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ v = fderiv ℝ (rdzK κ) (τ₀, Z₀) (v, 0) := by
  have hι : HasFDerivAt (fun τ : ℂ => ((τ, Z₀) : rdzPZ j)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) τ₀ :=
    (hasFDerivAt_id τ₀).prodMk (hasFDerivAt_const _ τ₀)
  have h2 := (hd.hasFDerivAt.comp τ₀ hι).fderiv
  rw [show (fun τ : ℂ => κ τ Z₀) = rdzK κ ∘ (fun τ : ℂ => ((τ, Z₀) : rdzPZ j)) from rfl, h2]
  rfl

def rdzH {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) : rdzPZ j → E := fun p =>
  c • (fderiv ℝ (rdzK κ) p (1, 0) + s • fderiv ℝ (rdzK κ) p (Complex.I, 0))

theorem rdz_dz_eq (f : ℂ → E) (τ : ℂ) :
    PBP.dz f τ = (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + (-Complex.I) • fderiv ℝ f τ Complex.I) := by
  simp only [PBP.dz, neg_smul, sub_eq_add_neg]

theorem rdz_dzb_eq (f : ℂ → E) (τ : ℂ) :
    PBP.dzb f τ = (1 / 2 : ℂ) • (fderiv ℝ f τ 1 + Complex.I • fderiv ℝ f τ Complex.I) := rfl

theorem rdz_H_eq {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) (τ₀ : ℂ) (Z₀ : MJ j)
    (hd : DifferentiableAt ℝ (rdzK κ) (τ₀, Z₀)) :
    c • (fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ 1 + s • fderiv ℝ (fun τ : ℂ => κ τ Z₀) τ₀ Complex.I) =
      rdzH κ c s (τ₀, Z₀) := by
  rw [rdz_slice κ τ₀ Z₀ hd, rdz_slice κ τ₀ Z₀ hd]
  rfl

theorem rdz_H_smooth {j : ℕ} (κ : ℂ → MJ j → E) (c s : ℂ) {U : Set (rdzPZ j)} (hU : IsOpen U)
    (hK : ContDiffOn ℝ ∞ (rdzK κ) U) : ContDiffOn ℝ ∞ (rdzH κ c s) U := by
  have hK1 : ContDiffOn ℝ ∞ (fderiv ℝ (rdzK κ)) U := hK.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
  exact ((hK1.clm_apply contDiffOn_const).add ((hK1.clm_apply contDiffOn_const).const_smul s)).const_smul c

theorem rdz_par {j : ℕ} (x : MJ j) : ParamCommF (E := E) (fun h => RdV x h) := by
  intro U κ hU _ hK
  have hKc : ContDiffOn ℝ ∞ (rdzK κ) U := hK
  have hKd : ∀ q ∈ U, DifferentiableAt ℝ (rdzK κ) q := fun q hq => rdz_da hU hKc hq
  have hK1 : ContDiffOn ℝ ∞ (fderiv ℝ (rdzK κ)) U := hKc.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
  have hG1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (rdzK κ) q (rdzLd x q)) U :=
    hK1.clm_apply (rdzLd x).contDiff.contDiffOn
  have hrd : ∀ q ∈ U, RdV x (κ q.1) (Matrix.of q.2) = fderiv ℝ (rdzK κ) q (rdzLd x q) :=
    fun q hq => rdz_rd x (rdzK κ) q.1 (Matrix.of q.2) (hKd q hq)
  refine ⟨hG1.congr fun q hq => hrd q hq, fun q hq => ?_⟩
  have hKa : ContDiffAt ℝ ∞ (rdzK κ) q := hKc.contDiffAt (hU.mem_nhds hq)
  have hc : DifferentiableAt ℝ (fderiv ℝ (rdzK κ)) q :=
    (hKa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hsym : IsSymmSndFDerivAt ℝ (rdzK κ) q := hKa.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hG1d : HasFDerivAt (fun p => fderiv ℝ (rdzK κ) p (rdzLd x p))
      ((fderiv ℝ (rdzK κ) q).comp (rdzLd x) + (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip (rdzLd x q)) q :=
    hc.hasFDerivAt.clm_apply (rdzLd x).hasFDerivAt
  have hL : ∀ v : ℂ, fderiv ℝ (fun τ => RdV x (κ τ) (Matrix.of q.2)) q.1 v =
      fderiv ℝ (fderiv ℝ (rdzK κ)) q (v, 0) (rdzLd x q) := by
    intro v
    have hev : (fun τ => RdV x (κ τ) (Matrix.of q.2)) =ᶠ[𝓝 q.1]
        (fun τ => fderiv ℝ (rdzK κ) (τ, q.2) (rdzLd x (τ, q.2))) := by
      have hc' : ContinuousAt (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) q.1 :=
        (continuous_id.prodMk continuous_const).continuousAt
      filter_upwards [hc'.preimage_mem_nhds (hU.mem_nhds hq)] with τ hτ
      exact hrd (τ, q.2) hτ
    have hι : HasFDerivAt (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) ((ContinuousLinearMap.id ℝ ℂ).prod 0) q.1 :=
      (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const _ q.1)
    rw [hev.fderiv_eq, show (fun τ => fderiv ℝ (rdzK κ) (τ, q.2) (rdzLd x (τ, q.2))) =
      (fun p => fderiv ℝ (rdzK κ) p (rdzLd x p)) ∘ (fun τ : ℂ => ((τ, q.2) : rdzPZ j)) from rfl,
      (hG1d.comp q.1 hι).fderiv]
    simp [rdzLd_inl]
  have hR : ∀ c s : ℂ, RdV x (fun Z => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 1 +
      s • fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 Complex.I)) (Matrix.of q.2) =
      c • (fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (1, 0) +
        s • fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (Complex.I, 0)) := by
    intro c s
    have hev : (fun Z : MJ j => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 1 +
        s • fderiv ℝ (fun τ : ℂ => κ τ Z) q.1 Complex.I)) =ᶠ[𝓝 (Matrix.of q.2)]
        (fun Z : MJ j => rdzH κ c s (q.1, Z)) := by
      have hc' : ContinuousAt (fun Z : MJ j => ((q.1, Z) : rdzPZ j)) (Matrix.of q.2) :=
        (continuous_const.prodMk continuous_id).continuousAt
      filter_upwards [hc'.preimage_mem_nhds (hU.mem_nhds hq)] with Z hZ
      exact rdz_H_eq κ c s q.1 Z (hKd _ hZ)
    have hH : HasFDerivAt (rdzH κ c s)
        (c • (((fderiv ℝ (rdzK κ) q).comp 0 + (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip ((1, 0) : rdzPZ j)) +
          s • ((fderiv ℝ (rdzK κ) q).comp 0 +
            (fderiv ℝ (fderiv ℝ (rdzK κ)) q).flip ((Complex.I, 0) : rdzPZ j)))) q :=
      ((hc.hasFDerivAt.clm_apply (hasFDerivAt_const ((1, 0) : rdzPZ j) q)).add
        ((hc.hasFDerivAt.clm_apply (hasFDerivAt_const ((Complex.I, 0) : rdzPZ j) q)).const_smul s)).const_smul c
    rw [rdz_loc x _ _ _ hev, rdz_rd x (rdzH κ c s) q.1 (Matrix.of q.2) hH.differentiableAt,
      show ((q.1, Matrix.of q.2) : rdzPZ j) = q from rfl, hH.fderiv]
    simp
  have hS : ∀ v : ℂ, fderiv ℝ (fderiv ℝ (rdzK κ)) q (v, 0) (rdzLd x q) =
      fderiv ℝ (fderiv ℝ (rdzK κ)) q (rdzLd x q) (v, 0) := fun v => hsym _ _
  refine ⟨?_, ?_⟩
  · simp only [rdz_dz_eq]
    rw [hR, hL, hL, hS, hS]
  · simp only [rdz_dzb_eq]
    rw [hR, hL, hL, hS, hS]

end Formalism.FourierDecayAlt.P.WirtingerOperators

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.FourierDecayAlt.P.WirtingerOperators

theorem right_derivative_operator_class : WirtingerOperators.ZOpRd := by
  intro j E _ _ x
  refine ⟨fun h₁ h₂ Z h => rdz_loc x h₁ h₂ Z h, ?_, ?_, rdz_par x⟩
  · intro V h₁ h₂ hV _ c1 c2 Z hZ
    have d1 := rdz_hd x (rdz_da hV c1 hZ)
    have d2 := rdz_hd x (rdz_da hV c2 hZ)
    simp only [RdV]
    rw [d1.deriv, d2.deriv]
    exact (d1.add d2).deriv
  · intro V c h hV _ ch Z hZ
    have d := rdz_hd x (rdz_da hV ch hZ)
    simp only [RdV]
    rw [d.deriv]
    exact (d.const_smul c).deriv

theorem wirtinger_slice_smooth : WirtingerOperators.DzSlice := by
  intro j E _ _ U κ hU hK τ₀
  have hKc : ContDiffOn ℝ ∞ (rdzK κ) U := hK
  have hι : ContDiff ℝ ∞ (fun Z : MJ j => ((τ₀, Z) : rdzPZ j)) := contDiff_const.prodMk contDiff_id
  have key : ∀ c s : ℂ, ContDiffOn ℝ ∞ (fun Z : MJ j => c • (fderiv ℝ (fun τ : ℂ => κ τ Z) τ₀ 1 +
      s • fderiv ℝ (fun τ : ℂ => κ τ Z) τ₀ Complex.I)) {Z : MJ j | (τ₀, (Z : Fin j → Fin j → ℂ)) ∈ U} := by
    intro c s
    refine ((rdz_H_smooth κ c s hU hKc).comp hι.contDiffOn (fun Z hZ => hZ)).congr fun Z hZ => ?_
    exact rdz_H_eq κ c s τ₀ Z (rdz_da hU hKc hZ)
  refine ⟨?_, ?_⟩
  · simp only [rdz_dz_eq]
    exact key _ _
  · simp only [rdz_dzb_eq]
    exact key _ _

end Formalism.FourierDecayAlt.P
end
end

section
namespace Formalism.FourierDecayAlt.P

theorem z_only_of_levi_curve (hC : WirtingerOperators.CurveLevi) (hH : WirtingerOperators.HpartLevi) : LevelPointCoordinates.ZOnly :=
  WirtingerOperators.zOnly_of_parts hC hH xi_coefficient xi_coefficient_vector xiMem_statement xi_smooth
    right_derivative_operator_class wirtinger_slice_smooth

end Formalism.FourierDecayAlt.P
end

section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem block_two_apply {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D' : Matrix (Fin s) (Fin s) ℂ) (a b : Fin (p + s)) :
    U.blk2 A B' C D' a b =
      if ha : a.val < p then (if hb : b.val < p then A ⟨a, ha⟩ ⟨b, hb⟩ else B' ⟨a, ha⟩ ⟨b - p, by omega⟩)
      else (if hb : b.val < p then C ⟨a - p, by omega⟩ ⟨b, hb⟩ else D' ⟨a - p, by omega⟩ ⟨b - p, by omega⟩) := by
  simp only [U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [fsym, fsym]
  split_ifs <;> rfl

theorem w_mul_apply {d : ℕ} {ι : Type*} (M : Matrix (Fin d) ι ℂ) (a : Fin d) (b : ι) :
    (G.wMat d * M) a b = M a.rev b := by
  simp [G.wMat, Matrix.mul_apply]

theorem mul_w_apply {d : ℕ} {ι : Type*} [Fintype ι] (M : Matrix ι (Fin d) ℂ) (a : ι) (b : Fin d) :
    (M * G.wMat d) a b = M a b.rev := by
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro c _ hc; rw [if_neg]; intro h; apply hc; rw [h, Fin.rev_rev]
  · simp

theorem xcongr {j : ℕ} (x : MJ j) {a a' b b' : Fin j} (ha : a.val = a'.val) (hb : b.val = b'.val) :
    x a b = x a' b' := by
  rw [Fin.ext ha, Fin.ext hb]

theorem levi_eq {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) :
    levi k r j x = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 (k := k) (j := j + 1) (ρ := r - (j + 1)) (U.blk2 x 0 0 0) 0 0 0 0 0 0 0
        (G.wMat (j + 1) * U.blk2 (-xᴴ) 0 0 0 * G.wMat (j + 1))) := by
  ext p q
  obtain ⟨X, hX⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) p)
  obtain ⟨Y, hY⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) q)
  have hp : p.val = (U.eB k (j + 1) (r - (j + 1)) X).val := by rw [hX]; rfl
  have hq : q.val = (U.eB k (j + 1) (r - (j + 1)) Y).val := by rw [hY]; rfl
  have e : ∀ M : B.Mat k (j + 1 + (r - (j + 1))),
      D.castM (by omega : j + 1 + (r - (j + 1)) = r) M p q =
        M (U.eB k (j + 1) (r - (j + 1)) X) (U.eB k (j + 1) (r - (j + 1)) Y) := by
    intro M
    rw [hX, hY]; rfl
  rw [e, Ux4.block3_apply]
  rcases X with ((a | v) | a) <;> rcases Y with ((b | w) | b) <;>
    simp only [Ux4.block_index_first_val_eq, Ux4.block_index_middle_val_eq, Ux4.block_index_last_val_eq] at hp hq <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, levi, Matrix.of_apply, block_two_apply, w_mul_apply, mul_w_apply,
      Matrix.mul_assoc, Fin.val_rev, Matrix.neg_apply, Matrix.conjTranspose_apply] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | skip
  all_goals first
    | exact xcongr x (by simp; omega) (by simp; omega)
    | (simp only [Complex.star_def]; congr 2; exact xcongr x (by simp; omega) (by simp; omega))

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end

section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem hpk_inv' (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq (k := k) (r := r))

theorem sandwich_apply {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (u v p q : Fin N) :
    (H * Matrix.single u v (1 : ℂ) * H) p q = H p u * H v q := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

theorem hpk_col_eI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (eI k r b) = if p.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_eI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if a.val + q.val = 2 * r + k then 1 else 0 := by
  have := a.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_col_esI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (esI k r b) = if p.val = b.val then 1 else 0 := by
  have := b.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_esI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) q = if q.val = a.val then 1 else 0 := by
  have := a.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpartLevi : HpartLevi := by
  intro k r j hj a b
  have ha := a.isLt
  have hb := b.isLt
  have hcI : (starRingEnd ℂ) (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have hc2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext p q <;>
    simp only [hpart1, hpart2, hpk_inv', Matrix.conjTranspose_single, star_one, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, sandwich_apply, hpk_col_eI, hpk_row_eI, hpk_col_esI, hpk_row_esI] <;>
    simp only [levi, Matrix.of_apply, Matrix.single_apply, eI, esI, Fin.ext_iff, Fin.val_castLE, smul_eq_mul,
      Matrix.smul_apply] <;>
    split_ifs <;> first | (exfalso; omega) | skip
  all_goals first
    | (exfalso; omega)
    | (simp; done)
    | (simp [Complex.conj_I]; done)
    | (simp [Complex.conj_I]; ring; done)
    | (simp only [mul_one, mul_zero, sub_zero, zero_sub, add_zero, zero_add, map_neg, hcI, hc2, neg_neg,
        neg_mul] <;> ring)

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end

section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem castM_mul' {k a b : ℕ} (h : a = b) (g g' : B.Mat k a) :
    D.castM h (g * g') = D.castM h g * D.castM h g' := by
  simp only [D.castM, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

theorem exp_castM {k a b : ℕ} (h : a = b) (M : B.Mat k a) :
    NormedSpace.exp (D.castM h M) = D.castM h (NormedSpace.exp M) := by
  unfold D.castM; exact exp_reindex _ M

theorem exp_block_three_diagonal {k j ρ : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) (Bm : B.Mat k ρ) (C : Matrix (Fin j) (Fin j) ℂ) :
    NormedSpace.exp (U.blk3 A 0 0 0 Bm 0 0 0 C) =
      U.blk3 (NormedSpace.exp A) 0 0 0 (NormedSpace.exp Bm) 0 0 0 (NormedSpace.exp C) := by
  unfold U.blk3
  rw [exp_reindex]
  have h1 : Matrix.fromRows (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) = 0 := by
    ext i l; rcases i with i | i <;> rfl
  have h2 : Matrix.fromCols (0 : Matrix (Fin j) (Fin j) ℂ) (0 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) = 0 := by
    ext i l; rcases l with l | l <;> rfl
  rw [h1, h2, exp_fromBlocks, exp_fromBlocks]

theorem exp_block_two_diagonal {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Dd : Matrix (Fin s) (Fin s) ℂ) :
    NormedSpace.exp (U.blk2 A 0 0 Dd) = U.blk2 (NormedSpace.exp A) 0 0 (NormedSpace.exp Dd) := by
  unfold U.blk2
  rw [exp_reindex, exp_fromBlocks]

theorem symmetricScalarBlockMatrix_one_zero {p s : ℕ} : U.blk2 (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
  simp [U.blk2]

theorem block_two_identity_conjTranspose {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) :
    (U.blk2 A 0 0 (1 : Matrix (Fin s) (Fin s) ℂ))ᴴ = U.blk2 Aᴴ 0 0 1 := by
  ext a b
  simp only [Matrix.conjTranspose_apply, block_two_apply]
  split_ifs <;> simp [Matrix.one_apply, Fin.ext_iff, eq_comm]

theorem w_inv (d : ℕ) : (G.wMat d)⁻¹ = G.wMat d :=
  Matrix.inv_eq_left_inv (Ux4.wMat_mul_self d)

theorem exp_w_conj (d : ℕ) (M : Matrix (Fin d) (Fin d) ℂ) :
    NormedSpace.exp (G.wMat d * M * G.wMat d) = G.wMat d * NormedSpace.exp M * G.wMat d := by
  have hu : IsUnit (G.wMat d) := ⟨⟨G.wMat d, G.wMat d, Ux4.wMat_mul_self d, Ux4.wMat_mul_self d⟩, rfl⟩
  have e := Matrix.exp_conj (G.wMat d) M hu
  rw [w_inv] at e
  exact e

theorem block_two_exp_conjTranspose_inv {j : ℕ} (y : MJ j) :
    (U.blk2 (NormedSpace.exp y) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))ᴴ⁻¹ = U.blk2 (NormedSpace.exp (-yᴴ)) 0 0 1 := by
  rw [block_two_identity_conjTranspose]
  apply Matrix.inv_eq_left_inv
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]
  have hu : IsUnit (NormedSpace.exp yᴴ).det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  rw [Matrix.exp_neg, ← Matrix.exp_conjTranspose, Matrix.nonsing_inv_mul _ hu, symmetricScalarBlockMatrix_one_zero]

theorem exp_levi {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • levi k r j x) = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.muP k (j + 1) (r - (j + 1)) (U.blk2 (NormedSpace.exp ((t : ℂ) • x)) 0 0 1)) := by
  have hs : (t : ℂ) • levi k r j x = levi k r j ((t : ℂ) • x) := by
    ext p q
    simp only [levi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Complex.conj_ofReal]
  rw [hs, levi_eq hj, exp_castM, exp_block_three_diagonal, exp_w_conj, exp_block_two_diagonal, exp_block_two_diagonal]
  simp only [NormedSpace.exp_zero]
  unfold U.muP
  rw [block_two_exp_conjTranspose_inv]

theorem zfull_mul {j : ℕ} (Z E : MJ j) (τ : ℂ) :
    zfull Z τ * U.blk2 E 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ) = zfull (Z * E) τ := by
  unfold zfull
  rw [Ux4.symmetricScalarBlockMatrix_mul]
  simp

theorem curveLevi : CurveLevi := by
  intro k r j hj Z τ γ x t
  rw [exp_levi hj]
  unfold x0
  rw [← castM_mul', Ux4.mMap_mul_muP, zfull_mul]

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

theorem Formalism.FourierDecayAlt.P.levi_curve : Formalism.FourierDecayAlt.P.WirtingerOperators.CurveLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.curveLevi

theorem Formalism.FourierDecayAlt.P.hermitian_part_levi : Formalism.FourierDecayAlt.P.WirtingerOperators.HpartLevi := Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential.hpartLevi
end
end

section
namespace Formalism.FourierDecayAlt.P

theorem z_only : LevelPointCoordinates.ZOnly :=
  z_only_of_levi_curve levi_curve hermitian_part_levi

end Formalism.FourierDecayAlt.P
end

section
noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem head_jacquet_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : LevelPointCoordinates.HeadJ :=
  LevelPointCoordinates.headJ_of (word_induction_of_parts hHL z_only rules_closed) hB

theorem radial_head_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : KB.RadHead :=
  pb_radHead_of_headJ (head_jacquet_of_letter_and_head hHL hB)

end Formalism.FourierDecayAlt.P
end
end
