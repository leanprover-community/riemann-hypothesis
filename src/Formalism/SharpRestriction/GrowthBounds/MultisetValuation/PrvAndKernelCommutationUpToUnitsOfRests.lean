import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PrimeCastNeZero
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FormValuationGeNegDegree
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeValueEstimateOfRecordValue
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.StabilizerCount
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulUpdate
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GShiftRowGenMonomial
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AuxUOfFirstTheoremPlaceBound
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeConditionOfAdm
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SmulPsiGUp
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PositivityConditionHolds
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CommonEigenvectorThird
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RestEntOf
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FirstTheoremPlaceBound
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

structure LinD : Prop where
  Tt_add : ∀ v i j (F F' : X.Fm j), X.Tt v i j (F + F') = X.Tt v i j F + X.Tt v i j F'
  Tt_smul : ∀ v i j (a : X.G.Kf) (F : X.Fm j), X.Tt v i j (a • F) = a • X.Tt v i j F
  yv_add : ∀ v (F F' : X.Fm 0), X.yv v (F + F') = X.yv v F + X.yv v F'
  yv_smul : ∀ v (a : X.G.Kf) (F : X.Fm 0), X.yv v (a • F) = a • X.yv v F
  yv_comm : ∀ v v' (F : X.Fm 0), X.yv v (X.yv v' F) = X.yv v' (X.yv v F)

variable {X}

theorem Zop_add (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (F F' : X.Fm j) :
    X.Zop v u m j (F + F') = X.Zop v u m j F + X.Zop v u m j F' := by
  unfold Sys.Zop Sys.Ttu
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL.Tt_add, smul_add, smul_add]

theorem Zop_smul (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) (a : X.G.Kf) (F : X.Fm j) :
    X.Zop v u m j (a • F) = a • X.Zop v u m j F := by
  unfold Sys.Zop Sys.Ttu
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL.Tt_smul]
  simp only [smul_smul]
  congr 1
  ring

theorem Zop_zero (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ) : X.Zop v u m j 0 = 0 := by
  have h := Zop_smul hL v u m j 0 0
  simpa using h

variable (X)

def ZL (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (vs : List X.Pl) (F : X.Fm j) : X.Fm j :=
  vs.foldr (fun v F' => X.Zop v (u v) (m v) j F') F

def Aof (i0 : X.Pl → ℕ) (vs : List X.Pl) : ℝ := ∑ v, if v ∈ vs ∧ i0 v = 0 then (X.alEven v : ℝ) else 0

def Gen (j : ℕ) (vs : List X.Pl) : Set (X.Fm (j + 1)) :=
  {T | ∃ (a : X.G.Kf) (i0 : X.Pl → ℕ) (G' : X.Fm j), G' ∈ X.Int j ∧ (∀ v, i0 v ≤ X.G.P.r) ∧
    (∀ v, v ∉ vs → i0 v = 0) ∧ X.vGeK a (Aof X i0 vs) ∧ T = a • TtL X (j + 1) i0 vs (X.Kz j G')}

variable {X}

theorem ZL_smul (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (vs : List X.Pl) (a : X.G.Kf) (F : X.Fm j) :
    ZL X u m j vs (a • F) = a • ZL X u m j vs F := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show X.Zop v (u v) (m v) j (ZL X u m j vs (a • F)) = a • X.Zop v (u v) (m v) j (ZL X u m j vs F)
    rw [ih, Zop_smul hL]

theorem TtL_congr (j : ℕ) (i0 i0' : X.Pl → ℕ) (vs : List X.Pl) (h : ∀ v ∈ vs, i0 v = i0' v) (F : X.Fm j) :
    TtL X j i0 vs F = TtL X j i0' vs F := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    show X.Tt v (i0 v) j (TtL X j i0 vs F) = X.Tt v (i0' v) j (TtL X j i0' vs F)
    rw [h v (by simp), ih (fun w hw => h w (by simp [hw]))]

theorem Aof_update (i0 : X.Pl → ℕ) (vs : List X.Pl) (v : X.Pl) (hv : v ∉ vs) (i : ℕ) :
    Aof X (Function.update i0 v i) (v :: vs) = Aof X i0 vs + (if i = 0 then (X.alEven v : ℝ) else 0) := by
  unfold Aof
  have hs : (if i = 0 then (X.alEven v : ℝ) else 0) =
      ∑ w, if w = v ∧ i = 0 then (X.alEven w : ℝ) else 0 := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [hs, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hw : w = v
  · subst hw
    simp [hv]
  · simp [hw, Function.update_apply]

theorem Zop_gen (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (v : X.Pl) (u m : ℕ → X.G.Kf) (j : ℕ)
    (hj : j < X.mm) (hu : ∀ l ∈ Icc 1 X.mm, X.vEqK (u l) 0)
    (hc0 : ∀ l ≤ X.G.P.r, X.vGeK (X.cl v m (j + 1) l) 0)
    (hcr : X.vGeK (X.cl v m (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hv : v ∉ vs) :
    ∀ T ∈ Submodule.span X.G.O (Gen X j vs), X.Zop v u m (j + 1) T ∈ Submodule.span X.G.O (Gen X j (v :: vs)) := by
  intro T hT
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, i0, G', hG', hr, h0, ha, rfl⟩ := hx
    rw [Zop_smul hL]
    unfold Sys.Zop
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun l hl => ?_
    rw [Finset.mem_range] at hl
    apply Submodule.subset_span
    have hupd : Function.update i0 v (X.G.P.r - l) v = X.G.P.r - l := by simp
    have hTt : TtL X (j + 1) (Function.update i0 v (X.G.P.r - l)) (v :: vs) (X.Kz j G') =
        X.Tt v (X.G.P.r - l) (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G')) := by
      show X.Tt v (Function.update i0 v (X.G.P.r - l) v) (j + 1)
          (TtL X (j + 1) (Function.update i0 v (X.G.P.r - l)) vs (X.Kz j G')) = _
      rw [hupd, TtL_congr (j + 1) _ i0 vs (fun w hw => Function.update_of_ne (ne_of_mem_of_not_mem hw hv) _ _)]
    refine ⟨a * ((-1) ^ l * X.cl v m (j + 1) l * (∏ l' ∈ Icc 1 (j + 1), u l') ^ (-((X.G.P.r - l : ℕ) : ℤ))),
      Function.update i0 v (X.G.P.r - l), G', hG', ?_, ?_, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst hw
        rw [hupd]
        omega
      · rw [Function.update_of_ne hw]
        exact hr w
    · intro w hw
      rw [List.mem_cons, not_or] at hw
      rw [Function.update_of_ne hw.1]
      exact h0 w hw.2
    · rw [Aof_update i0 vs v hv (X.G.P.r - l)]
      have hU : X.vEqK (∏ l' ∈ Icc 1 (j + 1), u l') 0 :=
        vEqK_prod_units X hfr (eO_pos X v) _ _ fun l' hl' => hu l' (by
          rw [Finset.mem_Icc] at hl' ⊢
          omega)
      have hUk := (vEqK_zpow X hfr hU (-((X.G.P.r - l : ℕ) : ℤ))).1
      have hcl : X.vGeK (X.cl v m (j + 1) l) (if X.G.P.r - l = 0 then (X.alEven v : ℝ) else 0) := by
        split_ifs with h
        · have hlr : l = X.G.P.r := by omega
          rw [hlr]
          exact hcr
        · exact hc0 l (by omega)
      have key := vGeK_mul X hfr ha (vGeK_mul X hfr (vGeK_mul X hfr (vGeK_negOnePow X l) hcl) hUk)
      convert key using 1
      ring
    · rw [hTt]
      simp only [Sys.Ttu, smul_smul]
  | zero =>
    rw [Zop_zero hL]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [Zop_add hL]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul X.G.Kf a x, Zop_smul hL, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

theorem ZL_mem (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (hj : j < X.mm)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hnd : vs.Nodup)
    (G : X.Fm j) (hG : G ∈ X.Int j) :
    ZL X u m (j + 1) vs (X.Kz j G) ∈ Submodule.span X.G.O (Gen X j vs) := by
  induction vs with
  | nil =>
    apply Submodule.subset_span
    refine ⟨1, fun _ => 0, G, hG, fun _ => Nat.zero_le _, fun _ _ => rfl, ?_, ?_⟩
    · have h0 : Aof X (fun _ => 0) [] = 0 := by
        simp [Aof]
      rw [h0]
      exact vGeK_one X
    · rw [one_smul]
      rfl
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    exact Zop_gen hfr hL v (u v) (m v) j hj (hu v) (hc0 v) (hcr v) vs hnd.1 _ (ih hnd.2)

theorem ZL_bound {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y)
    (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ) (hj : j < X.mm)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v)) (vs : List X.Pl) (hnd : vs.Nodup)
    (gP : X.Pl → ℝ) (h1 : ∀ v ∈ vs, gP v ≤ X.gv v (j + 1)) (h2 : ∀ v, v ∉ vs → Y.LowAt j v (gP v))
    (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (ZL X u m (j + 1) vs (X.Kz j G)) (∑ v, gP v - X.dG j) := by
  have key : ∀ T ∈ Submodule.span X.G.O (Gen X j vs), X.vGe (j + 1) T (∑ v, gP v - X.dG j) := by
    intro T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, i0, G', hG', hr, h0, ha, rfl⟩ := hx
      obtain ⟨gQ, hgQ⟩ : ∃ f : X.Pl → ℝ,
          f = fun v => gP v - (if v ∈ vs ∧ i0 v = 0 then (X.alEven v : ℝ) else 0) := ⟨_, rfl⟩
      have hP : ∀ v, PlaceB X Y j v (i0 v) (gQ v) := by
        intro v
        by_cases hv : v ∈ vs
        · by_cases hi : i0 v = 0
          · left
            refine ⟨hi, Or.inr ?_⟩
            simp only [hgQ, hv, hi, and_self, if_true]
            linarith [h1 v hv]
          · right
            refine ⟨by omega, hr v, ?_⟩
            simp only [hgQ, hv, hi, and_false, if_false, sub_zero]
            exact h1 v hv
        · left
          refine ⟨h0 v hv, Or.inl ?_⟩
          simp only [hgQ, hv, false_and, if_false, sub_zero]
          exact h2 v hv
      have hTt := form_of_place hF hE j hj i0 vs gQ hnd hr h0 hP G' hG'
      have hsum : ∑ v, gQ v = ∑ v, gP v - Aof X i0 vs := by
        simp only [hgQ, Aof, Finset.sum_sub_distrib]
      have hs := vGe_smul X hfr ha hTt
      rw [hsum] at hs
      convert hs using 1
      ring
    | zero => exact vGe_zero X _ _
    | add x y _ _ hx hy => exact vGe_add X hx hy
    | smul a x _ hx =>
      have ha : X.vGeK (algebraMap X.G.O X.G.Kf a) 0 := (vGeK_zero_iff X).2 ((mem_intK X).2 ⟨a, rfl⟩)
      have hs := vGe_smul X hfr ha hx
      rw [zero_add, algebraMap_smul] at hs
      exact hs
  exact key _ (ZL_mem hfr hL u m j hj hu hc0 hcr vs hnd G hG)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

def yE (hL : LinD X) (v : X.Pl) : Module.End X.G.Kf (X.Fm 0) :=
  { toFun := X.yv v, map_add' := hL.yv_add v, map_smul' := fun a F => hL.yv_smul v a F }

def PE (hL : LinD X) (vs : List X.Pl) : Module.End X.G.Kf (X.Fm 0) := (vs.map (yE hL)).prod

theorem yE_comm (hL : LinD X) (v v' : X.Pl) : Commute (yE hL v) (yE hL v') :=
  LinearMap.ext fun F => hL.yv_comm v v' F

theorem yE_PE_comm (hL : LinD X) (v : X.Pl) (ws : List X.Pl) : Commute (yE hL v) (PE hL ws) := by
  apply Commute.list_prod_right
  intro y hy
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hy
  exact yE_comm hL v w

theorem PE_comm (hL : LinD X) (vs ws : List X.Pl) : Commute (PE hL vs) (PE hL ws) := by
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 hx
  exact yE_PE_comm hL v ws

theorem PE_cons (hL : LinD X) (v : X.Pl) (vs : List X.Pl) : PE hL (v :: vs) = yE hL v * PE hL vs := by
  simp [PE]

theorem PE_append (hL : LinD X) (vs ws : List X.Pl) : PE hL (vs ++ ws) = PE hL vs * PE hL ws := by
  simp [PE]

theorem PE_perm (hL : LinD X) {vs ws : List X.Pl} (h : vs.Perm ws) : PE hL vs = PE hL ws := by
  apply List.Perm.prod_eq' (h.map _)
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  obtain ⟨v, _, rfl⟩ := List.mem_map.1 ha
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hb
  exact yE_comm hL v w

theorem PE_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) :
    ∀ F ∈ S, PE hL vs F ∈ S := by
  induction vs with
  | nil => intro F hF; simpa [PE] using hF
  | cons v vs ih =>
    intro F hF
    rw [PE_cons]
    exact hy v _ (ih F hF)

theorem PE_pow_mem (hL : LinD X) {S : Set (X.Fm 0)} (hy : ∀ v, ∀ F ∈ S, X.yv v F ∈ S) (vs : List X.Pl) (n : ℕ) :
    ∀ F ∈ S, (PE hL vs ^ n) F ∈ S := by
  induction n with
  | zero => intro F hF; simpa using hF
  | succ n ih =>
    intro F hF
    rw [pow_succ']
    exact PE_mem hL hy vs _ (ih F hF)

theorem fold_eq (hL : LinD X) (n : ℕ) (vs : List X.Pl) (z : X.Fm 0) :
    vs.foldr (fun v F' => (X.yv v)^[n] F') z = (PE hL vs ^ n) z := by
  induction vs with
  | nil => simp [PE]
  | cons v vs ih =>
    rw [PE_cons, (yE_PE_comm hL v vs).mul_pow, List.foldr_cons, ih, Module.End.mul_apply,
      Module.End.pow_apply (yE hL v)]
    rfl

theorem yv_FQ (hL : LinD X) (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) (v : X.Pl) :
    ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0 := by
  intro F hF
  unfold Sys.FQ at hF ⊢
  induction hF using Submodule.span_induction with
  | zero =>
    have := hL.yv_smul v 0 0
    simp only [zero_smul] at this
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy' => rw [hL.yv_add]; exact Submodule.add_mem _ hx hy'
  | smul c x _ hx => rw [hL.yv_smul]; exact Submodule.smul_mem _ _ hx
  | mem x hx => exact Submodule.subset_span (hy v x hx)

variable (X)

def PrS (j : ℕ) (vs : List X.Pl) : ℤ :=
  ∑ v, if v ∈ vs then PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j else 0

variable {X}

theorem PrS_cons (j : ℕ) (v : X.Pl) (vs : List X.Pl) (hv : v ∉ vs) :
    PrS X j (v :: vs) = PrS X j vs + PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j := by
  unfold PrS
  have : PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j =
      ∑ v', if v' = v then PrZ X.t X.G.P.r (X.G.P.lam0 v') (X.w v') j else 0 := by
    rw [Finset.sum_ite_eq' univ v]
    simp
  rw [this, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v' _
  by_cases h : v' = v
  · subst h
    simp [hv]
  · simp [h]

theorem ZL_chain (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X) (u m : X.Pl → ℕ → X.G.Kf) (j : ℕ)
    (hCi : ∀ v, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hyQ : ∀ v, ∀ F ∈ X.FQ 0, X.yv v F ∈ X.FQ 0) (vs : List X.Pl) (hnd : vs.Nodup) (F : X.Fm 0) (hF : F ∈ X.FQ 0) :
    ZL X u m (j + 1) vs (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrS X (j + 1) vs)) • X.chainK (j + 1) (PE hL vs F) := by
  induction vs with
  | nil => simp [ZL, PrS, PE]
  | cons v vs ih =>
    rw [List.nodup_cons] at hnd
    show X.Zop v (u v) (m v) (j + 1) (ZL X u m (j + 1) vs (X.chainK (j + 1) F)) = _
    rw [ih hnd.2, Zop_smul hL, hCi v _ (PE_mem hL (S := (X.FQ 0 : Set (X.Fm 0))) hyQ vs F hF), smul_smul,
      ← zpow_add₀ hp, PrS_cons _ _ _ hnd.1, PE_cons]
    rfl

theorem vGeK_vsc (g : ℝ) : X.vGeK (X.vsc g) g := (vGeK_iff X).2 ⟨1, by simp⟩

def bbJ (X : Sys p) (Lv : List X.Pl) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool) (j : ℕ) : ℝ :=
  ∑ v, (if v ∈ Lv.filter (Q j) then Gn v (j + 1) else G0n v (j + 1)) - X.dG j -
        (PrS X (j + 1) (Lv.filter (Q j)) : ℝ)

theorem main_ind {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0) (hL : LinD X)
    (hF : FormB X Y) (hE : EntCondition X Y) (u m : X.Pl → ℕ → X.G.Kf)
    (hu : ∀ v, ∀ l ∈ Icc 1 X.mm, X.vEqK (u v l) 0)
    (hc0 : ∀ v, ∀ j < X.mm, ∀ l ≤ X.G.P.r, X.vGeK (X.cl v (m v) (j + 1) l) 0)
    (hcr : ∀ v, ∀ j < X.mm, X.vGeK (X.cl v (m v) (j + 1) X.G.P.r) (X.alEven v))
    (hCi : ∀ v, ∀ j < X.mm, ∀ F ∈ X.FQ 0, X.Zop v (u v) (m v) (j + 1) (X.chainK (j + 1) F) =
      ((p : X.G.Kf) ^ (PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) (j + 1))) • X.chainK (j + 1) (X.yv v F))
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0)
    (Lv : List X.Pl) (hnd : Lv.Nodup) (Gn G0n : X.Pl → ℕ → ℝ) (Q : ℕ → X.Pl → Bool)
    (h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1))
    (h2 : ∀ v, ∀ j < X.mm, Y.LowAt j v (G0n v (j + 1))) :
    ∀ m' ≤ X.mm, ∀ F1 ∈ X.Int 0, X.vGe m' (X.chainK m' ((PE hL Lv ^ m') F1))
      (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) := by
  intro m'
  induction m' with
  | zero =>
    intro _ F1 hF1
    simp only [pow_zero, Finset.range_zero, Finset.sum_empty]
    exact (vGe_zero_iff X).2 hF1
  | succ m' ih =>
    intro hm F1 hF1
    have hj : m' < X.mm := hm
    set B := Lv.filter (Q m') with hB
    set C := Lv.filter (fun x => !Q m' x) with hC
    have e1 : PE hL Lv = PE hL B * PE hL C := by
      rw [← PE_append]
      exact (PE_perm hL (List.filter_append_perm (Q m') Lv)).symm
    have e2 : PE hL Lv ^ (m' + 1) = PE hL B * (PE hL Lv ^ m' * PE hL C) := by
      have e0 : PE hL Lv ^ (m' + 1) = (PE hL B * PE hL C) * PE hL Lv ^ m' := by rw [pow_succ', ← e1]
      rw [e0, mul_assoc, ((PE_comm hL C Lv).pow_right m').eq]
    have hF1' : PE hL C F1 ∈ X.Int 0 := PE_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy C F1 hF1
    set W := (PE hL Lv ^ m') (PE hL C F1) with hW
    have hWi : W ∈ X.Int 0 := PE_pow_mem hL (S := (X.Int 0 : Set (X.Fm 0))) hy Lv m' _ hF1'
    have hWQ : W ∈ X.FQ 0 := Submodule.subset_span hWi
    have hBnd : B.Nodup := hnd.filter _
    have e3 := ZL_chain hp hL u m m' (fun v => hCi v m' hj) (yv_FQ hL hy) B hBnd W hWQ
    have e4 : X.chainK (m' + 1) ((PE hL Lv ^ (m' + 1)) F1) =
        ((p : X.G.Kf) ^ (-(PrS X (m' + 1) B))) • ZL X u m (m' + 1) B (X.chainK (m' + 1) W) := by
      rw [e3, smul_smul, ← zpow_add₀ hp, neg_add_cancel, zpow_zero, one_smul, e2]
      rfl
    obtain ⟨G', hG', hG'e⟩ := (vGe_iff X).1 (ih (le_of_lt hj) _ hF1')
    have e5 : X.chainK (m' + 1) W = X.vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j) • X.Kz m' G' := by
      show X.Kz m' (X.chainK m' W) = _
      rw [← hG'e, map_smul]
    rw [e4, e5, ZL_smul hL]
    have hb := ZL_bound hfr hL hF hE u m m' hj hu (fun v => hc0 v m' hj) (fun v => hcr v m' hj) B hBnd
      (fun v => if v ∈ B then Gn v (m' + 1) else G0n v (m' + 1))
      (fun v hv => by simp only [hv, if_true]; exact h1 v (List.mem_of_mem_filter hv) m' hj)
      (fun v hv => by simp only [hv, if_false]; exact h2 v m' hj) G' hG'
    have h3 := vGe_smul X hfr (vGeK_ppow X hfr (-(PrS X (m' + 1) B))) (vGe_smul X hfr (vGeK_vsc (∑ j ∈ range m', bbJ X Lv Gn G0n Q j)) hb)
    rw [Finset.sum_range_succ]
    refine vGe_mono X hfr (le_of_eq ?_) h3
    conv_lhs => rw [bbJ]
    push_cast
    ring

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem sum_Icc_shift (f : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Icc 1 m, f j = ∑ j ∈ range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_ind {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (f : ι → ℝ) :
    ∑ v ∈ A, f v = ∑ v, if v ∈ A then f v else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem basic₂ {ι : Type} [Fintype ι] [DecidableEq ι] (mm : ℕ) (VV BB : Finset ι) (hBB : BB ⊆ VV)
    (Gn G0n PRn Prr : ι → ℕ → ℝ) (S : ι → ℝ) (dG : ℕ → ℝ) (inB : ℕ → ι → Prop) [∀ j v, Decidable (inB j v)]
    (hin : ∀ j v, inB j v ↔ v ∈ BB ∧ G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    (hPR : ∀ v ∈ VV, ∀ j < mm, Prr v (j + 1) ≤ PRn v (j + 1))
    (hS : ∀ v ∈ VV, ∑ j ∈ range mm, max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 ≤ S v) :
    ∑ j ∈ range mm, (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) +
        ∑ v ∈ univ \ VV, G0n v (j + 1)) - ∑ j ∈ range mm, dG j ≤
      ∑ v ∈ VV \ BB, S v + ∑ j ∈ range mm, (∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1)) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
  have hS' : ∑ j ∈ range mm, ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0)
      ≤ ∑ v ∈ VV \ BB, S v := by
    rw [Finset.sum_comm, sum_ind (VV \ BB) S]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV \ BB
    · simp only [hv, ↓reduceIte]
      exact hS v (Finset.mem_sdiff.1 hv).1
    · simp [hv]
  have key : ∀ j ∈ range mm,
      (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) + ∑ v ∈ univ \ VV, G0n v (j + 1)) - dG j ≤
      ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
      ((∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1))) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
    intro j hj
    have hj' : j < mm := Finset.mem_range.1 hj
    suffices h : ∑ v, ((if v ∈ VV then max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) else 0) +
        (if v ∈ univ \ VV then G0n v (j + 1) else 0) + (if inB j v then Prr v (j + 1) else 0)) ≤
        ∑ v, ((if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
        (if inB j v then Gn v (j + 1) else G0n v (j + 1))) by
      rw [sum_ind VV, sum_ind (univ \ VV)]
      simp only [Finset.sum_add_distrib] at h
      linarith
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV
    · have hv2 : v ∉ univ \ VV := by simp [hv]
      by_cases hb : v ∈ BB
      · have hv3 : v ∉ VV \ BB := by simp [hb]
        by_cases hi : inB j v
        · have h1 := ((hin j v).1 hi).2
          have h2 := hPR v hv j hj'
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_left h1]
          linarith
        · have h1 : ¬ (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1)) := fun h => hi ((hin j v).2 ⟨hb, h⟩)
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_right (le_of_lt (not_le.1 h1))]
          linarith
      · have hv3 : v ∈ VV \ BB := Finset.mem_sdiff.2 ⟨hv, hb⟩
        have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
        simp only [hv, hv2, hv3, hi, ↓reduceIte]
        have hm : max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) ≤
            max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 + G0n v (j + 1) := by
          have := le_max_left (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          have := le_max_right (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          exact max_le (by linarith) (by linarith)
        linarith
    · have hv2 : v ∈ univ \ VV := by simp [hv]
      have hb : v ∉ BB := fun h => hv (hBB h)
      have hv3 : v ∉ VV \ BB := by simp [hv]
      have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
      simp only [hv, hv2, hv3, hi, ↓reduceIte]
      linarith
  have hsum := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢
  linarith

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem PrZ_cast (v : X.Pl) (j : ℕ) :
    ((PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j : ℤ) : ℝ) = X.Conclusion₂ v j := by
  simp only [Sys.Conclusion₂, PrZ, Pr]
  push_cast
  congr 1
  obtain ⟨k, hk⟩ := (X.G.P.setting v).even
  rw [hk]
  have h2 : ((k + k : ℕ) : ℤ) / 2 = (k : ℤ) := by omega
  rw [h2]
  push_cast
  ring

theorem lift_bound_of_integrality (D : Formalism.BasicNotions.D7) {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0)
    (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y) (h4 : Conclusion4 D X)
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV hG hLow hPr hS F hF
  choose u m hu hm hrest using h4
  have hπ : (algebraMap X.G.O X.G.Kf X.vp) ≠ 0 := by
    intro h0
    exact X.unif.ne_zero ((IsFractionRing.injective X.G.O X.G.Kf) (h0.trans (map_zero _).symm))
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨BB, hBB, Lv, hnd, hLv, F0, hF0, rfl⟩ := hx
    obtain ⟨F1, hF1, rfl⟩ := hF0
    let Q : ℕ → X.Pl → Bool := fun j v => decide (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    have hmemL : ∀ v, v ∈ Lv ↔ v ∈ BB := fun v => by rw [← hLv, List.mem_toFinset]
    have h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1) := fun v hv j hj =>
      hG v (hBB ((hmemL v).1 hv)) (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hmi := main_ind hfr hp hL hF hE u m hu (fun v j hj => (hrest v j hj).2.1)
      (fun v j hj => (hrest v j hj).2.2.1) (fun v j hj => (hrest v j hj).1) hy Lv hnd Gn G0n Q h1 hLow
      X.mm le_rfl F1 hF1
    have hnum : (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) ≤ ∑ v ∈ VV \ BB, S v + ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j := by
      rw [sum_Icc_shift]
      have hb := basic₂ X.mm VV BB hBB Gn G0n PRn (fun v j => X.Conclusion₂ v j) S (fun j => (X.dG j : ℝ))
        (fun j v => v ∈ Lv.filter (Q j))
        (fun j v => by simp only [List.mem_filter, hmemL, Q, decide_eq_true_eq])
        (fun v hv j hj => hPr v hv (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
        (fun v hv => by rw [← sum_Icc_shift (fun j => max (Gn v j - PRn v j - G0n v j) 0)]; exact hS v hv)
      refine hb.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bbJ, PrS]
      push_cast [PrZ_cast]
      rfl
    unfold Sys.vGe scale at hmi ⊢
    obtain ⟨I, hI, hIeq⟩ := hmi
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hIeq ⊢
    rw [fold_eq hL]
    set g := ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j with hg
    set T : ℝ := (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) with hT
    have hceil : ⌈T * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ := by
      rw [Int.ceil_le]
      push_cast
      have h8 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
      have h6 : (∑ v ∈ VV \ BB, S v) * (X.eO : ℝ) ≤ ∑ v ∈ VV \ BB, (⌈S v * (X.eO : ℝ)⌉ : ℝ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => Int.le_ceil _
      have h7 := Int.le_ceil (g * (X.eO : ℝ))
      have h9 := mul_le_mul_of_nonneg_right hnum h8
      nlinarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ - ⌈T * (X.eO : ℝ)⌉ :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨X.vp ^ n • I, Submodule.smul_mem _ _ hI, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [map_smul, map_smul, ← hIeq, ← algebraMap_smul X.G.Kf (X.vp ^ n) I, smul_smul, smul_smul]
    congr 1
    unfold Sys.vsc
    rw [map_pow, ← zpow_natCast, ← zpow_add₀ hπ, ← zpow_add₀ hπ, hn]
    congr 1
    ring
  | zero =>
    unfold Sys.vGe
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    unfold Sys.vGe at *
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    unfold Sys.vGe at *
    rw [← algebraMap_smul X.G.Kf a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section PlacesLevel

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

def RestWeylEdge : Prop :=
  ∀ (v : Fin P.nV) (i : ℕ) (L : P.Tup) (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)),
    P.IsLatTup L → IsEdge p (P.n' v) i ⟨L'', L v⟩ →
    ∀ x ∈ P.HtupW (Function.update L v L''), ((p : Kf) ^ (Ar i (P.lam0 v))) • x ∈ P.HtupW L

theorem latTup_update {L : P.Tup} (hL : P.IsLatTup L) {v : Fin P.nV}
    {A : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)} (hA : IsLattice (P.W v) A) :
    P.IsLatTup (Function.update L v A) := by
  intro u
  by_cases h : u = v
  · subst h
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L u A u = A :=
      Function.update_self u A L
    exact e.symm ▸ hA
  · have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v A u = L u :=
      Function.update_of_ne h A L
    exact e.symm ▸ hL u

theorem Tminus_mem (h : RestWeylEdge P) (v : Fin P.nV) (i : ℕ) (F : P.Tup → P.Xsp)
    (hF : ∀ L, P.IsLatTup L → F L ∈ P.HtupW L) (L : P.Tup) (hL : P.IsLatTup L) :
    ((p : Kf) ^ (Ar i (P.lam0 v))) • P.Tminus v i F L ∈ P.HtupW L := by
  rw [Tminus_eq, Finset.smul_sum]
  refine Submodule.sum_mem _ fun L'' hL'' => ?_
  have hE := (mem_EE P).1 hL''
  exact h v i L L'' hL hE _ (hF _ (latTup_update P hL hE.1))

end PlacesLevel

section Num

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ}

theorem neg_liftWt_le (h : Std p n' k1 t m c r TT a b lam0 w) (s : Fin n') (j : ℕ) (hj : j + 1 ≤ m)
    (x : Fin (k1 + (j + 1) * (t + 1) + 1)) :
    -liftWt t k1 (lam0 s) (fun l => w l s) (j + 1) x ≤ w (j + 1) s := by
  unfold liftWt
  split_ifs with hx
  · have e1 := h.dom s (Fin.le_last (⟨x.val, hx⟩ : Fin (k1 + 1)))
    have e2 := (h.w_low s).2
    have e3 := w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj
    linarith
  · rw [neg_neg]
    refine w_le h s (Nat.le_add_left 1 _) ?_ hj
    have hx2 := x.isLt
    have : (x.val - (k1 + 1)) / (t + 1) < j + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega

theorem card_filter_lt_le (N i : ℕ) : (univ.filter fun x : Fin N => x.val < i).card ≤ i := by
  have := Finset.card_le_card_of_injOn (s := univ.filter fun x : Fin N => x.val < i) (t := range i)
    (fun x => x.val) (fun x hx => by
      have hx' := (mem_filter.1 (Finset.mem_coe.1 hx)).2
      exact Finset.mem_coe.2 (mem_range.2 hx')) (fun x _ y _ hxy => Fin.ext hxy)
  rwa [card_range] at this

theorem Ar_lift_le (h : Std p n' k1 t m c r TT a b lam0 w) (j i : ℕ) (hj : j + 1 ≤ m) (hi : i ≤ k1 + 1) :
    Ar i (fun s => liftWt t k1 (lam0 s) (fun l => w l s) (j + 1)) ≤ Nprime lam0 w (j + 1) i := by
  unfold Ar Nprime
  rw [← Finset.sum_filter_not_add_sum_filter univ (fun s : Fin n' => IsOddPos s), Finset.mul_sum]
  refine add_le_add (le_of_eq ?_) ?_
  · refine Finset.sum_congr rfl fun s hs => ?_
    rw [mem_filter] at hs
    have he : Even s.val := by
      rw [Nat.even_iff]
      have := hs.2
      unfold IsOddPos at this
      omega
    refine Finset.sum_bij (fun x _ => x.val + 1) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_filter] at hx
      rw [mem_Icc]
      omega
    · intro x _ x' _ hxx
      exact Fin.ext (by omega)
    · intro y hy
      rw [mem_Icc] at hy
      exact ⟨⟨y - 1, by omega⟩, by rw [mem_filter]; exact ⟨mem_univ _, by show y - 1 < i; omega⟩,
        by show y - 1 + 1 = y; omega⟩
    · intro x hx
      rw [mem_filter] at hx
      unfold lamAt
      rw [if_pos he]
      show liftWt t k1 (lam0 s) (fun l => w l s) (j + 1) x = _
      unfold liftWt
      rw [dif_pos (by omega : x.val < k1 + 1)]
      exact (lamI_fin lam0 s ⟨x.val, by omega⟩).symm
  · refine Finset.sum_le_sum fun s hs => ?_
    rw [mem_filter] at hs
    have he : ¬ Even s.val := by
      rw [Nat.even_iff]
      have := hs.2
      unfold IsOddPos at this
      omega
    have hw0 : 0 ≤ w (j + 1) s := by
      have e2 := (h.w_low s).1
      have e3 := w_le h s (l := 1) (l' := j + 1) le_rfl (by omega) hj
      have : (0 : ℤ) ≤ c := Int.natCast_nonneg c
      linarith
    have h1 : ∑ x : Fin (k1 + (j + 1) * (t + 1) + 1) with x.val < i,
        lamAt (fun s => liftWt t k1 (lam0 s) (fun l => w l s) (j + 1)) s x ≤
        (univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card • w (j + 1) s := by
      refine Finset.sum_le_card_nsmul _ _ _ fun x _ => ?_
      unfold lamAt
      rw [if_neg he]
      exact neg_liftWt_le h s j hj x.rev
    refine le_trans h1 ?_
    rw [nsmul_eq_mul]
    have h2 : ((univ.filter fun x : Fin (k1 + (j + 1) * (t + 1) + 1) => x.val < i).card : ℤ) ≤ i := by
      exact_mod_cast card_filter_lt_le _ i
    exact mul_le_mul_of_nonneg_right h2 hw0

end Num

section SysLevel

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem TmInt {j : ℕ} (h : RestWeylEdge (X.Pj j)) (v : X.Pl) (i : ℕ) {F : X.Fm j} (hF : F ∈ X.Int j) :
    ((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v)))) • X.Tm v i j F ∈ X.Int j := by
  rw [mem_Int_iff] at hF ⊢
  exact ⟨fun c L hL => Tminus_mem (X.Pj j) h (X.vJ j v) i (F c) (hF.1 c) L hL,
    Eqv_smul X _ (restTmEquiv X j v i F hF.2)⟩

theorem p_ne_zero (v : X.Pl) : (p : X.G.Kf) ≠ 0 := Rep.ne_zero X (frac_of_place X v) (Rep.ofP X)

theorem restTmFQ_of (h : ∀ j, RestWeylEdge (X.Pj j)) : RestTmFQ X := by
  intro v i j F hF
  have hp := p_ne_zero X v
  have hle : X.FQ j ≤ (X.FQ j).comap (TmLin X v i j) := by
    refine Submodule.span_le.2 fun G hG => ?_
    show X.Tm v i j G ∈ X.FQ j
    have h1 := TmInt X (h j) v i hG
    have h2 : ((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v))))⁻¹ •
        (((p : X.G.Kf) ^ (Ar i ((X.Pj j).lam0 (X.vJ j v)))) • X.Tm v i j G) ∈ X.FQ j :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rwa [smul_smul, inv_mul_cancel₀ (zpow_ne_zero _ hp), one_smul] at h2
  exact hle hF

theorem restricted_hecke_integral_of_edges (h : ∀ j, RestWeylEdge (X.Pj j)) : HeckeIntegralLevel X := by
  intro v j hj i hi F hF
  rw [mem_Icc] at hi
  have hp := p_ne_zero X v
  unfold Sys.Tt
  rw [if_neg (by omega)]
  have h1 := TmInt X (h (j + 1)) v i hF
  have hle : Ar i ((X.Pj (j + 1)).lam0 (X.vJ (j + 1) v)) ≤ Nprime (X.G.P.lam0 v) (X.w v) (j + 1) i :=
    Ar_lift_le (X.std v) j i hj (by have := (X.std v).two_r; omega)
  obtain ⟨d, hd⟩ := Int.le.dest hle
  rw [← hd, zpow_add₀ hp, zpow_natCast, mul_comm, mul_smul]
  have e : ∀ y : X.Fm (j + 1), ((p : X.G.Kf) ^ d) • y = ((p : X.G.O) ^ d) • y := by
    intro y
    rw [← algebraMap_smul X.G.Kf ((p : X.G.O) ^ d) y, map_pow, map_natCast]
  rw [e]
  exact Submodule.smul_mem _ _ h1

end SysLevel

section EdgeProof

open Formalism.MainNotions.G.LatticeSystems MvPolynomial

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)

theorem tenV_scale (v : Fin P.nV)
    (M M' : ∀ u, Submodule O (MvPolynomial (Fin (P.n' u) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)) (c : Kf)
    (hv : ∀ F ∈ M v, c • F ∈ M' v) (hu : ∀ u, u ≠ v → M u ≤ M' u) :
    ∀ x ∈ P.tenV M, c • x ∈ P.tenV M' := by
  classical
  have key : P.tenV M ≤ (P.tenV M').comap ((LinearMap.lsmul Kf P.Xsp c).restrictScalars O) := by
    unfold Places.tenV
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    apply Submodule.subset_span
    refine ⟨Function.update F v (c • F v), ?_, ?_⟩
    · intro u
      by_cases h : u = v
      · subst h
        rw [Function.update_self]
        exact hv _ (hF u)
      · rw [Function.update_of_ne h]
        exact hu u h (hF u)
    · show c • ∏ u, P.vEmb u (F u) = ∏ u, P.vEmb u (Function.update F v (c • F v) u)
      rw [← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (F u)) (Finset.mem_univ v),
        ← Finset.mul_prod_erase Finset.univ (fun u => P.vEmb u (Function.update F v (c • F v) u))
          (Finset.mem_univ v), Function.update_self, map_smul, smul_mul_assoc]
      congr 2
      refine Finset.prod_congr rfl fun u hu' => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hu')]
  exact fun x hx => key hx

theorem pKf_ne_of_place (v : Fin P.nV) : (p : Kf) ≠ 0 := by
  have hS := P.setting v
  have := hS.frac_alt
  have h1 : (p : P.Qq v) ≠ 0 := by
    have h2 : algebraMap (P.W v) (P.Qq v) (p : P.W v) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (P.W v) (P.Qq v))).2 hS.p_unif.ne_zero
    rwa [map_natCast] at h2
  have h3 : P.ι v (p : P.Qq v) ≠ 0 := (map_ne_zero (P.ι v)).2 h1
  rwa [map_natCast] at h3

theorem la_tw_diag (v : Fin P.nV) (s i : ℕ) (g : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    la_tw (P.ι v) (P.σ v) s (g * Matrix.diagonal fun c => if c.val < i then ((p : P.Qq v))⁻¹ else 1) =
      la_tw (P.ι v) (P.σ v) s g * lb_D (P.m + 1) i (algebraMap O Kf (p : O)) := by
  unfold la_tw lb_D
  rw [map_mul]
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext c
  show (P.ι v).comp ((P.σ v ^ s : P.Qq v ≃+* P.Qq v) : P.Qq v →+* P.Qq v) (if c.val < i then ((p : P.Qq v))⁻¹ else 1) = _
  split_ifs
  · rw [map_inv₀, map_natCast, map_natCast]
  · rw [map_one]

theorem restWeylEdge : RestWeylEdge P := by
  intro v i L L'' hL hE x hx
  have hS := P.setting v
  have := hS.frac_alt
  have hinj : Function.Injective (algebraMap O Kf) := by
    have := hS.frac_O
    exact IsFractionRing.injective O Kf
  have hp := pKf_ne_of_place P v
  have hw : algebraMap O Kf (p : O) ≠ 0 := by rwa [map_natCast]
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p (P.n' v) i (P.m + 1) hS.p_unif hS.res_card
    (by have := hS.five_le; omega) (by have := hS.two_le; omega) ⟨L'', L v⟩ hE
  have hsrc' : L'' = colSpan (P.W v) g := hsrc
  have htgt' : L v = colSpan (P.W v) (g * Matrix.diagonal fun c => if c.val < i then ((p : P.Qq v))⁻¹ else 1) := htgt
  have hfrob : ∀ x : P.W v, ∃ y : P.W v, P.σ v (algebraMap (P.W v) (P.Qq v) x) = algebraMap (P.W v) (P.Qq v) y := by
    intro x
    obtain ⟨y, hy⟩ := hS.frob x
    exact ⟨_, hy⟩
  have hloc : ∀ y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L''),
      ((p : Kf) ^ (Ar i (P.lam0 v))) • y ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val (L v)) := by
    intro y hy
    have h1 := lb_tensor O Kf (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val L''))
      (fun s => Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L v)))
      (fun s => (p : Kf) ^ (∑ t : Fin (P.m + 1) with t.val < i, lamAt (P.lam0 v) s t)) (by
        intro s F hF
        rw [hsrc', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp] at hF
        rw [htgt', la_extO (P.ι v) (P.σ v) (P.j v) hfrob hS.ι_comp, la_tw_diag]
        have h2 := dl_pos O Kf hinj P.m i (lamAt (P.lam0 v) s) (p : O) hw _ (la_tw_det _ _ s.val g hg) F hF
        rwa [map_natCast] at h2 ⊢) y hy
    rw [lb_zpow_sum _ hp] at h1
    exact h1
  unfold Places.HtupW at hx ⊢
  refine tenV_scale P v _ _ _ ?_ ?_ x hx
  · intro F hF
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v = L'' :=
      Function.update_self v L'' L
    have hF' : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val L'') := by
      have h0 : F ∈ HtenW O (P.lam0 v) (fun s => extO O (P.ι v) (P.σ v) s.val
        (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' v)) := hF
      rwa [e] at h0
    exact hloc F hF'
  · intro u hu F hF
    have e : Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u = L u :=
      Function.update_of_ne hu L'' L
    have h0 : F ∈ HtenW O (P.lam0 u) (fun s => extO O (P.ι u) (P.σ u) s.val
      (Function.update (β := fun v => Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) L v L'' u)) := hF
    rwa [e] at h0

end EdgeProof

section Final

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

theorem restTmFQ : RestTmFQ X := restTmFQ_of X fun j => restWeylEdge (X.Pj j)

theorem restricted_hecke_integral : HeckeIntegralLevel X := restricted_hecke_integral_of_edges X fun j => restWeylEdge (X.Pj j)

end Final

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

theorem tsum_rat_tail (g : ℕ → ℚ) (hs : Summable (fun e => (g e : ℝ))) (E N : ℕ) (Q : ℚ) (hQ1 : 1 < Q)
    (h4 : ∀ e, E ≤ e → g (e + N) = g e / Q) : ∃ q : ℚ, ∑' e, (g e : ℝ) = q := by
  have hsE : Summable (fun i => (g (i + E) : ℝ)) := (summable_nat_add_iff E).2 hs
  have h1 := hsE.sum_add_tsum_nat_add N
  have h2 : ∀ i, (g (i + N + E) : ℝ) = (g (i + E) : ℝ) / Q := by
    intro i
    rw [show i + N + E = i + E + N by omega, h4 (i + E) (by omega)]
    push_cast
    try rfl
  simp only [h2] at h1
  rw [tsum_div_const] at h1
  have h0 := hs.sum_add_tsum_nat_add E
  have hQ0 : (Q : ℝ) ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hQ1' : (Q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Q := by exact_mod_cast hQ1
    linarith
  have hT : ∑' i, (g (i + E) : ℝ) = (∑ i ∈ range N, (g (i + E) : ℝ)) * Q / (Q - 1) := by
    rw [eq_div_iff hQ1']
    field_simp at h1
    linarith
  refine ⟨∑ i ∈ range E, g i + (∑ i ∈ range N, g (i + E)) * Q / (Q - 1), ?_⟩
  rw [← h0, hT]
  push_cast
  ring

def fqT (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) : ℚ :=
  if 2 * e + 1 ∈ Ds then 0 else max ((α : ℚ) / (P : ℚ) ^ (2 * e + 1) - (c e : ℚ)) 0

theorem fqT_cast (P : ℕ) (α : ℤ) (c : ℕ → ℤ) (Ds : Finset ℕ) (e : ℕ) :
    (if 2 * e + 1 ∈ Ds then (0 : ℝ) else max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) =
      (fqT P α c Ds e : ℝ) := by
  unfold fqT
  split_ifs
  · simp
  · push_cast
    try rfl

theorem tsum_rat (P N : ℕ) (hP : 2 ≤ P) (hN : 0 < N) (α : ℤ) (c : ℕ → ℤ) (hc : ∀ e, c (e + N) = c e)
    (Ds : Finset ℕ) :
    ∃ q : ℚ, ∑' e : ℕ, (if 2 * e + 1 ∈ Ds then (0 : ℝ) else
      max ((α : ℝ) / (P : ℝ) ^ (2 * e + 1) - (c e : ℝ)) 0) = q := by
  simp_rw [fqT_cast]
  by_cases hs : Summable (fun e => (fqT P α c Ds e : ℝ))
  swap
  · exact ⟨0, by rw [tsum_eq_zero_of_not_summable hs]; simp⟩
  have hP0 : (0 : ℚ) < P := by exact_mod_cast (by omega : 0 < P)
  have h1 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 2 * e + 1 ∉ Ds := fun e he hmem => by
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega
  have h2 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ)| * 2 < (P : ℚ) ^ (2 * e + 1) := by
    intro e he
    have a1 : α.natAbs * 2 < P ^ (2 * e + 1) :=
      calc α.natAbs * 2 < 2 * e + 1 := by omega
        _ < 2 ^ (2 * e + 1) := Nat.lt_two_pow_self
        _ ≤ P ^ (2 * e + 1) := Nat.pow_le_pow_left hP _
    have a2 : ((α.natAbs : ℕ) : ℚ) = |(α : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [← a2]
    exact_mod_cast a1
  have h2' : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → |(α : ℚ) / (P : ℚ) ^ (2 * e + 1)| < 1 / 2 := by
    intro e he
    have hpos : (0 : ℚ) < (P : ℚ) ^ (2 * e + 1) := pow_pos hP0 _
    rw [abs_div, abs_of_pos hpos, div_lt_iff₀ hpos]
    linarith [h2 e he]
  have hcK : ∀ k e, c (e + k * N) = c e := by
    intro k
    induction k with
    | zero => intro e; simp
    | succ k ih => intro e; rw [Nat.succ_mul, ← add_assoc, hc, ih]
  have h3 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e → 0 ≤ c e := by
    intro e0 he0
    by_contra hneg
    have hneg : c e0 ≤ -1 := by omega
    have tend := hs.tendsto_atTop_zero
    obtain ⟨M, hM⟩ := (tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists_forall_of_atTop
    have hge : M ≤ e0 + M * N := by nlinarith
    have hlt : (fqT P α c Ds (e0 + M * N) : ℝ) < 1 / 2 := hM _ hge
    have hlt' : fqT P α c Ds (e0 + M * N) < 1 / 2 := by
      have : (fqT P α c Ds (e0 + M * N) : ℝ) < ((1 / 2 : ℚ) : ℝ) := by push_cast; exact hlt
      exact Rat.cast_lt.1 this
    have hE1 : Ds.sup id + α.natAbs + 1 ≤ e0 + M * N := le_trans he0 (Nat.le_add_right _ _)
    unfold fqT at hlt'
    rw [if_neg (h1 _ hE1), hcK] at hlt'
    have b1 := abs_lt.1 (h2' _ hE1)
    have b2 : ((c e0 : ℤ) : ℚ) ≤ -1 := by exact_mod_cast hneg
    have b3 := le_max_left ((α : ℚ) / (P : ℚ) ^ (2 * (e0 + M * N) + 1) - (c e0 : ℚ)) 0
    linarith [b1.1]
  have h4 : ∀ e, Ds.sup id + α.natAbs + 1 ≤ e →
      fqT P α c Ds (e + N) = fqT P α c Ds e / (P : ℚ) ^ (2 * N) := by
    intro e he
    have he' : Ds.sup id + α.natAbs + 1 ≤ e + N := le_trans he (Nat.le_add_right _ _)
    unfold fqT
    rw [if_neg (h1 _ he), if_neg (h1 _ he'), hc]
    have hQ : (0 : ℚ) < (P : ℚ) ^ (2 * N) := pow_pos hP0 _
    rcases (h3 e he).eq_or_lt with h0 | h0
    · rw [← h0]
      simp only [Int.cast_zero, sub_zero]
      have : (α : ℚ) / (P : ℚ) ^ (2 * (e + N) + 1) = (α : ℚ) / (P : ℚ) ^ (2 * e + 1) / (P : ℚ) ^ (2 * N) := by
        rw [div_div, ← pow_add]
        congr 2
        ring
      rw [this, ← max_div_div_right hQ.le, zero_div]
    · have b2 : (1 : ℚ) ≤ ((c e : ℤ) : ℚ) := by exact_mod_cast h0
      have c1 := abs_lt.1 (h2' _ he)
      have c2 := abs_lt.1 (h2' _ he')
      rw [max_eq_right (by linarith [c2.2]), max_eq_right (by linarith [c1.2]), zero_div]
  have hQ1 : (1 : ℚ) < (P : ℚ) ^ (2 * N) := by
    have : (1 : ℚ) < P := by exact_mod_cast (by omega : 1 < P)
    exact one_lt_pow₀ this (by omega)
  exact tsum_rat_tail _ hs _ N _ hQ1 h4

theorem gA_rat {n' k1 : ℕ} (p t : ℕ) (hp : 2 ≤ p) (hn : 0 < n') (TT : Finset (Fin n'))
    (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ) : ∃ q : ℚ, gA p t TT lam0 w j = q := by
  have h1 : ∀ s : Fin n', ∃ q : ℚ, ∑' e : ℕ,
      (if 2 * e + 1 ∈ dSet TT s then (0 : ℝ) else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) - (cap t TT lam0 w j (posAdd s (2 * e + 1)) : ℝ)) 0) = q := by
    intro s
    apply tsum_rat p n' hp hn (al TT lam0 s) (fun e => cap t TT lam0 w j (posAdd s (2 * e + 1))) _ (dSet TT s)
    intro e
    have : posAdd s (2 * (e + n') + 1) = posAdd s (2 * e + 1) := by
      unfold posAdd
      apply Fin.ext
      show (s.val + (2 * (e + n') + 1)) % n' = (s.val + (2 * e + 1)) % n'
      have : s.val + (2 * (e + n') + 1) = s.val + (2 * e + 1) + 2 * n' := by ring
      rw [this, Nat.add_mul_mod_self_right]
    simp only [this]
  choose q hq using h1
  refine ⟨∑ s ∈ TT, q s - (∑ s : Fin n', ((NN k1 t j : ℚ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℚ) * (NN k1 t j : ℚ) * lgp p (lsz t TT lam0 w j s)) +
    ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℚ)) ^ 2), ?_⟩
  unfold gA de
  simp only [hq]
  push_cast
  ring

theorem restRat {p : ℕ} [Fact p.Prime] (X : Sys p) : RatCondition X := by
  intro v j
  have h := X.std v
  exact gA_rat p X.t (by have := h.five_le; omega) (by have := h.two_le; omega) _ _ _ j

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable {σ κ τ τ' K : Type} [Field K]

def eb_w (F : MvPowerSeries σ K) (n : σ →₀ ℕ) : K :=
  (∏ x ∈ n.support, ((n x).factorial : K)) * MvPowerSeries.coeff n F

def eb_J (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) : MvPolynomial τ K :=
  ∑ n ∈ Q.support, eb_w F n • MvPolynomial.coeff n Q

theorem eb_J_subset (F : MvPowerSeries σ K) (Q : MvPolynomial σ (MvPolynomial τ K)) (S : Finset (σ →₀ ℕ))
    (h : Q.support ⊆ S) : eb_J F Q = ∑ n ∈ S, eb_w F n • MvPolynomial.coeff n Q := by
  unfold eb_J
  apply Finset.sum_subset h
  intro n _ hn
  rw [MvPolynomial.notMem_support_iff.1 hn, smul_zero]

theorem eb_applyD (P : MvPolynomial σ (MvPolynomial τ ℤ)) (F : MvPowerSeries σ K) :
    applyD P F = eb_J F (MvPolynomial.map (MvPolynomial.map (Int.castRingHom K)) P) := by
  rw [eb_J_subset F _ P.support (MvPolynomial.support_map_subset _ _)]
  unfold applyD eb_w
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map]


theorem eb_w_mapDomain (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K) (n : κ →₀ ℕ) :
    eb_w F (n.mapDomain ε) = eb_w (resV ε F) n := by
  classical
  unfold eb_w
  rw [Finsupp.mapDomain_support_of_injective hε, Finset.prod_image (fun a _ b _ h => hε h)]
  congr 1
  apply Finset.prod_congr rfl
  intro y _
  rw [Finsupp.mapDomain_apply hε]

theorem eb_J_rename (ε : κ → σ) (hε : Function.Injective ε) (F : MvPowerSeries σ K)
    (Q : MvPolynomial κ (MvPolynomial τ K)) : eb_J F (MvPolynomial.rename ε Q) = eb_J (resV ε F) Q := by
  classical
  unfold eb_J
  rw [MvPolynomial.support_rename_of_injective hε,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hε h)]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_rename_mapDomain ε hε, eb_w_mapDomain ε hε]

theorem eb_J_map (φ : τ' → τ) (G : MvPowerSeries κ K) (Pc : MvPolynomial κ (MvPolynomial τ' K)) :
    eb_J G (MvPolynomial.map (MvPolynomial.rename φ : MvPolynomial τ' K →ₐ[K] MvPolynomial τ K).toRingHom Pc) =
      MvPolynomial.rename φ (Formalism.DworkPowerSeriesWeights.jetPairPoly Pc G) := by
  rw [eb_J_subset G _ Pc.support (MvPolynomial.support_map_subset _ _)]
  unfold Formalism.DworkPowerSeriesWeights.jetPairPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.coeff_map, map_mul, MvPolynomial.rename_C, MvPolynomial.smul_eq_C_mul, mul_comm]
  congr 2
  unfold eb_w Formalism.DworkPowerSeriesWeights.mfact Finsupp.prod
  rw [Nat.cast_prod]

end Gen

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_phi (v : X.Pl) (j : ℕ) : ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j) → X.FrI j :=
  fun y => ⟨v, ((ea_e X v).symm y.1, y.2.1.val, y.2.2)⟩

theorem eb_phi_inj (v : X.Pl) (j : ℕ) : Function.Injective (eb_phi X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [eb_phi, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, Fin.ext h2, h3]

theorem eb_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
  simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, true_and, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h1, h2, h3]

theorem eb_fac (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) (s : ea_S X v) (c : Fin (ea_colN X v j s)) :
    MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
      (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
      (Matrix.of fun (r r' : Fin (ea_hts X v j s c)) =>
        (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X
            (s, (⟨r.val, lt_of_lt_of_le r.isLt (ea_hp X v j s c)⟩ : Fin (NN X.G.P.m X.t j)), a)) *
          MvPolynomial.X (s, a, ea_Ic X v j I s c r') :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K'))).det) =
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.colFac j I v ((ea_e X v).symm s) c.val) := by
  unfold Sys.colFac
  rw [RingHom.map_det, AlgHom.map_det, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun r r' => ?_)
  change _ = MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (∑ a : Fin (NN X.G.P.m X.t j),
    MvPolynomial.C (MvPolynomial.X (⟨v, ((ea_e X v).symm s, r.val, a)⟩ : X.FrI j)) *
      MvPolynomial.X (⟨v, ((ea_e X v).symm s, a, I v ((ea_e X v).symm s) c.val r'.val)⟩ : X.ZA j))
  simp only [RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.rename_C, MvPolynomial.rename_X, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_Pc (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K') :=
  ∏ s : ea_S X v, Formalism.DworkPowerSeriesWeights.minorProd
    (fun (i : Fin (NN X.G.P.m X.t j)) (b : Fin (NN X.G.P.m X.t (j + 1))) =>
      (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K')))
    (ea_hts X v j s) (ea_hp X v j s) (ea_Ic X v j I s)

theorem eb_poly (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.PIv j I v) =
      MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
        (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
        (eb_Pc X v j K' I)) := by
  unfold Sys.PIv eb_Pc Formalism.DworkPowerSeriesWeights.minorProd
  simp only [map_prod]
  refine (Fintype.prod_equiv (ea_e X v).symm _ _ fun s => ?_).symm
  rw [Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => eb_fac X v j K' I s c

theorem eb_jet (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (F : MvPowerSeries (X.ZA j) K') (I : X.ColCh j) :
    applyD (X.PIv j I v) F = MvPolynomial.rename (eb_phi X v j)
      (Formalism.DworkPowerSeriesWeights.frameJet (ea_colN X v j) (ea_hts X v j) (ea_hp X v j) (ea_Ic X v j I) (resV (ea_eps X v j) F)) := by
  rw [eb_applyD, eb_poly, eb_J_rename _ (eb_eps_inj X v j), eb_J_map]
  rfl

theorem eb_brJet : ea_BrJet X := by
  intro v j K' _ F I n
  rw [eb_jet]
  by_cases h : ∃ n', Finsupp.mapDomain (eb_phi X v j) n' = n
  · obtain ⟨n', rfl⟩ := h
    exact Or.inr ⟨n', MvPolynomial.coeff_rename_mapDomain _ (eb_phi_inj X v j) _ n'⟩
  · exact Or.inl (MvPolynomial.coeff_rename_eq_zero _ _ _ fun u hu => absurd ⟨u, hu⟩ h)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

theorem linD (X : Sys p) : LinD X where
  Tt_add v i j F F' := by
    have := (TtLin X v i j).map_add F F'
    simp only [TtLin_apply] at this
    exact this
  Tt_smul v i j a F := by
    have := (TtLin X v i j).map_smul a F
    simp only [TtLin_apply] at this
    exact this
  yv_add v F F' := (yvLin X v).map_add F F'
  yv_smul v a F := (yvLin X v).map_smul a F
  yv_comm v v' F := funext fun i => Formalism.MainNotions.G.LatticeSystems.ef_yv_comm X.G.P v v' (F i)

variable {X : Sys p}

theorem vGe_of_eO_zero (he : X.eO = 0) {j : ℕ} {F : X.Fm j} {g g' : ℝ} (h : X.vGe j F g) : X.vGe j F g' := by
  unfold Sys.vGe Sys.vsc at h ⊢
  simpa [he] using h

theorem low_term_bound_of_eO_eq_zero_of_aux0 (D : Formalism.BasicNotions.D7) (Y : Pend X) (he : X.eO = 0) (h0 : Conclusion0 D X) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV _ _ _ _ F hFm
  have hPl : ∀ _ : X.Pl, False := fun v => by have := eO_pos X v; omega
  have hFint : F ∈ X.Int 0 := by
    unfold Sys.Iprod at hFm
    refine (Submodule.span_le.2 ?_) hFm
    rintro F' ⟨BB, _, Lv, _, _, F0, hF0, rfl⟩
    have hLv : Lv = [] := by
      cases Lv with
      | nil => rfl
      | cons v _ => exact (hPl v).elim
    subst hLv
    have h1 : F0 ∈ scale (1 : X.G.Kf) (X.Int 0) := by simpa [he] using hF0
    rw [scale_one] at h1
    exact h1
  have key : ∀ m' ≤ X.mm, X.chainK m' F ∈ X.Int m' := by
    intro m'
    induction m' with
    | zero => intro _; exact hFint
    | succ n ih =>
      intro h
      have := h0 n (by omega) _ (ih (by omega))
      exact (vGe_zero_iff X).1 (vGe_of_eO_zero he this)
  exact vGe_of_eO_zero he ((vGe_zero_iff X).2 (key X.mm le_rfl))

structure Rests (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) : Prop where

  S1 : Conclusion1 D X Y

  allPlacesExpansion : ExpansionsMultiply D X Y

  U2 : VolumeRatio₂ D X Y

  Ent : EntCondition X Y

theorem prv_and_kernel_commutation_up_to_units_of_rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) (R : Rests D X Y) :
    Conclusion₂ D X Y ∧ KernelCommutationUpToUnits D X := by
  have hF : FormB X Y := formB D X Y hA
  have hH : RestHecke X := heckeCondition_of_adm D X Y hA countLoc (restTmFQ X)
  obtain ⟨_, _, _, _, h3, h3b, _, _, _, _, _, h8, _⟩ := hA
  have p2b := hecke_integral_of_forms D hF R.Ent R.U2
  have p3 := latticeChain_succ_of_partial D hF R.Ent R.U2 (restricted_hecke_integral X)
  have pAlt := alternate_expansion_of_relations X D hH (restTmFQ X) h3b p3 p2b
  have p4 := theorem_of_alternate_form X D pAlt
  have p5D : LowTermBound D X Y := by
    rcases Nat.eq_zero_or_pos X.eO with he | he
    · exact low_term_bound_of_eO_eq_zero_of_aux0 D Y he (form_valuation_of_bound D hF h3)
    · exact lift_bound_of_integrality D (isFractionRing_of_pos_eO Y he) (pKf_ne Y) (linD X) hF R.Ent p4
        (fun v F hFm => h8.2 v F hFm)
  exact ⟨⟨form_valuation_of_bound D hF h3, R.S1, R.allPlacesExpansion, slopeEstimate_of_lemmaB_slopeLine D hF R.Ent R.U2, theorem_A_entries_of_corollary D R.Ent (restRat X) R.U2, R.U2, p2b, p3, p4,
    ramifiedLattice_of_chain_estimates D R.U2 p5D, p5D⟩, pAlt⟩

theorem rests (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Rests D X Y where
  S1 := theta_kernel_expansion D X Y hA
  allPlacesExpansion := expansions_multiply D X Y hA
  U2 := auxU_of_firstTheoremPlaceBound D (first_theorem_place_bound X Y D (restGc p) (eb_brJet X)) hA
  Ent := restEnt_of X Y D (second_lemma_place_bound X Y D (restGc p) (eb_brJet X))
    (hecke_place_bound X Y D (restGc p) (eb_brJet X)) hA

theorem packet_statements_hold (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y) : Conclusion₂ D X Y :=
  (prv_and_kernel_commutation_up_to_units_of_rests D Y hA (rests D Y hA)).1

theorem stmt_proved (D : Formalism.BasicNotions.D7) : Stmt D :=
  ⟨fun _ _ _ Y hA => packet_statements_hold D Y hA, relative_presentation_of_d7 D⟩

theorem stmtAt_proved (D : Formalism.BasicNotions.D7) : ErrorExponentStatement D :=
  fun _ _ _ _ _ Y _ hA => packet_statements_hold D Y hA


end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
