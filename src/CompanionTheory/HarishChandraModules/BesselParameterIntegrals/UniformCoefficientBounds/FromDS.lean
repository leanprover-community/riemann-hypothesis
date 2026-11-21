import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.InfinitesimalDecay.DecBoundOfCompact
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNormDegGCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJmuFacts
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.CoefBoundUniform

section
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.Coef

open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Deriv

variable {k r : ℕ} {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {G : Set (B.Mat k r)} {σ : B.Mat k r → (H →L[ℂ] H)}

def cf (σ : B.Mat k r → (H →L[ℂ] H)) (x₀ : E) (a b : H) (g : B.Mat k r) : E := ⟪a, σ g b⟫_ℂ • x₀

theorem rw_cf (h : RepOn G σ) (x₀ : E) (a : H) {b : H} (hb : IsSm G σ b) :
    ∀ {v : List (B.Mat k r)}, LieW G v → ∀ g ∈ G,
      B.Rw v (cf σ x₀ a b) g = cf σ x₀ a (dsW σ v b) g
  | [], _, _, _ => rfl
  | X :: v, hv, g, hg => by
    have hv' : LieW G v := fun Y hY => hv Y (List.mem_cons_of_mem _ hY)
    have hX := hv X List.mem_cons_self
    change deriv (fun t : ℝ => B.Rw v (cf σ x₀ a b) (g * ex X t)) 0 = _
    have e : (fun t : ℝ => B.Rw v (cf σ x₀ a b) (g * ex X t)) =
        fun t => ⟪a, σ g (σ (ex X t) (dsW σ v b))⟫_ℂ • x₀ := by
      ext1 t
      rw [rw_cf h x₀ a hb hv' _ (h.mul_mem _ hg _ (hX t)), cf, h.apply_mul hg (hX t)]
    rw [e]
    have h1 := ((hb.dsW h hv').differentiableAt h hX).hasDerivAt
    let L : H →L[ℝ] E := (((innerSL ℂ a).comp (σ g)).smulRight x₀).restrictScalars ℝ
    exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1).deriv

theorem lw_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a : H}
    (ha : IsSm G σ a) (b : H) {f : B.Mat k r → E} (hf : ∀ g ∈ G, f g = cf σ x₀ a b g) :
    ∀ {u : List (B.Mat k r)}, LieW G u → ∀ g ∈ G,
      u.foldr B.LdV f g = cf σ x₀ (dsW σ u a) b g
  | [], _, g, hg => hf g hg
  | X :: u, hu, g, hg => by
    have hu' : LieW G u := fun Y hY => hu Y (List.mem_cons_of_mem _ hY)
    have hX := hu X List.mem_cons_self
    change deriv (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0 = _
    have e : (fun t : ℝ => u.foldr B.LdV f (NormedSpace.exp (-((t : ℂ) • X)) * g)) =
        fun t => ⟪σ (ex X t) (dsW σ u a), σ g b⟫_ℂ • x₀ := by
      ext1 t
      have e1 : NormedSpace.exp (-((t : ℂ) • X)) = ex X (-t) := by simp [ex]
      rw [e1, lw_cf h hiso x₀ ha b hf hu' _ (h.mul_mem _ (hX _) _ hg), cf]
      let I : H →ₗᵢ[ℂ] H := ⟨σ (ex X t), hiso _ (hX t)⟩
      rw [← I.inner_map_map]
      change ⟪σ (ex X t) _, σ (ex X t) (σ (ex X (-t) * g) b)⟫_ℂ • x₀ = _
      rw [← h.apply_mul (hX t) (h.mul_mem _ (hX _) _ hg), ← Matrix.mul_assoc, ← ex_add,
        add_neg_cancel, ex_zero, Matrix.one_mul]
    rw [e]
    have h1 := ((ha.dsW h hu').differentiableAt h hX).hasDerivAt
    have h2 := (h1.inner ℂ (hasDerivAt_const (0 : ℝ) (σ g b))).smul_const x₀
    rw [h2.deriv]
    simp [cf, dsW_cons, ds]

theorem dLR_cf (h : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (x₀ : E) {a b : H}
    (ha : IsSm G σ a) (hb : IsSm G σ b) {u v : List (B.Mat k r)} (hu : LieW G u) (hv : LieW G v)
    {g : B.Mat k r} (hg : g ∈ G) :
    B.dLR u v (cf σ x₀ a b) g = cf σ x₀ (dsW σ u a) (dsW σ v b) g :=
  lw_cf h hiso x₀ ha _ (rw_cf h x₀ a hb hv) hu g hg

end Deriv

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq]

end CompanionTheory.D.Upq.Coef

end
end

section
open Matrix MeasureTheory Set
open scoped ContDiff InnerProductSpace ENNReal

noncomputable section

namespace CompanionTheory.D.Upq.Coef

open CompanionTheory.D.Upq.Sm Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inCC_cf_of_dec (hK : PI.KFinSmooth) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {lam : Fin (2 * r + k + 1) → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mx k r → (H →L[ℂ] H)}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {w : H}
    (hw : PI.UpqRep.IsKFinHpk (k := k) (r := r) σ w) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x₀ : E) {A : ℝ}
    (hdec : ∀ a ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∀ b ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪a, σ g b⟫_ℂ‖ ≤ C) (m : ℕ) :
    B.InCC A m (cf σ x₀ w w) := by
  obtain ⟨P, ⟨⟨hP, hPJ⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hiso, -⟩, -⟩ := id hσ
  obtain ⟨hc1, -⟩ := conj_facts hP hPJ
  have hG : PI.IsMatGroup (B.GV k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hrep : RepOn (B.GV k r) σ := repOn_of_conj hP hPJ h1 hm
  have hiso' : ∀ g ∈ B.GV k r, ∀ v, ‖σ g v‖ = ‖v‖ := fun g hg v => by
    obtain ⟨b, hb, rfl⟩ := hc1 g hg
    exact hiso b hb v
  obtain ⟨S, hS, hwS, hSK⟩ := hw
  have hT : GoodSub (B.GV k r) (B.GV k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set _))
      σ S := ⟨hS, fun v hv => hK k r ε lam H σ hlam hσ v ⟨S, hS, hv, hSK⟩, hSK⟩
  have hws := hT.sm w hwS
  obtain ⟨T, C, hT', hC, hW⟩ := hT.words hG hrep inter_subset_left hwS m
  haveI := hT'.fin
  obtain ⟨C', hC', hb⟩ := coef_bound_uniform (G := B.GV k r) (σ := σ) (T := T)
    (ρ := fun g => B.gN g ^ (-A)) (fun g _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    (fun a ha b hb => by
      obtain ⟨C, hd⟩ := hdec a (hT'.sm a ha) b (hT'.sm b hb)
      refine ⟨C, fun g hg => ?_⟩
      have hg0 : 0 < B.gN g := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
      rw [Real.rpow_neg hg0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hg0 _), mul_comm]
      exact hd g hg)
  refine ⟨C' * C * C * ‖x₀‖, fun g₀ hg₀ => ?_, fun u v hu hv huv g hg => ?_⟩
  · obtain ⟨U, F, hU, hgU, hF, hfF⟩ :=
      SmOn.clm hws (((innerSL ℂ w).smulRight x₀).restrictScalars ℝ) g₀ hg₀
    exact ⟨U, F, hU, hgU, hF.of_le (by exact_mod_cast le_top), hfF⟩
  · have hlie : ∀ W : List (B.Mat k r), (∀ X ∈ W, B.unitLie k r X) →
        LieW (B.GV k r) W ∧ ∀ X ∈ W, ‖X‖ ≤ 1 := fun W hW =>
      ⟨fun X hX t => ex_mem_of_lie (hW X hX).1 t,
        fun X hX => (Matrix.norm_le_iff zero_le_one).2 (hW X hX).2⟩
    obtain ⟨hu1, hu2⟩ := hW u (hlie u hu).1 (hlie u hu).2 (by omega)
    obtain ⟨hv1, hv2⟩ := hW v (hlie v hv).1 (hlie v hv).2 (by omega)
    rw [dLR_cf hrep hiso' x₀ hws hws (hlie u hu).1 (hlie v hv).1 hg, cf, norm_smul]
    have hg1 : 1 ≤ B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
    have h2 := hb _ hu1 _ hv1 g hg
    have h3 : B.gN g ^ A * B.gN g ^ (-A) ≤ 1 := by
      rw [← Real.rpow_add (by linarith)]
      simp
    have h4 : 0 ≤ B.gN g ^ A := Real.rpow_nonneg (by linarith) _
    have h5 : 0 ≤ B.gN g ^ (-A) := Real.rpow_nonneg (by linarith) _
    calc _ ≤ B.gN g ^ A * (C' * C * C * B.gN g ^ (-A) * ‖x₀‖) := by
          gcongr
          exact h2.trans (by gcongr)
      _ = (B.gN g ^ A * B.gN g ^ (-A)) * (C' * C * C * ‖x₀‖) := by ring
      _ ≤ _ := mul_le_of_le_one_left (by positivity) h3

theorem coef_eq_cf {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (μG : Measure (Formalism.QuantumDeterminants.Mt k r))
    (A : JDat k r Wp Wq) : A.coef μG = cf A.σ (((A.scal μG : ℝ) : ℂ) •
      (innerSL ℂ (A.l' A.w0)).smulRight (A.l A.w0)) A.w0 A.w0 := by
  ext g x
  simp only [JDat.coef, cf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_smul]
  congr 1
  ring

end CompanionTheory.D.Upq.Coef

end
end

section
open Matrix MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.Coef

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu Formalism.FourierDecayAlt.P.CutBP.Jmu.NDG ReciprocityTheory.ChartRestriction.DS

theorem thrStar_le {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) : thrStar ε ≤ 32 * (n : ℝ) ^ 3 := by
  have hp : pOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hq : qOf ε ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have h0 : S7.q0 ε ≤ n := by unfold S7.q0; omega
  have hp' : (pOf ε : ℝ) ≤ n := by exact_mod_cast hp
  have hq' : (qOf ε : ℝ) ≤ n := by exact_mod_cast hq
  have h0' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast h0
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) ≤ n ^ 3 := le_self_pow₀ h1 (by norm_num)
  have h3 : (n : ℝ) ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
  refine max_le ?_ ?_
  · have : (n : ℝ) * pOf ε * qOf ε ≤ n * n * n := by gcongr
    nlinarith
  · have h4 : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n :=
      Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    have h5 : 16 * (n : ℝ) * S7.q0 ε ≤ 16 * n * n := by gcongr
    nlinarith

theorem dsigW_SK {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mx k r → (H →L[ℂ] H)) : ∀ (W : List (Mx k r)) (v : H),
    Formalism.MainNotions.S.dsigW (k := k) (r := r) σ W v = PI.UpqRep.dsigW (k := k) (r := r) σ W v
  | [], _ => rfl
  | X :: W, v => by
    change Formalism.MainNotions.S.dsig σ X (Formalism.MainNotions.S.dsigW σ W v) = PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ W v)
    rw [dsigW_SK σ W v]; rfl

theorem decay_infinite_range : DecInf := by
  intro k r ε lam h H _ _ _ σ hlam hσ hgap hok v0 hv0
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast by omega)
  have hh := hok.2.1
  have ht := thrStar_le (n := 2 * r + k + 1) (by omega) ε
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * ((r : ℝ) + 1)) :=
    Real.one_le_sqrt.2 (by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith)
  have ha0 : 0 ≤ aOf r h := div_nonneg (by linarith) (by positivity)
  have ha : aOf r h ≤ h / 8 := div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith)
  have hm : thrStar ε + (⌊aOf r h⌋₊ : ℕ) < h := by
    have := Nat.floor_le ha0
    linarith
  obtain ⟨C, Ws, hWs, hC⟩ := DecInf.decSm hlam hgap _ hm (σ := σ) hσ
  have hv0s := CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam H σ hlam hσ v0 hv0
  set N := (Ws.map fun w => ‖Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v0‖).sum
  refine ⟨|C * N|, Ws, fun W hW => (hWs W hW).2, fun w hw x hx => ?_⟩
  have h1 := hC w hw v0 hv0s x hx
  simp only [dsigW_SK] at h1
  set M := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) σ W w‖).sum
  have hM : 0 ≤ M := List.sum_nonneg fun t ht => by
    obtain ⟨W, -, rfl⟩ := List.mem_map.1 ht
    exact norm_nonneg _
  have hg1 : 1 ≤ B.gN x := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx
  have h2 : B.gN x ^ (aOf r h - 1) ≤ B.gN x ^ (⌊aOf r h⌋₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hg1 (Nat.sub_one_lt_floor _).le
  have h3 : B.gN x ^ (aOf r h - 1) * ‖⟪v0, σ x w⟫_ℂ‖ ≤ |C * N| * M := by
    refine (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans (h1.trans ?_)
    have e : N = (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w v0‖).sum := by
      simp only [N, dsigW_SK]
    rw [← e, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hM
  rw [← neg_sub, Real.rpow_neg (by linarith), ← div_eq_mul_inv,
    le_div_iff₀ (Real.rpow_pos_of_pos (by linarith) _), mul_comm]
  exact h3

theorem capelli_coefficient_continuity : CoefCC := by
  intro hK k r Wp Wq _ _ _ _ _ _ Bs ε lam h u u' νq νq' A hG
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast by omega)
  have hh := hG.1.2.2.2.1.2.1
  have ht := thrStar_le (n := 2 * r + k + 1) (by omega) ε
  have hm : thrStar ε + (64 * (2 * r + k + 1) ^ 3 : ℕ) < h := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    linarith
  obtain ⟨C, Ws, -, hC⟩ := DecInf.decSm hG.1.1 hG.1.2.2.1 _ hm (σ := A.σ) hG.1.2.1
  rw [coef_eq_cf]
  exact inCC_cf_of_dec hK hG.1.1 hG.1.2.1 (lowest_unit_vector_is_K_finite hG) _ (fun a ha b hb => ⟨_, fun g hg =>
    (congrArg (· * _) (Real.rpow_natCast _ _)).trans_le (hC b hb a ha g hg)⟩) 5

end CompanionTheory.D.Upq.Coef

end
end
