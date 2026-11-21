import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemWOfNorm

section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section W

variable {p : ℕ} [Fact p.Prime]

theorem mem_W_of_norm (i0 : K0 p →+* ℂ_[p]) (hW : ∀ x : WW p, ‖i0 (algebraMap (WW p) (K0 p) x)‖ ≤ 1) (x : K0 p)
    (hx : ‖i0 x‖ ≤ 1) : ∃ w : WW p, algebraMap (WW p) (K0 p) w = x := by
  first | exact UpperTheory.Reformulated.B.Qi32.mem_W_of_norm .. | (apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> assumption) | (apply @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x hx | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW x | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 hW | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› i0 | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p ‹_› | exact @UpperTheory.Reformulated.B.Qi32.mem_W_of_norm p

theorem cc_Ex {ι K : Type} [Field K] [CharZero K] {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) :
    constantCoeff (Ex f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_Ex hf]
  simp

theorem cc_lgE (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (iC : Kc →+* ℂ_[p])
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE) : PowerSeries.constantCoeff lgE = 0 := by
  rw [← th_log]
  exact PowerSeries.constantCoeff_subst_eq_zero (cc_pmap _ th_zero) _ (cc_pmap _ (cc_logF p))

theorem simeq_of {ι : Type} (Kc : Type) [Field Kc] [Algebra (K0 p) Kc] (Oc : Subring Kc)
    (witt_mem_integers_Cp : ∀ x : WW p, algebraMap (K0 p) Kc (algebraMap (WW p) (K0 p) x) ∈ Oc)
    (iC : Kc →+* ℂ_[p]) (iC_int : ∀ x : Kc, x ∈ Oc ↔ ‖iC x‖ ≤ 1)
    (th : PowerSeries (WW p)) (th_zero : PowerSeries.constantCoeff th = 0) (th_unit : IsUnit (PowerSeries.coeff 1 th))
    (lgE : PowerSeries ℂ_[p])
    (th_log : PowerSeries.subst
      (PowerSeries.map (iC.comp ((algebraMap (K0 p) Kc).comp (algebraMap (WW p) (K0 p)))) th)
      (PowerSeries.map (iC.comp (algebraMap (K0 p) Kc)) (logF p)) = lgE)
    (f g : MvPowerSeries ι (K0 p)) (hfg : constantCoeff (f - g) = 0)
    (h : IntegralMv (expMv (subst (diagS lgE) (map (iC.comp (algebraMap (K0 p) Kc)) (f - g))))) :
    FormalGroupSystem.Simeq p f g := by
  have : CharZero Kc := charZero_of_injective_algebraMap (algebraMap (K0 p) Kc).injective
  have hl0 := cc_lgE Kc iC th th_zero lgE th_log
  refine ⟨hfg, ?_⟩
  obtain ⟨U, hU1, hU2⟩ := K1core Kc Oc witt_mem_integers_Cp iC iC_int th th_zero th_unit lgE th_log (f - g) hfg 1 (by
    have h1 : subst (diagS lgE) (1 : MvPowerSeries ι ℂ_[p]) = 1 := by
      rw [← coe_substAlgHom (hs_dg hl0), map_one]
    rw [map_one, h1, one_mul]
    exact h)
  have hU : U = map (algebraMap (K0 p) Kc) (Ex (f - g)) := by
    have h1 : map (algebraMap (K0 p) Kc) (Ex (f - g)) * (map (algebraMap (K0 p) Kc) (expS p (-(f - g))) * U) =
        map (algebraMap (K0 p) Kc) (Ex (f - g)) := by rw [← hU1, mul_one]
    rw [expS_eq_Ex p (by rw [map_neg, hfg, neg_zero]), ← mul_assoc, ← map_mul, mul_comm (Ex (f - g)), Ex_neg_mul hfg,
      map_one, one_mul] at h1
    exact h1
  have e0 : constantCoeff (inParam p (f - g)) = 0 :=
    constantCoeff_subst_eq_zero (hs_dg (cc_logF p)) (cc_dg (cc_logF p)) hfg
  have hP : inParamK p Kc U = map (algebraMap (K0 p) Kc) (expS p (inParam p (f - g))) := by
    rw [expS_eq_Ex p e0, hU]
    show subst (diagS (PowerSeries.map (algebraMap (K0 p) Kc) (logF p))) (map (algebraMap (K0 p) Kc) (Ex (f - g))) =
      map (algebraMap (K0 p) Kc) (Ex (subst (diagS (logF p)) (f - g)))
    rw [← subst_Ex (hs_dg (cc_logF p)) hfg, map_subst (hs_dg (cc_logF p))]
    congr 1
    funext i
    rw [map_dg]
  have hm : ∀ n, ∃ w : WW p, algebraMap (WW p) (K0 p) w = coeff n (expS p (inParam p (f - g))) := fun n =>
    mem_W_of_norm (iC.comp (algebraMap (K0 p) Kc)) (fun x => (iC_int _).mp (witt_mem_integers_Cp x)) _ (by
      have h3 := hU2 n
      rw [hP, coeff_map] at h3
      exact (iC_int _).mp h3)
  choose G hG using hm
  let Gs : MvPowerSeries ι (WW p) := G
  have hGs : map (algebraMap (WW p) (K0 p)) Gs = expS p (inParam p (f - g)) := by
    ext n
    rw [coeff_map]
    exact hG n
  refine ⟨Gs - 1, ?_, ?_⟩
  · have h4 : algebraMap (WW p) (K0 p) (constantCoeff Gs) = 1 := by
      rw [← constantCoeff_map, hGs, expS_eq_Ex p e0, cc_Ex e0]
    rw [map_sub, map_one, sub_eq_zero]
    exact IsFractionRing.injective (WW p) (K0 p) (by rw [h4, map_one])
  · rw [map_sub, map_one, add_sub_cancel, hGs]

end W

end Formalism.MainNotions.J
end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Be

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ τ : Type}

theorem lg_pt (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hax : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  have hae : PowerSeries.HasSubst g.ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply hae hax, hinv, PowerSeries.subst_X hax]

variable (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p])

theorem be_at (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {a b : MvPowerSeries τ ℂ_[p]} (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) :
    subst ![C ep * g.lg a, C ep * g.lg b] (map i0 be) = g.be a b := by
  have hlg : ∀ {σ' : Type} {c : σ' → MvPowerSeries τ ℂ_[p]}, HasSubst c → ∀ i : σ',
      subst c (C ep * g.lg (X i)) = C ep * g.lg (c i) := by
    intro σ' c hc i
    have hXi : HasSubst (fun _ : Unit => (X i : MvPowerSeries σ' ℂ_[p])) :=
by
      have hz : ∀ _ : Unit, constantCoeff (X i : MvPowerSeries σ' ℂ_[p]) = 0 := fun _ => constantCoeff_X i
      first
        | exact hasSubst_of_constantCoeff_zero hz
        | exact HasSubst.of_constantCoeff_zero' hz
        | exact hasSubst_of_constantCoeff_nilpotent (fun j => by rw [hz j]; exact IsNilpotent.zero)
    rw [← smul_eq_C_mul, subst_smul hc, ← smul_eq_C_mul]
    congr 1
    unfold G1.lg PowerSeries.subst
    rw [subst_comp_subst_apply hXi hc]
    simp only [subst_X hc]
  have h0 : ∀ i : Fin 2, constantCoeff (![a, b] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hc : HasSubst ![a, b] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have hl0 : ∀ i : Fin 2, constantCoeff (g.lg (X i : MvPowerSeries (Fin 2) ℂ_[p])) = 0 := fun i =>
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_X i) _ (cc_l g)
  have h1 : ∀ i : Fin 2, constantCoeff
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i) = 0 := by
    intro i; fin_cases i <;> simp [hl0]
  have hd : HasSubst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] := by
    first
      | exact hasSubst_of_constantCoeff_zero h1
      | exact HasSubst.of_constantCoeff_zero' h1
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h1 i]; exact IsNilpotent.zero)
  have h := congrArg (subst ![a, b]) be_tie
  rw [be_subst g hex hc (constantCoeff_X _) (constantCoeff_X _), subst_X hc, subst_X hc,
    subst_comp_subst_apply hd hc] at h
  have hfun : (fun i => subst ![a, b]
      (![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] i)) = ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hlg hc 0
    · exact hlg hc 1
  rw [hfun] at h
  simpa using h

def LogOf (x : MvPowerSeries τ (K0 p)) (a : MvPowerSeries τ ℂ_[p]) : Prop :=
  constantCoeff x = 0 ∧ constantCoeff a = 0 ∧
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 x) = C ep * g.lg a

theorem logOf_X (i : τ) : LogOf g i0 ep (X i) (X i) := by
  refine ⟨constantCoeff_X i, constantCoeff_X i, ?_⟩
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  rw [map_X, subst_X (hs_dg hc), dg_Cmul]

theorem logOf_add (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) : LogOf g i0 ep (x + y) (g.add a b) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hlb : constantCoeff (g.lg b) = 0 := PowerSeries.constantCoeff_subst_eq_zero hb0 _ (cc_l g)
  have hs : constantCoeff (g.lg a + g.lg b) = 0 := by rw [map_add, hla, hlb, add_zero]
  refine ⟨by rw [map_add, hx0, hy0, add_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_add, subst_add (hs_dg hc), hx1, hy1, G1.add, lg_pt g hex hinv hs, mul_add]

theorem logOf_mul (hex : PowerSeries.constantCoeff g.ex = 0)
    (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X) (c : K0 p) {x : MvPowerSeries τ (K0 p)}
    {a : MvPowerSeries τ ℂ_[p]} (hx : LogOf g i0 ep x a) : LogOf g i0 ep (C c * x) (g.mulBy (i0 c) a) := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have hla : constantCoeff (g.lg a) = 0 := PowerSeries.constantCoeff_subst_eq_zero ha0 _ (cc_l g)
  have hs : constantCoeff (C (i0 c) * g.lg a) = 0 := by rw [map_mul, hla, mul_zero]
  refine ⟨by rw [map_mul, hx0, mul_zero], ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hs _ hex
  · rw [map_mul, map_C, ← smul_eq_C_mul, subst_smul (hs_dg hc), hx1, G1.mulBy, lg_pt g hex hinv hs,
      smul_eq_C_mul]
    ring

theorem subtraction_formal_group_log (hex : PowerSeries.constantCoeff g.ex = 0)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    {x y : MvPowerSeries τ (K0 p)} {a b : MvPowerSeries τ ℂ_[p]}
    (hx : LogOf g i0 ep x a) (hy : LogOf g i0 ep y b) :
    subst (diagS (PowerSeries.C ep * g.l)) (map i0 (sub2 p be x y)) = g.be a b := by
  obtain ⟨hx0, ha0, hx1⟩ := hx
  obtain ⟨hy0, hb0, hy1⟩ := hy
  have hc : PowerSeries.constantCoeff (PowerSeries.C ep * g.l) = 0 := by
    rw [map_mul, cc_l, mul_zero]
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  have h0' : ∀ i : Fin 2, constantCoeff (map i0 (![x, y] i)) = 0 := by
    intro i; rw [constantCoeff_map, h0 i, map_zero]
  have hs' : HasSubst (fun i : Fin 2 => map i0 (![x, y] i)) := by
    first
      | exact hasSubst_of_constantCoeff_zero h0'
      | exact HasSubst.of_constantCoeff_zero' h0'
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0' i]; exact IsNilpotent.zero)
  unfold sub2
  rw [map_subst hs, subst_comp_subst_apply hs' (hs_dg hc)]
  have hfun : (fun i : Fin 2 => subst (diagS (PowerSeries.C ep * g.l)) (map i0 (![x, y] i))) =
      ![C ep * g.lg a, C ep * g.lg b] := by
    funext i
    fin_cases i
    · exact hx1
    · exact hy1
  rw [hfun]
  exact be_at g i0 be ep hex be_tie ha0 hb0

theorem constantCoeff_sub2_eq_zero (hbe : constantCoeff be = 0) {x y : MvPowerSeries τ (K0 p)} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : constantCoeff (sub2 p be x y) = 0 := by
  have h0 : ∀ i : Fin 2, constantCoeff (![x, y] i) = 0 := by
    intro i; fin_cases i <;> simpa
  have hs : HasSubst ![x, y] := by
    first
      | exact hasSubst_of_constantCoeff_zero h0
      | exact HasSubst.of_constantCoeff_zero' h0
      | exact Formalism.G.LogP.hs2 hx hy
      | exact hasSubst_of_constantCoeff_nilpotent (fun i => by rw [h0 i]; exact IsNilpotent.zero)
  unfold sub2
  first
    | exact constantCoeff_subst_eq_zero hs h0 hbe
    | exact constantCoeff_subst_eq_zero h0 hbe
    | exact MvPowerSeries.constantCoeff_subst_eq_zero hs h0 hbe

end Be

end Formalism.MainNotions.J
end
end

section
noncomputable section

namespace Formalism.MainNotions.J

open MvPowerSeries Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta NumberField

section Ab

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

theorem cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
  rw [Formalism.MainNotions.GL3Theta.G1.ph.eq_1, map_neg, neg_eq_zero]
  show Formalism.MainNotions.GL3Theta.logMv _ 0 = 0
  rw [Formalism.MainNotions.GL3Theta.logMv.eq_1]
  simp

theorem be_ab (i0 : K0 p →+* ℂ_[p]) (be : MvPowerSeries (Fin 2) (K0 p)) (ep : ℂ_[p]) (hep : ep ≠ 0)
    (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    (be_tie : subst ![C ep * g.lg (X (0 : Fin 2)), C ep * g.lg (X (1 : Fin 2))] (map i0 be) =
      g.be (X (0 : Fin 2)) (X (1 : Fin 2)))
    (n : Fin 2 →₀ ℕ) (hn : coeff n be ≠ 0) : 1 ≤ n 0 ∧ 1 ≤ n 1 := by
  classical
  set c : ℂ_[p] := ep⁻¹ with hc
  set ψ : PowerSeries ℂ_[p] :=
    PowerSeries.subst (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) g.ph with hψ
  have hcX : PowerSeries.constantCoeff (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) = 0 := by simp
  have hE : PowerSeries.constantCoeff (PowerSeries.subst (PowerSeries.C c * PowerSeries.X : PowerSeries ℂ_[p]) g.ex) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hcX _ hex
  have hψ0 : PowerSeries.coeff 0 ψ = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.constantCoeff_subst_eq_zero hE _ (cc_ph g)
  have key : ∀ z : MvPowerSeries (Fin 2) ℂ_[p], constantCoeff z = 0 →
      g.phAt (g.pt (C c * z)) = PowerSeries.subst z ψ := by
    intro z hz
    have hz' := PowerSeries.HasSubst.of_constantCoeff_zero hz
    rw [hψ, PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hE) hz',
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hcX) hz',
      PowerSeries.subst_mul hz', PowerSeries.subst_C, PowerSeries.subst_X hz']
    rfl
  have h0 : ∀ i : Fin 2, constantCoeff (C c * X i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by intro i; simp
  have hB : map i0 be = PowerSeries.subst (X 0 + X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) ℂ_[p]) ψ -
      PowerSeries.subst (X 1 : MvPowerSeries (Fin 2) ℂ_[p]) ψ := by
    have h := be_at g i0 be ep hex be_tie (cc_pt g hex (h0 0)) (cc_pt g hex (h0 1))
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1)] at h
    have e : (![C ep * (C c * X 0), C ep * (C c * X 1)] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[p]) = X := by
      funext s
      fin_cases s
      · show C ep * (C c * X 0) = X 0
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
      · show C ep * (C c * X 1) = X 1
        rw [← mul_assoc, ← map_mul, hc, mul_inv_cancel₀ hep, map_one, one_mul]
    rw [e, subst_self] at h
    have h' : map i0 be = g.be (g.pt (C c * X 0)) (g.pt (C c * X 1)) := h
    rw [h']
    unfold G1.be G1.add
    rw [lg_pt g hex hinv (h0 0), lg_pt g hex hinv (h0 1), ← mul_add, key _ (by simp), key _ (by simp),
      key _ (by simp)]
  have hco : i0 (coeff n be) = ((n 0 + n 1).choose (n 0) : ℂ_[p]) * PowerSeries.coeff (n 0 + n 1) ψ -
      (if n = Finsupp.single 0 (n 0) then PowerSeries.coeff (n 0) ψ else 0) -
      (if n = Finsupp.single 1 (n 1) then PowerSeries.coeff (n 1) ψ else 0) := by
    rw [← coeff_map, hB, map_sub, map_sub, PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_single,
      PowerSeries.coeff_subst_single]
  by_contra hcon
  apply hn
  apply i0.injective
  rw [map_zero, hco]
  have hcase : n 0 = 0 ∨ n 1 = 0 := by
    by_contra h
    push Not at h
    exact hcon ⟨Nat.one_le_iff_ne_zero.2 h.1, Nat.one_le_iff_ne_zero.2 h.2⟩
  rcases hcase with h | h
  · have e1 : n = Finsupp.single 1 (n 1) := by
      ext i
      fin_cases i
      · simp [h]
      · simp
    rw [if_pos e1, h, zero_add, Nat.choose_zero_right, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 1 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring
  · have e1 : n = Finsupp.single 0 (n 0) := by
      ext i
      fin_cases i
      · simp
      · simp [h]
    rw [if_pos e1, h, add_zero, Nat.choose_self, Nat.cast_one, one_mul]
    split_ifs with h2
    · have : n 0 = 0 := by rw [h2]; simp
      rw [this, hψ0]; ring
    · ring

end Ab

variable {D : D7} {Gt : GatTies D} {Tw : TwForms D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
    [Fact (D.what₂.places.resChar w).Prime] {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
    {T : Formalism.MainNotions.TaylorLogMetric.Tor D} {e : Formalism.MainNotions.TaylorLogMetric.FamE D} {X : Sys (D.what₂.places.resChar w)} {Y : Pend X}

end Formalism.MainNotions.J
end
end
