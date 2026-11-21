import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFactorDepthInChartChartIndependent
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RelatedMap
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0EqSumOfSubset
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffInvariantOperatorAlongMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalBiextensionIntegralChartValuedExtens
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

section
open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_lipschitz_eval {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (Q : MvPolynomial ι C) :
    ∃ K : ℝ, (∀ a : ι → C, (∀ i, IsIntV v (a i)) →
        ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q)) ∧
      ∀ (M : ℝ) (a a' : ι → C), (∀ i, IsIntV v (a i)) → (∀ i, IsIntV v (a' i)) →
        (∀ i, ((M : ℝ) : WithTop ℝ) ≤ v (a i - a' i)) →
        ((M - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q - MvPolynomial.eval a' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    by_cases hc : v c = ⊤
    · exact ⟨0, fun a _ => by simp [hc], fun M a a' _ _ _ => by simp⟩
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
      exact ⟨-r, fun a _ => by simp [hr], fun M a a' _ _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨K₁, h₁, h₁'⟩ := hp
    obtain ⟨K₂, h₂, h₂'⟩ := hq
    refine ⟨max K₁ K₂, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_add]
      refine v.map_le_add (le_trans ?_ (h₁ a ha)) (le_trans ?_ (h₂ a ha))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_left _ _))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_right _ _))
    · rw [map_add, map_add, add_sub_add_comm]
      refine v.map_le_add (le_trans ?_ (h₁' M a a' ha ha' hM))
        (le_trans ?_ (h₂' M a a' ha ha' hM))
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_left _ _) _)
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_right _ _) _)
  | mul_X p i hp =>
    obtain ⟨K, h, h'⟩ := hp
    refine ⟨K, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_mul, MvPolynomial.eval_X, v.map_mul]
      exact le_add_of_le_of_nonneg (h a ha) (ha i)
    · rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      have e : MvPolynomial.eval a p * a i - MvPolynomial.eval a' p * a' i =
          (MvPolynomial.eval a p - MvPolynomial.eval a' p) * a i +
            MvPolynomial.eval a' p * (a i - a' i) := by ring
      rw [e]
      refine v.map_le_add ?_ ?_
      · rw [v.map_mul]
        exact le_add_of_le_of_nonneg (h' M a a' ha ha' hM) (ha i)
      · rw [v.map_mul]
        have e2 : ((M - K : ℝ) : WithTop ℝ) = ((-K : ℝ) : WithTop ℝ) + ((M : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; congr 1; ring
        rw [e2]
        exact add_le_add (h a' ha') (hM i)

theorem exists_poly_derivAt0_subst {C : Type} [Field C] {σ Λ : Type} [Fintype σ] [Fintype Λ]
    (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C) :
    ∃ Q : MvPolynomial (σ × Λ) C, ∀ a : σ → Λ → C,
      derivAt0 P (MvPowerSeries.subst
        (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) =
      MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2) Q := by
  let u : σ → MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    fun s => ∑ l, (MvPolynomial.X (s, l) : MvPolynomial (σ × Λ) C) • MvPowerSeries.X l
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero fun s => by simp [u]
  let Zu : MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    subst u (MvPowerSeries.map (MvPolynomial.C : C →+* MvPolynomial (σ × Λ) C) Z)
  refine ⟨∑ α ∈ P.support, MvPolynomial.C (P.coeff α * mfact α) * coeff α Zu, fun a => ?_⟩
  have key : MvPowerSeries.map (MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2)) Zu =
      MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z := by
    rw [MvPowerSeries.map_subst hu]
    congr 1
    · funext s
      simp [u, MvPowerSeries.smul_eq_C_mul]
    · ext d
      simp
  rw [← key, derivAt0, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, MvPolynomial.eval_C, coeff_map]

theorem derivAt0_subst_linear_lipschitz :
    ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ Λ : Type) [Fintype σ] [Fintype Λ] (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C), ∃ K : ℝ, ∀ (M : ℝ) (a a' : σ → Λ → C), (∀ s l, IsIntV v (a s l)) → (∀ s l, IsIntV v (a' s l)) → (∀ s l, ((M : ℝ) : WithTop ℝ) ≤ v (a s l - a' s l)) → ((M - K : ℝ) : WithTop ℝ) ≤ v (derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) - derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a' s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z)) := by
  intro C _ v σ Λ _ _ P Z
  obtain ⟨Q, hQ⟩ := exists_poly_derivAt0_subst P Z
  obtain ⟨K, -, hK⟩ := exists_lipschitz_eval v Q
  refine ⟨K, fun M a a' ha ha' hM => ?_⟩
  rw [hQ, hQ]
  exact hK M _ _ (fun x => ha x.1 x.2) (fun x => ha' x.1 x.2) (fun x => hM x.1 x.2)

end GlobalTheory.FGDepth
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ColApprox

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.FGDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

variable {C : Type} [Field C] {d : ℕ} {τ τ' : Type}

abbrev NC (a : Fin d → MvPowerSeries τ C) : Prop := ∀ i, constantCoeff (a i) = 0

def ev1 (a : Fin d → MvPowerSeries τ C) (f : PS C 1 d) : MvPowerSeries τ C :=
  subst (fun p : Fin 1 × Fin d => (![a] : Fin 1 → Fin d → MvPowerSeries τ C) p.1 p.2) f

def ev2 (a b : Fin d → MvPowerSeries τ C) (f : PS C 2 d) : MvPowerSeries τ C :=
  subst (fun p : Fin 2 × Fin d => (![a, b] : Fin 2 → Fin d → MvPowerSeries τ C) p.1 p.2) f

theorem nc1 {a : Fin d → MvPowerSeries τ C} (ha : NC a) (p : Fin 1 × Fin d) :
    constantCoeff ((![a] : Fin 1 → Fin d → MvPowerSeries τ C) p.1 p.2) = 0 := by
  obtain ⟨j, i⟩ := p
  fin_cases j; exact ha i

theorem nc2 {a b : Fin d → MvPowerSeries τ C} (ha : NC a) (hb : NC b) (p : Fin 2 × Fin d) :
    constantCoeff ((![a, b] : Fin 2 → Fin d → MvPowerSeries τ C) p.1 p.2) = 0 := by
  obtain ⟨j, i⟩ := p
  fin_cases j; exacts [ha i, hb i]

theorem constantCoeff_substOnePointPowerSeries_eq_zero {a : Fin d → MvPowerSeries τ C} (ha : NC a) {f : PS C 1 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev1 a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (nc1 ha)) (nc1 ha) hf

theorem constantCoeff_germEvalPair_eq_zero {a b : Fin d → MvPowerSeries τ C} (ha : NC a) (hb : NC b) {f : PS C 2 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev2 a b f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (nc2 ha hb)) (nc2 ha hb) hf

theorem subst_substOnePointPowerSeries {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) {a : Fin d → MvPowerSeries τ C} (ha : NC a)
    (f : PS C 1 d) : subst φ (ev1 a f) = ev1 (fun i => subst φ (a i)) f := by
  unfold ev1
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (nc1 ha)) hφ]
  congr 1
  funext ⟨j, i⟩
  fin_cases j; rfl

theorem subst_substTwoPointsPowerSeries {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) {a b : Fin d → MvPowerSeries τ C} (ha : NC a)
    (hb : NC b) (f : PS C 2 d) : subst φ (ev2 a b f) = ev2 (fun i => subst φ (a i)) (fun i => subst φ (b i)) f := by
  unfold ev2
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (nc2 ha hb)) hφ]
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> rfl

theorem subst_zero' {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) : subst φ (0 : MvPowerSeries τ C) = 0 := by
  rw [← coe_substAlgHom hφ, map_zero]

theorem substTwoPointsPowerSeries_zero_of_vanish_first_axis {a : Fin d → MvPowerSeries τ C} (ha : NC a) {h : PS C 2 d}
    (hh : ev (n := 1) ![pt C d 0, 0] h = 0) : ev2 a 0 h = 0 := by
  have hs : HasSubst (fun p : Fin 1 × Fin d => a p.2) := hasSubst_of_constantCoeff_zero fun p => ha p.2
  have h1 := congrArg (subst (fun p : Fin 1 × Fin d => a p.2)) (show ev2 (pt C (n := 1) d 0) 0 h = 0 from hh)
  rw [subst_substTwoPointsPowerSeries hs (fun i => by simp [pt]) (fun i => by simp), subst_zero' hs] at h1
  rw [← h1]
  congr 1
  · funext i; simp only [pt]; rw [subst_X hs]
  · funext i; exact (subst_zero' hs).symm

section Germ

variable [CharZero C] {n m : ℕ} (hL : PS C 1 d) (h : PS C 2 d) (k : ℕ) (g : PS C n d)

def germ (ψ : Fin n → Fin d → MvPowerSeries τ C) (s : Fin m → Fin d → MvPowerSeries τ C)
    (t : Fin m → Fin m → Fin d → MvPowerSeries τ C) : MvPowerSeries τ C :=
  subst (fun q : Fin n × Fin d => ψ q.1 q.2) g *
    PowerSeries.subst ((k : C) • (∑ j, ev1 (ψ j) hL - ∑ b, ∑ b', ev2 (s b) (t b b') h)) (PowerSeries.exp C)

variable {hL h}

theorem subst_germ (cL : constantCoeff hL = 0) (ch : constantCoeff h = 0) {φ : τ → MvPowerSeries τ' C}
    (hφ : HasSubst φ) {ψ : Fin n → Fin d → MvPowerSeries τ C} {s : Fin m → Fin d → MvPowerSeries τ C}
    {t : Fin m → Fin m → Fin d → MvPowerSeries τ C} (hψ : ∀ j, NC (ψ j)) (hs : ∀ b, NC (s b))
    (ht : ∀ b b', NC (t b b')) :
    subst φ (germ hL h k g ψ s t) = germ hL h k g (fun j i => subst φ (ψ j i)) (fun b i => subst φ (s b i))
      (fun b b' i => subst φ (t b b' i)) := by
  unfold germ
  have h0 : constantCoeff ((k : C) • (∑ j, ev1 (ψ j) hL - ∑ b, ∑ b', ev2 (s b) (t b b') h)) = 0 := by
    simp [map_sum, constantCoeff_substOnePointPowerSeries_eq_zero (hψ _) cL, constantCoeff_germEvalPair_eq_zero (hs _) (ht _ _) ch]
  rw [subst_mul hφ, subst_comp_subst_apply (a := fun q : Fin n × Fin d => ψ q.1 q.2)
    (hasSubst_of_constantCoeff_zero fun q => hψ q.1 q.2) hφ]
  congr 1
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => h0) hφ]
  congr 1
  funext _
  rw [← coe_substAlgHom hφ]
  simp only [map_smul, map_sub, map_sum]
  simp only [coe_substAlgHom, subst_substOnePointPowerSeries hφ (hψ _), subst_substTwoPointsPowerSeries hφ (hs _) (ht _ _)]

end Germ

section Exp

variable {v : AddValuation C (WithTop ℝ)} (L : LogFGL v d)

def exPt (w : Fin d → MvPowerSeries τ C) : Fin d → MvPowerSeries τ C := fun e => subst w (expOf L e)

theorem nc_exPt {w : Fin d → MvPowerSeries τ C} (hw : NC w) : NC (exPt L w) := fun e =>
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hw) hw ((isExp_expOf L).1 e)

theorem subst_exPt {φ : τ → MvPowerSeries τ' C} (hφ : HasSubst φ) {w : Fin d → MvPowerSeries τ C} (hw : NC w)
    (e : Fin d) : subst φ (exPt L w e) = exPt L (fun i => subst φ (w i)) e :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hw) hφ _

theorem lg_exPt {w : Fin d → MvPowerSeries τ C} (hw : NC w) (e : Fin d) : subst (exPt L w) (L.lg e) = w e := by
  have hs := hasSubst_of_constantCoeff_zero hw
  unfold exPt
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf L).1) hs, (isExp_expOf L).2, subst_X hs]

theorem exPt_lg {a : Fin d → MvPowerSeries τ C} (ha : NC a) : exPt L (fun e => subst a (L.lg e)) = a := by
  have hs := hasSubst_of_constantCoeff_zero ha
  funext e
  unfold exPt
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero L.lg_const) hs, subst_lg_expOf, subst_X hs]

theorem exPt_add {F : Fin d → PS C 2 d} (hF0 : NC F) (hF : ∀ a, L.F a = subst (twoVars C d) (F a))
    {w w' : Fin d → MvPowerSeries τ C} (hw : NC w) (hw' : NC w') :
    (fun i => ev2 (exPt L w) (exPt L w') (F i)) = exPt L (w + w') := by
  have ha := nc_exPt L hw
  have hb := nc_exPt L hw'
  have hs : HasSubst (Sum.elim (exPt L w) (exPt L w')) :=
    hasSubst_of_constantCoeff_zero fun s => by cases s; exacts [ha _, hb _]
  rw [← exPt_lg L (a := fun i => ev2 (exPt L w) (exPt L w') (F i)) fun i => constantCoeff_germEvalPair_eq_zero ha hb (hF0 i)]
  congr 1
  funext e
  have h1 := congrArg (subst (Sum.elim (exPt L w) (exPt L w'))) (L.lg_F e)
  rw [subst_add hs, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero L.F_const) hs,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hs,
    subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _) hs] at h1
  simp only [subst_X hs, Sum.elim_inl, Sum.elim_inr] at h1
  rw [Pi.add_apply, ← lg_exPt L hw e, ← lg_exPt L hw' e, ← h1]
  congr 1
  funext i
  rw [hF, subst_comp_subst_apply hs_twoVars hs]
  unfold ev2
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> simp [twoVars, subst_X hs]

theorem exPt_zero : exPt L (0 : Fin d → MvPowerSeries τ C) = 0 := by
  funext e
  exact subst_zero_of_constantCoeff_zero ((isExp_expOf L).1 e)

end Exp

theorem exPt_hom [CharZero C] {v : AddValuation C (WithTop ℝ)} (G : FGLaw C d)
    (hG : ∀ a, MvIsInt v (subst (twoVars C d) (G.F a))) (φ : Pt C 1 d) (hφ : NC φ)
    (hhom : comp1 φ G.F = addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1)))
    {w : Fin d → MvPowerSeries τ C} (hw : NC w) :
    (fun i => ev1 (exPt (logFGLOf v G hG) w) (φ i)) = exPt (logFGLOf v G hG) (fun e => ∑ f, dLin φ e f • w f) := by
  funext i
  have hl := logOf_comp_hom G G φ hφ hhom
  have h1 := exp_eq_of_log_hom (logFGLOf v G hG) (logFGLOf v G hG) (fun e => subst (oneVar C d) (φ e))
    (fun e => constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hφ e)) (dLin φ) (fun e => by
      show subst _ (subst (oneVar C d) _) = ∑ f, dLin φ e f • subst (oneVar C d) _
      rw [subst_oneVar _ cc_oneVar _ hφ]
      have := congrFun hl e
      simp only [comp1] at this
      rw [this, ← coe_substAlgHom hs_oneVar]
      simp only [map_sum, map_smul]) _ w hw (fun _ => rfl) i
  refine Eq.trans ?_ h1.symm
  have hs : HasSubst (exPt (logFGLOf v G hG) w) := hasSubst_of_constantCoeff_zero (nc_exPt _ hw)
  show _ = subst (exPt (logFGLOf v G hG) w) _
  rw [subst_comp_subst_apply hs_oneVar hs]
  unfold ev1
  congr 1
  funext ⟨j, i⟩
  fin_cases j; simp [oneVar, subst_X hs]

section Core

variable {Λ : Type} [Fintype Λ]

def lin (u : Λ → Fin d → C) (c : Λ → C) : Fin d → MvPowerSeries Λ C :=
  fun e => ∑ l, (c l * u l e) • (X l : MvPowerSeries Λ C)

theorem nc_lin (u : Λ → Fin d → C) (c : Λ → C) : NC (lin u c) := fun e => by simp [lin]

theorem lin_add (u : Λ → Fin d → C) (c c' : Λ → C) : lin u c + lin u c' = lin u (c + c') := by
  funext e
  simp only [lin, Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib]

theorem lin_zero (u : Λ → Fin d → C) : lin u 0 = 0 := by
  funext e; simp [lin]

theorem mat_lin (u : Λ → Fin d → C) (M : Matrix (Fin d) (Fin d) C) (c z : Λ → C)
    (hM : ∀ l, c l ≠ 0 → M.mulVec (u l) = z l • u l) :
    (fun e => ∑ f, M e f • lin u c f) = lin u (fun l => c l * z l) := by
  funext e
  simp only [lin, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  by_cases hc : c l = 0
  · simp [hc]
  · have := congrFun (hM l hc) e
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [mul_assoc, ← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun f _ => by ring

variable [CharZero C] {v : AddValuation C (WithTop ℝ)} {R : Type} [CommRing R] [Algebra R C] {O : Type} [CommRing O]
  [StarRing O] (B : FB R d O)

def colSum {m : ℕ} (x : Fin m → O) (s : List (Fin m)) : Pt C m d :=
  s.foldr (fun b acc => addOf (B.FK C) (comp1 (B.actK C (x b)) (pt C d b)) acc) 0

theorem nc_FK : NC (B.FK C) := (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).const

theorem nc_actK (a : O) : NC (B.actK C a) := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).const a

omit [CharZero C] in
theorem nc_pt {m : ℕ} (b : Fin m) : NC (pt C d b) := fun i => by simp [pt]

theorem nc_actPt {m : ℕ} (a : O) (b : Fin m) : NC (comp1 (B.actK C a) (pt C d b)) := fun i =>
  constantCoeff_substOnePointPowerSeries_eq_zero (nc_pt b) (nc_actK B a i)

theorem nc_colSum {m : ℕ} (x : Fin m → O) (s : List (Fin m)) : NC (colSum (C := C) B x s) := by
  induction s with
  | nil => intro i; simp [colSum]
  | cons b s ih => exact fun i => constantCoeff_germEvalPair_eq_zero (nc_actPt B _ b) ih (nc_FK B i)

omit [CharZero C] in
theorem int_map (hR : ∀ r, IsIntV v (algebraMap R C r)) {σ : Type} (f : MvPowerSeries σ R) :
    MvIsInt v (MvPowerSeries.map (algebraMap R C) f) := fun α => by
  rw [coeff_map]; exact hR _

theorem int_colSum (hR : ∀ r, IsIntV v (algebraMap R C r)) {m : ℕ} (x : Fin m → O) (s : List (Fin m))
    (i : Fin d) : MvIsInt v (colSum (C := C) B x s i) := by
  induction s generalizing i with
  | nil => intro α; simp [colSum, IsIntV]
  | cons b s ih =>
    refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (int_map hR _) ?_ (nc2 (nc_actPt B _ b) (nc_colSum B x s))
    rintro ⟨j, i⟩
    fin_cases j
    · refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (int_map hR _) ?_ (nc1 (nc_pt b))
      rintro ⟨j, i⟩ α
      fin_cases j
      show IsIntV v (coeff α (X (b, i)))
      rw [coeff_X]; split_ifs <;> simp [IsIntV]
    · exact ih i

variable {G : FGLaw C d} (hGF : G.F = B.FK C) (hG : ∀ a, MvIsInt v (subst (twoVars C d) (G.F a)))
  {m : ℕ} (col : Λ → Fin m) (u : Λ → Fin d → C) (σ : Fin m → O → C)
  (heig : ∀ a l, (dAct C B a).mulVec (u l) = σ (col l) a • u l)

def colExp (L : LogFGL v d) : Fin m × Fin d → MvPowerSeries Λ C :=
  fun q => exPt L (lin u fun l => if col l = q.1 then 1 else 0) q.2

omit [CharZero C] in
theorem hs_colExp (L : LogFGL v d) : HasSubst (colExp col u L) :=
  hasSubst_of_constantCoeff_zero fun q => nc_exPt L (nc_lin _ _) q.2

include hGF heig in
theorem subst_actPt (a : O) (b : Fin m) :
    (fun i => subst (colExp col u (logFGLOf v G hG)) (comp1 (B.actK C a) (pt C d b) i)) =
      exPt (logFGLOf v G hG) (lin u fun l => if col l = b then σ b a else 0) := by
  have hs := hs_colExp col u (logFGLOf v G hG)
  have hh := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).hom a
  rw [add_pt] at hh
  have h1 := exPt_hom G hG (B.actK C a) (nc_actK B a) (by rw [hGF]; exact hh)
    (nc_lin u fun l => if col l = b then 1 else 0)
  rw [mat_lin u (dLin (B.actK C a)) _ (fun l => σ (col l) a) fun l _ => heig a l] at h1
  have e : (fun l => (if col l = b then (1 : C) else 0) * σ (col l) a) = fun l => if col l = b then σ b a else 0 := by
    funext l; split_ifs with hl <;> simp [*]
  rw [← e, ← h1]
  funext i
  refine (subst_substOnePointPowerSeries hs (nc_pt b) _).trans ?_
  congr 1
  funext e
  exact subst_X hs _

include hGF heig in
theorem subst_colSum (x : Fin m → O) (s : List (Fin m)) :
    (fun i => subst (colExp col u (logFGLOf v G hG)) (colSum (C := C) B x s i)) =
      exPt (logFGLOf v G hG) (lin u fun l => (s.map fun b => if col l = b then σ b (x b) else 0).sum) := by
  have hs := hs_colExp col u (logFGLOf v G hG)
  induction s with
  | nil =>
    funext i
    simp only [List.map_nil, List.sum_nil]
    rw [show (fun _ : Λ => (0 : C)) = 0 from rfl, lin_zero, exPt_zero]
    exact subst_zero' hs
  | cons b s ih =>
    funext i
    refine (subst_substTwoPointsPowerSeries hs (nc_actPt B _ b) (nc_colSum B x s) _).trans ?_
    rw [ih, subst_actPt B hGF hG col u σ heig]
    refine (congrFun (exPt_add (logFGLOf v G hG) (nc_FK B) (fun a => by rw [← hGF]; rfl) (nc_lin _ _)
      (nc_lin _ _)) i).trans ?_
    rw [lin_add]
    rfl

def coefs {n : ℕ} (γ : Fin m → Fin n → C) (δ : Fin m → Fin m → C) : Fin n ⊕ Fin m ⊕ Fin m × Fin m → Λ → C :=
  Sum.elim (fun j l => γ (col l) j)
    (Sum.elim (fun b l => if col l = b then 1 else 0) fun q l => if col l = q.2 then δ q.1 q.2 else 0)

theorem subst_univ (L : LogFGL v d) {hL : PS C 1 d} {h : PS C 2 d} (cL : constantCoeff hL = 0)
    (ch : constantCoeff h = 0) (k : ℕ) {n : ℕ} (g : PS C n d) (c : Fin n ⊕ Fin m ⊕ Fin m × Fin m → Λ → C) :
    subst (fun s : (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d =>
        ∑ l, (c s.1 l * u l s.2) • (X l : MvPowerSeries Λ C))
      (germ (τ := (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) hL h k g
        (fun j => exPt L fun e => X (Sum.inl j, e)) (fun b => exPt L fun e => X (Sum.inr (Sum.inl b), e))
        fun b b' => exPt L fun e => X (Sum.inr (Sum.inr (b, b')), e)) =
      germ hL h k g (fun j => exPt L (lin u (c (Sum.inl j)))) (fun b => exPt L (lin u (c (Sum.inr (Sum.inl b)))))
        fun b b' => exPt L (lin u (c (Sum.inr (Sum.inr (b, b'))))) := by
  have hs : HasSubst (fun s : (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d =>
      ∑ l, (c s.1 l * u l s.2) • (X l : MvPowerSeries Λ C)) :=
    hasSubst_of_constantCoeff_zero fun s => nc_lin u (c s.1) s.2
  have hX : ∀ j : Fin n ⊕ Fin m ⊕ Fin m × Fin m,
      NC fun e : Fin d => (X (j, e) : MvPowerSeries ((Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) C) :=
    fun j e => by simp
  rw [subst_germ k g cL ch hs (fun _ => nc_exPt L (hX _)) (fun _ => nc_exPt L (hX _)) fun _ _ => nc_exPt L (hX _)]
  simp only [subst_exPt L hs (hX _), subst_X hs]
  rfl

include hGF heig in

theorem exists_germ_close (hR : ∀ r, IsIntV v (algebraMap R C r)) {h : PS C 2 d} (hc : B.IsCanonGauge C h) (w0 : O)
    (hu : ∀ l e, IsIntV v (u l e)) (hσ : ∀ b a, IsIntV v (σ b a)) {n : ℕ}
    (hU : ∀ x : Fin m → Fin n → O, ∃ U : PS R m d, FB.toK C U = FB.expS C ((∑ j : Fin n, ev (n := m)
      ![colSum B (fun b => x b j) (List.finRange m)] (B.hL C h w0)) - ∑ b : Fin m, ∑ b' : Fin m, ev (n := m)
        ![pt C d b, comp1 (B.actK C (w0 * ∑ j : Fin n, star (x b j) * x b' j)) (pt C d b')] h))
    (P : MvPolynomial Λ C) (k : ℕ) (g : PS C n d) (hg : MvIsInt v g) :
    ∃ K : ℝ, ∀ (M : ℝ) (x : Fin m → Fin n → O) (β : Fin m → Fin n → C), (∀ b j, IsIntV v (β b j)) →
      (∀ b j, ((M : ℝ) : WithTop ℝ) ≤ v (β b j - σ b (x b j))) →
      (∀ b b', ((M : ℝ) : WithTop ℝ) ≤ v (σ b' (w0 * ∑ j : Fin n, star (x b j) * x b' j))) →
      ∃ f : PS C m d, MvIsInt v f ∧ ((M - K : ℝ) : WithTop ℝ) ≤
        v (derivAt0 P (subst (fun q : Fin n × Fin d => exPt (logFGLOf v G hG) (lin u fun l => β (col l) q.1) q.2)
            (g * FB.expS C ((k : C) • ∑ j : Fin n, ev (n := n) ![pt C d j] (B.hL C h w0)))) -
          derivAt0 P (subst (colExp col u (logFGLOf v G hG)) f)) := by
  set L := logFGLOf v G hG with hL
  have ch : constantCoeff h = 0 := by
    have h0 := congrArg constantCoeff (substTwoPointsPowerSeries_zero_of_vanish_first_axis (τ := Fin 2 × Fin d) (a := 0) (fun _ => by simp) hc.ax1)
    have e : ev2 (0 : Fin d → PS C 2 d) 0 h = subst ((0 : Fin 2 × Fin d → C) • X) h := by
      unfold ev2; congr 1; funext ⟨j, i⟩; fin_cases j <;> simp
    rw [e, ← rescale_eq_subst, rescale_zero_apply] at h0
    simpa using h0
  have cL : constantCoeff (B.hL C h w0) = 0 := constantCoeff_germEvalPair_eq_zero (nc_pt 0) (nc_actPt B w0 0) ch
  obtain ⟨K, hK⟩ := GlobalTheory.FGDepth.derivAt0_subst_linear_lipschitz C v ((Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) Λ P
    (germ (τ := (Fin n ⊕ Fin m ⊕ Fin m × Fin m) × Fin d) (B.hL C h w0) h k g
      (fun j => exPt L fun e => X (Sum.inl j, e)) (fun b => exPt L fun e => X (Sum.inr (Sum.inl b), e))
      fun b b' => exPt L fun e => X (Sum.inr (Sum.inr (b, b')), e))
  refine ⟨K, fun M x β hβ h1 h2 => ?_⟩
  obtain ⟨U, hU⟩ := hU x
  have hΦ : ∀ j, NC (colSum (C := C) B (fun b => x b j) (List.finRange m)) := fun j => nc_colSum B _ _
  have imul : ∀ a b : C, IsIntV v a → IsIntV v b → IsIntV v (a * b) := fun a b ha hb => by
    unfold IsIntV at *
    rw [v.map_mul]; exact add_nonneg ha hb
  have ico : ∀ (γ : Fin m → Fin n → C) (δ : Fin m → Fin m → C), (∀ b j, IsIntV v (γ b j)) →
      (∀ b j, IsIntV v (δ b j)) → ∀ s l, IsIntV v (coefs col γ δ s l) := by
    rintro γ δ hγ hδ (j | b | q) l
    · exact hγ _ _
    · simp only [coefs, Sum.elim_inl, Sum.elim_inr]; split_ifs <;> simp [IsIntV]
    · simp only [coefs, Sum.elim_inr]; split_ifs
      · exact hδ _ _
      · simp [IsIntV]
  have key := hK M (fun s l => coefs col β 0 s.1 l * u l s.2)
    (fun s l => coefs col (fun b j => σ b (x b j))
      (fun b b' => σ b' (w0 * ∑ j : Fin n, star (x b j) * x b' j)) s.1 l * u l s.2)
    (fun s l => imul _ _ (ico _ _ hβ (fun _ _ => by simp [IsIntV]) _ _) (hu _ _))
    (fun s l => imul _ _ (ico _ _ (fun _ _ => hσ _ _) (fun _ _ => hσ _ _) _ _) (hu _ _)) (by
      rintro ⟨s, e⟩ l
      rw [← sub_mul, v.map_mul]
      refine le_add_of_le_of_nonneg ?_ (hu _ _)
      rcases s with j | b | q
      · exact h1 _ _
      · simp [coefs]
      · simp only [coefs, Sum.elim_inr]; split_ifs
        · simpa using h2 q.1 q.2
        · simp)
  rw [subst_univ u L cL ch, subst_univ u L cL ch] at key
  refine ⟨ev (fun j => colSum B (fun b => x b j) (List.finRange m)) g * FB.toK C U ^ k, ?_, ?_⟩
  · rw [← map_pow]
    intro α
    rw [coeff_mul]
    exact v.map_le_sum fun q _ => imul _ _ (ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v hg
      (fun q => int_colSum B hR _ _ _) (fun q => hΦ q.1 q.2) _) (int_map hR _ _)
  convert key using 4
  · have hp : ∀ j, NC (exPt L (lin u fun l => β (col l) j)) := fun j => nc_exPt L (nc_lin _ _)
    have hs : HasSubst (fun q : Fin n × Fin d => exPt L (lin u fun l => β (col l) q.1) q.2) :=
      hasSubst_of_constantCoeff_zero fun q => hp q.1 q.2
    have e0 : g * FB.expS C ((k : C) • ∑ j : Fin n, ev (n := n) ![pt C d j] (B.hL C h w0)) =
        germ (m := 0) (B.hL C h w0) h k g (pt C d) (fun _ => 0) fun _ _ => 0 := by
      unfold germ
      rw [show (fun q : Fin n × Fin d => pt C d q.1 q.2) = X from rfl, subst_self]
      simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
      rfl
    rw [e0, subst_germ k g cL ch hs nc_pt (fun _ _ => by simp) fun _ _ _ => by simp]
    have e1 : ∀ b b' : Fin m, coefs col β 0 (Sum.inr (Sum.inr (b, b'))) = 0 := fun b b' => by
      funext l; simp [coefs]
    simp only [germ, pt, subst_X hs, e1, lin_zero, exPt_zero, substTwoPointsPowerSeries_zero_of_vanish_first_axis (nc_exPt L (nc_lin _ _)) hc.ax1,
      Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]
    rfl
  · have hs := hs_colExp col u L
    have e0 : ev (fun j => colSum B (fun b => x b j) (List.finRange m)) g * FB.toK C U ^ k =
        germ (B.hL C h w0) h k g (fun j => colSum B (fun b => x b j) (List.finRange m)) (pt C d)
          fun b b' => comp1 (B.actK C (w0 * ∑ j : Fin n, star (x b j) * x b' j)) (pt C d b') := by
      rw [hU, ← GlobalTheory.JetSer.IntTrans.expS_nsmul]
      · rfl
      · rw [map_sub, map_sum, map_sum, sub_eq_zero]
        refine (Finset.sum_eq_zero fun j _ => constantCoeff_substOnePointPowerSeries_eq_zero (hΦ j) cL).trans (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [map_sum]
        exact Finset.sum_eq_zero fun b' _ => constantCoeff_germEvalPair_eq_zero (nc_pt b) (nc_actPt B _ b') ch
    rw [e0, subst_germ k g cL ch hs hΦ nc_pt fun b b' => nc_actPt B _ b']
    congr 1
    · funext j
      rw [subst_colSum B hGF hG col u σ heig]
      congr 2
      funext l
      rw [← Fin.sum_univ_def]
      simp [coefs]
    · funext b e
      exact subst_X hs _
    · funext b b'
      exact subst_actPt B hGF hG col u σ heig _ _

end Core

end GlobalTheory.ColApprox
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpCoord

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.LawLog
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (pderiv_subst)

section Deriv

variable {C : Type} [Field C] {σ : Type}

theorem mfact_eq_prod [Fintype σ] (α : σ →₀ ℕ) : (mfact α : C) = ∏ s, ((α s).factorial : C) := by
  first
  | exact Finsupp.prod_fintype α _ (fun _ => by simp)
  | (unfold mfact; rw [Finsupp.prod_fintype]; intro; simp)

theorem mfact_add_single [Fintype σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : C) = mfact α * ((α l : C) + 1) := by
  classical
  first
  | (have h : ∀ s, (((α + Finsupp.single l 1 : σ →₀ ℕ) s).factorial : C) =
        ((α s).factorial : C) * (if s = l then ((α l : C) + 1) else 1) := by
      intro s
      by_cases hs : s = l
      · rw [if_pos hs]
        subst hs
        rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hs, mul_one]
        simp [Finsupp.single_apply, Ne.symm hs]
     rw [mfact_eq_prod, mfact_eq_prod, Finset.prod_congr rfl (fun s _ => h s), Finset.prod_mul_distrib]
     simp
     done)

theorem derivAt0_monomial (α : σ →₀ ℕ) (a : C) (S : MvPowerSeries σ C) :
    derivAt0 (MvPolynomial.monomial α a) S = a * mfact α * coeff α S := by
  classical
  first
  | (rw [derivAt0_eq_sum_of_subset _ _ MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]; done)
  | (by_cases ha : a = 0 <;> simp [derivAt0, ha, MvPolynomial.support_monomial]; done)

private lemma hasSubst_lemma {ι τ : Type} [Finite ι] {a : ι → MvPowerSeries τ C}
    (ha : ∀ i, constantCoeff (a i) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha]; exact IsNilpotent.zero)

private lemma cc_subst_lemma_2 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) :
    constantCoeff (subst a f) = 0 := by
  first
  | exact constantCoeff_subst_eq_zero (hasSubst_lemma ha) ha hf
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_lemma ha) ha hf
  | exact MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_lemma ha) hf

private lemma subst_zero_lemma_3 {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) :
    subst a (0 : MvPowerSeries σ C) = 0 := by
  first
  | (rw [← MvPowerSeries.coe_substAlgHom ha]; exact map_zero _)
  | simp

private lemma subst_C_eq_C' {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (r : C) :
    subst a (MvPowerSeries.C r : MvPowerSeries σ C) = MvPowerSeries.C r := by
  first
  | (rw [← MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.c_eq_algebraMap, AlgHom.commutes,
      MvPowerSeries.c_eq_algebraMap])
  | (rw [← MvPowerSeries.coe_substAlgHom ha]; exact AlgHom.commutes _ r)
  | simp [ha]

private lemma subst_subst_eq_subst_comp {σ τ ρ : Type} {a : σ → MvPowerSeries τ C} {b : τ → MvPowerSeries ρ C}
    (ha : HasSubst a) (hb : HasSubst b) (f : MvPowerSeries σ C) :
    subst b (subst a f) = subst (fun s => subst b (a s)) f := by
  first
  | exact MvPowerSeries.subst_comp_subst_apply ha hb f
  | exact (MvPowerSeries.subst_comp_subst_apply ha hb f).symm
  | exact congrFun (MvPowerSeries.subst_comp_subst ha hb) f

private lemma pderiv_inr_subst_twoVars {d : ℕ} (f : MvPowerSeries (Fin 2 × Fin d) C) (k : Fin d) :
    pderiv C (Sum.inr k) (subst (GlobalTheory.LawLog.twoVars C d) f) =
      subst (GlobalTheory.LawLog.twoVars C d) (pderiv C ((1 : Fin 2), k) f) := by
  classical
  rw [pderiv_subst GlobalTheory.LawLog.cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply]
  · rintro ⟨a, i⟩ _ hs
    fin_cases a
    · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply]
    · have hik : i ≠ k := fun h => hs (by subst h; rfl)
      simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.pderiv_X, Pi.single_apply, hik]
  · simp

variable [CharZero C] (v : AddValuation C (WithTop ℝ))
include v

theorem derivAt0_pderiv [Fintype σ] (Q : MvPolynomial σ C) (l : σ) (S : MvPowerSeries σ C) :
    derivAt0 Q (pderiv C l S) = derivAt0 (Q * MvPolynomial.X l) S := by
  classical
  first
  | (unfold derivAt0
     rw [MvPolynomial.support_mul_X, Finset.sum_map]
     refine Finset.sum_congr rfl fun α _ => ?_
     simp only [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, mfact_add_single]
     first
     | (rw [MvPowerSeries.coeff_pderiv]; ring)
     | (simp [MvPowerSeries.coeff_pderiv]; ring)
     | (simp [MvPowerSeries.coeff_pderiv])
     done)

end Deriv

section Chain

variable {C : Type} [Field C] [CharZero C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem subst_jacEntry (G : FGLaw C d) (L : LogFGL v d)
    (hL : ∀ a, L.F a = subst (twoVars C d) (G.F a)) {n : ℕ} {Λ : Type} [Finite Λ]
    (ψ : Fin n × Fin d → MvPowerSeries Λ C) (hψ : ∀ q, constantCoeff (ψ q) = 0) (j : Fin n) (k e : Fin d) :
    subst (fun i => ψ (j, i)) (GlobalTheory.LogJacobian.jacEntry L k e) =
      subst ψ (ev (n := n) ![pt C d j, 0] (pderiv C ((1 : Fin 2), k) (G.F e))) := by
  classical
  have hA : HasSubst (GlobalTheory.LogJacobian.substSecondBlockZero (C := C) d) := hasSubst_lemma (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d)
  have hT : HasSubst (GlobalTheory.LawLog.twoVars C d) := hasSubst_lemma GlobalTheory.LawLog.cc_twoVars
  have hB : HasSubst (fun i => ψ (j, i)) := hasSubst_lemma (fun i => hψ (j, i))
  have hΨ : HasSubst ψ := hasSubst_lemma hψ
  have hAT : HasSubst (fun s => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := C) d) (GlobalTheory.LawLog.twoVars C d s)) :=
    hasSubst_lemma (fun s => cc_subst_lemma_2 (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (GlobalTheory.LawLog.cc_twoVars s))
  have hP : HasSubst (fun p : Fin 2 × Fin d => (![fun i => X (j, i), 0] : Fin 2 → Fin d → MvPowerSeries (Fin n × Fin d) C) p.1 p.2) := by
    refine hasSubst_lemma (fun p => ?_)
    rcases p with ⟨a, i⟩
    fin_cases a <;> simp
  unfold GlobalTheory.LogJacobian.jacEntry ev pt
  rw [hL e, pderiv_inr_subst_twoVars, subst_subst_eq_subst_comp hT hA, subst_subst_eq_subst_comp hAT hB, subst_subst_eq_subst_comp hP hΨ]
  congr 1
  funext p
  rcases p with ⟨a, i⟩
  fin_cases a
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.subst_X hA, MvPowerSeries.subst_X hΨ]
    all_goals simp [GlobalTheory.LogJacobian.substSecondBlockZero, MvPowerSeries.subst_X hB]
  · simp [GlobalTheory.LawLog.twoVars, MvPowerSeries.subst_X hA, MvPowerSeries.subst_X hΨ, subst_zero_lemma_3 hΨ]
    all_goals simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_zero_lemma_3 hB]

variable (L : LogFGL v d) {n : ℕ} {Λ : Type} [Fintype Λ] (β : Λ → Fin n → C) (w : Λ → Fin d → C)

def lin (j : Fin n) : Fin d → MvPowerSeries Λ C :=
  fun e => ∑ l, (β l j * w l e) • (X l : MvPowerSeries Λ C)

def psi : Fin n × Fin d → MvPowerSeries Λ C :=
  fun q => subst (lin β w q.1) (expOf L q.2)

theorem cc_lin (j : Fin n) (e : Fin d) : constantCoeff (lin β w j e) = 0 := by
  first
  | (simp [lin, MvPowerSeries.smul_eq_C_mul]; done)
  | (unfold lin
     rw [map_sum]
     refine Finset.sum_eq_zero fun l _ => ?_
     rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])

theorem cc_psi (q : Fin n × Fin d) : constantCoeff (psi L β w q) = 0 := by
  have hs : MvPowerSeries.HasSubst (lin β w q.1) := by
    first
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' (cc_lin β w q.1)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_lin β w q.1)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [cc_lin]; exact IsNilpotent.zero)
  first
  | exact constantCoeff_subst_eq_zero hs (cc_lin β w q.1) ((isExp_expOf L).1 q.2)
  | exact MvPowerSeries.constantCoeff_subst_eq_zero hs (cc_lin β w q.1) ((isExp_expOf L).1 q.2)
  | exact MvPowerSeries.constantCoeff_subst_eq_zero hs ((isExp_expOf L).1 q.2)

theorem pderiv_lin (l : Λ) (j : Fin n) (e : Fin d) :
    pderiv C l (lin β w j e) = MvPowerSeries.C (β l j * w l e) := by
  classical
  first
  | (simp only [lin, map_sum, Derivation.map_smul, MvPowerSeries.pderiv_X]
     simp [Pi.single_apply, MvPowerSeries.smul_eq_C_mul]
     done)
  | (simp [lin, MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]; done)

theorem pderiv_subst_psi (G : FGLaw C d) (hL : ∀ a, L.F a = subst (twoVars C d) (G.F a)) (l : Λ) (g : PS C n d) :
    pderiv C l (subst (psi L β w) g) =
      subst (psi L β w) (∑ j, MvPowerSeries.C (β l j) * DofN G.F j (w l) g) := by
  classical
  have hΨ : HasSubst (psi L β w) := hasSubst_lemma (cc_psi L β w)
  have hpt : ∀ (j : Fin n) (i : Fin d), constantCoeff (pt C d j i) = 0 := fun j i => by simp [pt]
  have hcol : ∀ (j : Fin n) (c : Fin d), pderiv C l (psi L β w (j, c)) =
      ∑ e, subst (psi L β w) (ev ![pt C d j, 0] (pderiv C ((1 : Fin 2), e) (G.F c))) *
        MvPowerSeries.C (β l j * w l e) := by
    intro j c
    have hlin : HasSubst (lin β w j) := hasSubst_lemma (cc_lin β w j)
    have hE : HasSubst (expOf L) := hasSubst_lemma (isExp_expOf L).1
    show pderiv C l (subst (lin β w j) (expOf L c)) = _
    rw [pderiv_subst (cc_lin β w j)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [pderiv_lin, GlobalTheory.LogJacobian.pderiv_expOf, subst_subst_eq_subst_comp hE hlin]
    congr 1
    exact subst_jacEntry G L hL (psi L β w) (cc_psi L β w) j e c
  rw [pderiv_subst (cc_psi L β w), Fintype.sum_prod_type]
  simp only [hcol]
  simp only [GlobalTheory.MatChain.dofN_eq G, GlobalTheory.MatChain.jv]
  rw [← MvPowerSeries.coe_substAlgHom hΨ]
  simp only [map_sum, map_mul, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [GlobalTheory.MatChain.ev_jac G (hpt j)]
  try rw [map_mul]
  ring

end Chain

open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies GlobalTheory.MatChain in

theorem constantCoeff_dpolyN_eq_derivAt0 : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : FGLaw C d) (L : LogFGL v d), (∀ a, L.F a = MvPowerSeries.subst (twoVars C d) (G.F a)) → ∀ (n : ℕ) (ι Λ : Type) [Fintype ι] [Fintype Λ] (cp : ι → Fin n) (u : ι → Fin d → C) (β : Λ → Fin n → C) (t : Λ → Fin n → ι) (w : Λ → Fin d → C), (∀ l j, cp (t l j) = j) → (∀ l j, u (t l j) = w l) → ∀ (P : MvPolynomial Λ C) (g : PS C n d), MvPowerSeries.constantCoeff (DpolyN G.F cp u (MvPolynomial.aeval (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) P) g) = derivAt0 P (MvPowerSeries.subst (fun q : Fin n × Fin d => (MvPowerSeries.subst (fun e : Fin d => ∑ l, (β l q.1 * w l e) • (MvPowerSeries.X l : MvPowerSeries Λ C)) (expOf L q.2) : MvPowerSeries Λ C)) g) := by
  intro C _ _ v d G L hL n ι Λ _ _ cp u β t w hcp hu P g
  classical
  show constantCoeff (DpolyN G.F cp u (MvPolynomial.aeval
      (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) P) g) =
    derivAt0 P (subst (psi L β w) g)
  have hΨ : HasSubst (psi L β w) := hasSubst_lemma (cc_psi L β w)
  have hmon0 : ∀ f : PS C n d, DmonN G.F cp u 0 f = f := by
    intro f
    simp [DmonN]
  have hsub : ∀ (Q : MvPolynomial ι C) (s : Finset (ι →₀ ℕ)) (f : PS C n d), Q.support ⊆ s →
      DpolyN G.F cp u Q f = ∑ m ∈ s, MvPowerSeries.C (MvPolynomial.coeff m Q) * DmonN G.F cp u m f := by
    intro Q s f hs
    unfold DpolyN
    refine Finset.sum_subset hs fun m _ hm => ?_
    simp only [MvPolynomial.mem_support_iff, not_not] at hm
    simp [hm]
  have hadd : ∀ (Q1 Q2 : MvPolynomial ι C) (f : PS C n d),
      DpolyN G.F cp u (Q1 + Q2) f = DpolyN G.F cp u Q1 f + DpolyN G.F cp u Q2 f := by
    intro Q1 Q2 f
    rw [hsub (Q1 + Q2) (Q1.support ∪ Q2.support) f MvPolynomial.support_add,
      hsub Q1 (Q1.support ∪ Q2.support) f Finset.subset_union_left,
      hsub Q2 (Q1.support ∪ Q2.support) f Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_add, map_add, add_mul]
  have hC : ∀ (a : C) (f : PS C n d), DpolyN G.F cp u (MvPolynomial.C a) f = MvPowerSeries.C a * f := by
    intro a f
    rw [hsub (MvPolynomial.C a) {0} f (by rw [MvPolynomial.C_apply]; exact MvPolynomial.support_monomial_subset),
      Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl, hmon0]
  have hfin : ∀ (Q : Fin n → MvPolynomial ι C) (f : PS C n d),
      DpolyN G.F cp u (∑ j, Q j) f = ∑ j, DpolyN G.F cp u (Q j) f := fun Q f =>
    map_sum (AddMonoidHom.mk' (fun Q => DpolyN G.F cp u Q f) (fun Q1 Q2 => hadd Q1 Q2 f)) Q Finset.univ
  have hcomm1 : ∀ (j : Fin n) (x : Fin d → C) (Q : MvPolynomial ι C) (f : PS C n d),
      DofN G.F j x (DpolyN G.F cp u Q f) = DpolyN G.F cp u Q (DofN G.F j x f) := by
    intro j x Q
    induction Q using MvPolynomial.induction_on
    next a =>
      intro f
      rw [hC, hC, GlobalTheory.MatChain.dofN_C_mul]
    next Q1 Q2 h1 h2 =>
      intro f
      rw [hadd, hadd, GlobalTheory.MatChain.dofN_add, h1, h2]
    next Q m h =>
      intro f
      rw [GlobalTheory.MatChain.dpoly_mul_X, GlobalTheory.MatChain.dpoly_mul_X, Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation.dofN_comm, h]
  have hccs : ∀ f : PS C n d, constantCoeff (subst (psi L β w) f) = constantCoeff f := by
    intro f
    have h0 : constantCoeff (f - MvPowerSeries.C (constantCoeff f)) = 0 := by simp
    have h1 := cc_subst_lemma_2 (cc_psi L β w) h0
    rw [← MvPowerSeries.coe_substAlgHom hΨ, map_sub, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ,
      map_sub] at h1
    simpa [sub_eq_zero] using h1
  have hlinD : ∀ (Q : MvPolynomial Λ C) (b : Fin n → C) (s : Fin n → MvPowerSeries Λ C),
      derivAt0 Q (∑ j, MvPowerSeries.C (b j) * s j) = ∑ j, b j * derivAt0 Q (s j) := by
    intro Q b s
    simp only [derivAt0, map_sum, MvPowerSeries.coeff_C_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun α _ => by ring
  revert g
  induction P using MvPolynomial.induction_on
  next a =>
    intro g
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, hC, MvPolynomial.C_apply, derivAt0_monomial]
    simp [mfact, hccs, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  next P1 P2 h1 h2 =>
    intro g
    rw [map_add, hadd, map_add, h1, h2,
      (derivAt0_linear C v Λ P1 P2 (subst (psi L β w) g) (subst (psi L β w) g) 0).2.2.1]
  next Q l h =>
    intro g
    have hφ : MvPolynomial.aeval (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C))
          (Q * MvPolynomial.X l) =
        ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.aeval
          (fun l => ∑ j, MvPolynomial.C (β l j) * (MvPolynomial.X (t l j) : MvPolynomial ι C)) Q *
            MvPolynomial.X (t l j)) := by
      rw [map_mul, MvPolynomial.aeval_X, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hφ, hfin]
    simp only [GlobalTheory.MatChain.dpoly_C_mul, GlobalTheory.MatChain.dpoly_mul_X, hcp, hu, hcomm1]
    rw [← derivAt0_pderiv v Q l, pderiv_subst_psi L β w G hL l g, ← MvPowerSeries.coe_substAlgHom hΨ]
    simp only [map_sum, map_mul, MvPowerSeries.coe_substAlgHom, subst_C_eq_C' hΨ, MvPowerSeries.constantCoeff_C, h]
    rw [hlinD]

end GlobalTheory.ExpCoord
end
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.QuadDeriv

namespace GlobalTheory.MatrixGauge

section Small

variable (R : Type) [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {m : ℕ}

def Small (f : PS k m d) : Prop :=
  constantCoeff f = 0 ∧ ∃ w : PS R m d, constantCoeff w = 1 ∧ FB.toK k w = FB.expS k f

def IsBase (P : Pt k m d) : Prop := ∃ Q : Pt R m d, GP Q ∧ P = mapP (algebraMap R k) Q

variable {R}

theorem small_zero : Small R (0 : PS k m d) :=
  ⟨map_zero _, 1, map_one _, by
    rw [FB.toK, map_one, FB.expS, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]⟩

theorem Small.congr {f g : PS k m d} (hf : Small R f) (e : f = g) : Small R g := e ▸ hf

theorem Small.add {f g : PS k m d} (hf : Small R f) (hg : Small R g) : Small R (f + g) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  obtain ⟨g0, w, w1, hw⟩ := hg
  refine ⟨by simp [f0, g0], v * w, by simp [v1, w1], ?_⟩
  rw [FB.toK, map_mul, gt_expS_add _ _ f0 g0]
  exact congrArg₂ (· * ·) hv hw

theorem Small.neg {f : PS k m d} (hf : Small R f) : Small R (-f) := by
  obtain ⟨f0, v, v1, hv⟩ := hf
  have n0 : constantCoeff (-f) = 0 := by simp [f0]
  refine ⟨n0, invOfUnit v 1, by simp, ?_⟩
  have h1 : FB.toK k v * FB.toK k (invOfUnit v 1) = 1 := by
    rw [FB.toK, FB.toK, ← map_mul, mul_invOfUnit v 1 (by simpa using v1), map_one]
  have h2 : FB.expS k (-f) * FB.expS k f = 1 := by
    rw [← gt_expS_add _ _ n0 f0, neg_add_cancel, FB.expS, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero]
  rw [hv] at h1
  calc FB.toK k (invOfUnit v 1) = (FB.expS k (-f) * FB.expS k f) * FB.toK k (invOfUnit v 1) := by
        rw [h2, _root_.one_mul]
    _ = FB.expS k (-f) := by rw [_root_.mul_assoc, h1, _root_.mul_one]

theorem Small.sum {ι : Type} (s : Finset ι) {f : ι → PS k m d} (hf : ∀ i, Small R (f i)) :
    Small R (∑ i ∈ s, f i) :=
  Finset.sum_induction f (Small R) (fun _ _ => Small.add) small_zero fun i _ => hf i

theorem Small.sum_sub {ι : Type} (s : Finset ι) {f g : ι → PS k m d} (hf : ∀ i, Small R (f i - g i)) :
    Small R (∑ i ∈ s, f i - ∑ i ∈ s, g i) :=
  (Small.sum s hf).congr (Finset.sum_sub_distrib _ _)

theorem Small.trans {f g e : PS k m d} (h1 : Small R (f - g)) (h2 : Small R (g - e)) : Small R (f - e) :=
  (h1.add h2).congr (by ring)

omit [Algebra ℚ k] in
theorem IsBase.gp {P : Pt k m d} (hP : IsBase R P) : GP P := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact constantCoeff_mapP_eq_zero _ _ hQ

omit [Algebra ℚ k] in
theorem isBase_pt (j : Fin m) : IsBase R (pt k d j) := ⟨pt R d j, gp_pt j, (baseChange_pt _ j).symm⟩

omit [Algebra ℚ k] in
theorem isBase_zero : IsBase R (0 : Pt k m d) := ⟨0, gp_zero₂, funext fun _ => (map_zero _).symm⟩

theorem Small.subst {l : ℕ} {V : Fin l → Pt k m d} (hV : ∀ j, IsBase R (V j)) {f : PS k l d}
    (hf : Small R f) : Small R (ev V f) := by
  obtain ⟨f0, w, w1, hw⟩ := hf
  have hV' : ∀ j, GP (V j) := fun j => (hV j).gp
  choose a ha e using hV
  refine ⟨gt_const_ev V hV' f f0, ev a w, by rw [gt_const_ev_eq a ha, w1], ?_⟩
  rw [← gt_ev_expS V hV' f f0, ← hw, FB.toK, QuadDeriv.map_ev _ _ ha]
  congr 1
  funext j
  exact (e j).symm

omit [Algebra ℚ k] in
theorem isBase2 {P Q : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) : ∀ j, IsBase R (![P, Q] j) := by
  intro j; fin_cases j
  · exact hP
  · exact hQ

omit [Algebra ℚ k] in
theorem isBase3 {P Q T : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) (hT : IsBase R T) :
    ∀ j, IsBase R (![P, Q, T] j) := by
  intro j; fin_cases j
  · exact hP
  · exact hQ
  · exact hT

end Small

section Points

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra R k] (B : FB R d O) {m : ℕ}

theorem gp_act (a : O) : GP (B.actK k a) := constantCoeff_mapP_eq_zero _ _ (B.A.const a)

theorem gp_law : GP (B.FK k) := constantCoeff_mapP_eq_zero _ _ B.G.const

theorem IsBase.act (a : O) {P : Pt k m d} (hP : IsBase R P) : IsBase R (comp1 (B.actK k a) P) := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact ⟨comp1 (B.A.act a) Q, gp_comp1 _ _ (B.A.const a) hQ, (baseChange_comp1 _ _ _ hQ).symm⟩

theorem IsBase.add {P P' : Pt k m d} (hP : IsBase R P) (hP' : IsBase R P') :
    IsBase R (addOf (B.FK k) P P') := by
  obtain ⟨Q, hQ, rfl⟩ := hP
  obtain ⟨Q', hQ', rfl⟩ := hP'
  exact ⟨addOf B.G.F Q Q', gp_addOf _ B.G.const _ _ hQ hQ', (baseChange_addOf _ _ _ _ hQ hQ').symm⟩

theorem isBase_foldr {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b)) (L : List ι) :
    IsBase R (L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0) := by
  induction L with
  | nil => exact isBase_zero
  | cons b L ih => exact (hg b).add B ih

theorem act_act (a c : O) {P : Pt k m d} (hP : GP P) :
    comp1 (B.actK k a) (comp1 (B.actK k c) P) = comp1 (B.actK k (a * c)) P := by
  rw [FramePull.actK_mul, gt_comp1_comp1 _ _ (gp_act B c) _ hP]

theorem add_act (a c : O) {P : Pt k m d} (hP : GP P) :
    comp1 (B.actK k (a + c)) P = addOf (B.FK k) (comp1 (B.actK k a) P) (comp1 (B.actK k c) P) := by
  rw [FramePull.actK_add]
  exact evP_addOf ![P] (single_point_zero_constant hP) _ _ _ (gp_act B a) (gp_act B c)

theorem act_add (a : O) {P Q : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q) :
    comp1 (B.actK k a) (addOf (B.FK k) P Q) =
      addOf (B.FK k) (comp1 (B.actK k a) P) (comp1 (B.actK k a) Q) := by
  obtain ⟨P, hP, rfl⟩ := hP
  obtain ⟨Q, hQ, rfl⟩ := hQ
  have hV := pair_points_zero_constant hP hQ
  have p0 : GP (pt R (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt R (n := 2) d 1) := gp_pt 1
  have hc : ∀ {n : ℕ} {X : Pt R n d}, GP X → GP (comp1 (B.A.act a) X) :=
    fun hX => gp_comp1 _ _ (B.A.const a) hX
  have h1 := congrArg (evP ![P, Q]) (B.A.hom a)
  rw [evP_comp1 _ hV _ _ (gp_addOf _ B.G.const _ _ p0 p1), evP_addOf _ hV _ _ _ p0 p1,
    evP_addOf _ hV _ _ _ (hc p0) (hc p1), evP_comp1 _ hV _ _ p0, evP_comp1 _ hV _ _ p1,
    evP_pt _ hV, evP_pt _ hV] at h1
  have h2 : comp1 (B.A.act a) (addOf B.G.F P Q) =
      addOf B.G.F (comp1 (B.A.act a) P) (comp1 (B.A.act a) Q) := h1
  have h3 := congrArg (mapP (algebraMap R k)) h2
  rw [baseChange_comp1 _ _ _ (gp_addOf _ B.G.const _ _ hP hQ), baseChange_addOf _ _ _ _ hP hQ,
    baseChange_addOf _ _ _ _ (hc hP) (hc hQ), baseChange_comp1 _ _ _ hP, baseChange_comp1 _ _ _ hQ] at h3
  exact h3

theorem act_foldr (a : O) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b)) (L : List ι) :
    comp1 (B.actK k a) (L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0) =
      L.foldr (fun b acc => addOf (B.FK k) (comp1 (B.actK k a) (g b)) acc) 0 := by
  induction L with
  | nil => exact gt_comp1_zero _ (gp_act B a)
  | cons b L ih => rw [List.foldr_cons, List.foldr_cons, act_add B a (hg b) (isBase_foldr B hg L), ih]

end Points

section Gauge

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] {B : FB R d O} {h : PS k 2 d} {m : ℕ}

theorem const_gauge (hh : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have := congrArg constantCoeff hh.ax0
  rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this

theorem gauge_zero_left (hh : B.IsCanonGauge k h) {Q : Pt k m d} (hQ : GP Q) : ev ![0, Q] h = 0 := by
  have := congrArg (ev ![Q]) hh.ax0
  rwa [formalSubst_single_of_formalSubst_two _ hQ _ _ gp_zero₂ (gp_pt 0), formalComp_zero_left_point _ hQ, gt_comp1_pt _ hQ,
    gt_ev_zero _ (single_point_zero_constant hQ)] at this

theorem gauge_zero_right (hh : B.IsCanonGauge k h) {Q : Pt k m d} (hQ : GP Q) : ev ![Q, 0] h = 0 := by
  have := congrArg (ev ![Q]) hh.ax1
  rwa [formalSubst_single_of_formalSubst_two _ hQ _ _ (gp_pt 0) gp_zero₂, formalComp_zero_left_point _ hQ, gt_comp1_pt _ hQ,
    gt_ev_zero _ (single_point_zero_constant hQ)] at this

theorem small_balanced (hh : B.IsCanonGauge k h) (a : O) {P Q : Pt k m d} (hP : IsBase R P)
    (hQ : IsBase R Q) :
    Small R (ev ![comp1 (B.actK k a) P, Q] h - ev ![P, comp1 (B.actK k (star a)) Q] h) := by
  have p0 : GP (pt k (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 2) d 1) := gp_pt 1
  have c0 := pair_points_zero_constant (gp_comp1 _ _ (gp_act B a) p0) p1
  have c1 := pair_points_zero_constant p0 (gp_comp1 _ _ (gp_act B (star a)) p1)
  have w1 : constantCoeff (B.ad a) = 1 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant (gp_zero₂ (n := 1)) (gp_pt 0)), B.adjoint_zero_fst, map_one]
  have key := Small.subst (isBase2 hP hQ) ⟨by
    rw [map_sub, gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, sub_self], _, w1, hh.ad a⟩
  have hV := pair_points_zero_constant hP.gp hQ.gp
  rw [gt_ev_sub _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, eval_pair_points, eval_pair_points,
    evP_comp1 _ hV _ _ p0, evP_comp1 _ hV _ _ p1, evP_pt _ hV, evP_pt _ hV] at key
  exact key

theorem small_add_left (hh : B.IsCanonGauge k h) {P P' Q : Pt k m d} (hP : IsBase R P) (hP' : IsBase R P')
    (hQ : IsBase R Q) :
    Small R (ev ![P, Q] h + ev ![P', Q] h - ev ![addOf (B.FK k) P P', Q] h) := by
  have p0 : GP (pt k (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt k (n := 3) d 2) := gp_pt 2
  have c0 := pair_points_zero_constant p0 p2
  have c1 := pair_points_zero_constant p1 p2
  have c2 := pair_points_zero_constant (gp_addOf _ (gp_law B) _ _ p0 p1) p2
  have w1 : constantCoeff B.ph1 = 1 := by
    rw [← gt_const_ev_eq _ (triple_points_zero_constant (gp_zero₂ (n := 2)) (gp_pt 0) (gp_pt 1)), B.cocycleLeft_zero_fst, map_one]
  have key := Small.subst (isBase3 hP hP' hQ) ⟨by
    rw [map_sub, map_add, gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, gt_const_ev_eq _ c2, const_gauge hh,
      add_zero, sub_self], _, w1, hh.ph1⟩
  have hV := triple_points_zero_constant hP.gp hP'.gp hQ.gp
  rw [gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, gt_ev_ev' _ _ hV c2,
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ p0 p1, evP_pt _ hV, evP_pt _ hV,
    evP_pt _ hV] at key
  exact key

theorem small_add_right (hh : B.IsCanonGauge k h) {P Q Q' : Pt k m d} (hP : IsBase R P) (hQ : IsBase R Q)
    (hQ' : IsBase R Q') :
    Small R (ev ![P, Q] h + ev ![P, Q'] h - ev ![P, addOf (B.FK k) Q Q'] h) := by
  have p0 : GP (pt k (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt k (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt k (n := 3) d 2) := gp_pt 2
  have c0 := pair_points_zero_constant p0 p1
  have c1 := pair_points_zero_constant p0 p2
  have c2 := pair_points_zero_constant p0 (gp_addOf _ (gp_law B) _ _ p1 p2)
  have w1 : constantCoeff B.ph2 = 1 := by
    rw [← gt_const_ev_eq _ (triple_points_zero_constant (gp_zero₂ (n := 2)) (gp_pt 0) (gp_pt 1)), B.cocycleRight_zero_fst, map_one]
  have key := Small.subst (isBase3 hP hQ hQ') ⟨by
    rw [map_sub, map_add, gt_const_ev_eq _ c0, gt_const_ev_eq _ c1, gt_const_ev_eq _ c2, const_gauge hh,
      add_zero, sub_self], _, w1, hh.ph2⟩
  have hV := triple_points_zero_constant hP.gp hQ.gp hQ'.gp
  rw [gt_ev_sub _ hV, gt_ev_add _ hV, gt_ev_ev' _ _ hV c0, gt_ev_ev' _ _ hV c1, gt_ev_ev' _ _ hV c2,
    eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hV _ _ _ p1 p2, evP_pt _ hV, evP_pt _ hV,
    evP_pt _ hV] at key
  exact key

theorem small_foldr_left (hh : B.IsCanonGauge k h) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b))
    {Q : Pt k m d} (hQ : IsBase R Q) (L : List ι) :
    Small R (ev ![L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0, Q] h -
      (L.map fun b => ev ![g b, Q] h).sum) := by
  induction L with
  | nil => exact small_zero.congr (by rw [List.foldr_nil, gauge_zero_left hh hQ.gp]; simp)
  | cons b L ih =>
    refine (ih.add (small_add_left hh (hg b) (isBase_foldr B hg L) hQ).neg).congr ?_
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    ring

theorem small_foldr_right (hh : B.IsCanonGauge k h) {ι : Type} {g : ι → Pt k m d} (hg : ∀ b, IsBase R (g b))
    {P : Pt k m d} (hP : IsBase R P) (L : List ι) :
    Small R (ev ![P, L.foldr (fun b acc => addOf (B.FK k) (g b) acc) 0] h -
      (L.map fun b => ev ![P, g b] h).sum) := by
  induction L with
  | nil => exact small_zero.congr (by rw [List.foldr_nil, gauge_zero_right hh hP.gp]; simp)
  | cons b L ih =>
    refine (ih.add (small_add_right hh hP (hg b) (isBase_foldr B hg L)).neg).congr ?_
    rw [List.foldr_cons, List.map_cons, List.sum_cons]
    ring

theorem small_sum_scalar (hh : B.IsCanonGauge k h) {ι : Type} (s : Finset ι) (c : ι → O) {P Q : Pt k m d}
    (hP : IsBase R P) (hQ : IsBase R Q) :
    Small R (∑ i ∈ s, ev ![P, comp1 (B.actK k (c i)) Q] h - ev ![P, comp1 (B.actK k (∑ i ∈ s, c i)) Q] h) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := small_add_right hh hP (hQ.act B 0) (hQ.act B 0)
    rw [← add_act B 0 0 hQ.gp, add_zero] at this
    refine this.neg.congr ?_
    rw [Finset.sum_empty, Finset.sum_empty]
    ring
  | insert i s hi ih =>
    have := small_add_right hh hP (hQ.act B (c i)) (hQ.act B (∑ i ∈ s, c i))
    rw [← add_act B _ _ hQ.gp] at this
    refine (ih.add this).congr ?_
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    ring

theorem small_column (hh : B.IsCanonGauge k h) (w0 : O) (y : Fin m → O) :
    Small R (ev (n := m) ![(List.finRange m).foldr
        (fun b acc => addOf (B.FK k) (comp1 (B.actK k (y b)) (pt k d b)) acc) 0] (B.hL k h w0) -
      ∑ b : Fin m, ∑ b' : Fin m,
        ev (n := m) ![pt k d b, comp1 (B.actK k (w0 * (star (y b) * y b'))) (pt k d b')] h) := by
  have hg : ∀ b, IsBase R (comp1 (B.actK k (y b)) (pt k (n := m) d b)) := fun b => (isBase_pt b).act B _
  have hS := isBase_foldr B hg (List.finRange m)
  rw [FB.hL, gt_comp1_pt_right, formalSubst_single_of_formalSubst_two _ hS.gp _ _ (gp_pt 0) (gp_act B w0), gt_comp1_pt _ hS.gp]
  have h1 := small_foldr_left hh hg (hS.act B w0) (List.finRange m)
  rw [← Fin.sum_univ_def] at h1
  refine h1.trans (Small.sum_sub _ fun b => ?_)
  refine (small_balanced hh (y b) (isBase_pt b) (hS.act B w0)).trans ?_
  rw [act_act B _ _ hS.gp, act_foldr B _ hg]
  have h2 := small_foldr_right hh (fun b' => (hg b').act B (star (y b) * w0)) (isBase_pt b) (List.finRange m)
  rw [← Fin.sum_univ_def] at h2
  refine h2.congr ?_
  congr 1
  refine Finset.sum_congr rfl fun b' _ => ?_
  rw [act_act B _ _ (gp_pt b'), show star (y b) * w0 * y b' = w0 * (star (y b) * y b') by ring]

end Gauge

end GlobalTheory.MatrixGauge

namespace GlobalTheory

open MatrixGauge

theorem exists_integral_unit_matrix_gauge :
    ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ (w0 : O) (m n : ℕ) (x : Fin m → Fin n → O), ∃ U : PS R m d, constantCoeff U = 1 ∧ FB.toK k U = FB.expS k ((∑ j : Fin n, ev (n := m) ![(List.finRange m).foldr (fun b acc => addOf (B.FK k) (comp1 (B.actK k (x b j)) (pt k d b)) acc) 0] (B.hL k h w0)) - ∑ b : Fin m, ∑ b' : Fin m, ev (n := m) ![pt k d b, comp1 (B.actK k (w0 * ∑ j : Fin n, star (x b j) * x b' j)) (pt k d b')] h) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 m n x
  have h1 := Small.sum_sub (Finset.univ : Finset (Fin n)) fun j => small_column hh w0 fun b => x b j
  refine (h1.trans ?_).2
  rw [Finset.sum_comm]
  refine Small.sum_sub _ fun b => ?_
  rw [Finset.sum_comm]
  refine Small.sum_sub _ fun b' => ?_
  rw [Finset.mul_sum]
  exact small_sum_scalar hh _ _ (isBase_pt b) (isBase_pt b')

end GlobalTheory
end
end

section
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.ColApprox

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

theorem map_polyT {T : CDVR} {C : Type} [Field C] (φ : T.Fr →+* C) (cx : Lt1 Dw → ℕ) {n : ℕ}
    (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) :
    MvPolynomial.map φ (polyT B cx) = MvPolynomial.aeval (fun ℓ : Let cx => ∑ j,
      MvPolynomial.C (φ (algebraMap T.V T.Fr (B ℓ.1.1.1 ℓ.1.2 j))) *
        (MvPolynomial.X ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩ : MvPolynomial (LtN Dw n) C)) (polyH C cx) := by
  classical
  unfold polyT polyP polyH
  rw [map_prod, map_prod, ← Finset.prod_filter_of_ne (p := fun f => cx f ≠ 0)
    (fun f _ hf h0 => hf (by rw [h0, pow_zero, map_one])),
    Finset.prod_subtype (p := fun f => cx f ≠ 0) _ (fun f => by simp)]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [MvPolynomial.aeval_rename, GlobalTheory.FGDepth.detPow, map_pow, map_pow, RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose]
  congr 2
  ext a b : 2
  simp [GlobalTheory.CombMinor.cMat]

theorem exists_cols {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {p : ℕ} {cx : Lt1 Dw → ℕ} {n : ℕ}
    {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V} (hB : IsCols c T io p cx B) (N : ℕ) :
    ∃ x : Col cx → Fin n → 𝓞 E,
      (∀ b j, ∃ z : T.V, io (embK c b.1.1.1 (x b j)) = algebraMap T.V T.Fr (B b.1.1 b.2 j + (p : T.V) ^ N * z)) ∧
      ∀ b b', ∑ j, H.bar (x b j) * x b' j ∈ Ideal.span {(p : 𝓞 E) ^ N} := by
  obtain ⟨blk, hb⟩ := hB
  choose x h0 h1 h2 using fun f => (hb f).2.2 N
  refine ⟨fun b => x b.1 b.2, fun b j => h1 b.1 b.2 j, ?_⟩
  rintro ⟨f, b⟩ ⟨f', b'⟩
  by_cases hf : f = f'
  · subst hf
    simpa only [mul_comm] using h2 f b' b
  · rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    intro j _
    dsimp only
    by_cases hj : j ∈ Set.range fun j => blk ⟨f, j⟩
    · rw [h0 f' b' j, mul_zero]
      rintro ⟨j2, e2⟩
      obtain ⟨j1, e1⟩ := hj
      exact hf (congrArg Sigma.fst (blk.injective (e1.trans e2.symm)))
    · rw [h0 f b j hj, map_zero, zero_mul]

theorem isIntV_ringHom {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (φ : 𝓞 E →+* X.C) (a : 𝓞 E) :
    IsIntV (vX_vp X) (φ a) := by
  rw [isIntV_iff, ← X.ints.isIntegral_iff_v_le_one]
  exact (map_isIntegral_int φ (Algebra.IsIntegral.isIntegral a)).tower_top

theorem le_v_pow_mul {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) (N : ℕ) {z : X.C}
    (hz : IsIntV (vX_vp X) z) : (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X ((p : X.C) ^ N * z) := by
  rw [AddValuation.map_mul, AddValuation.map_pow, vX_vp_p]
  refine le_add_of_le_of_nonneg (le_of_eq ?_) hz
  simp

theorem lin_col {C : Type} [Field C] {d m : ℕ} {κ : Type} [Fintype κ] {ι : κ → Type} [∀ b, Fintype (ι b)]
    (e : κ ≃ Fin m) (u : ∀ b, ι b → Fin d → C) (q : Fin m) :
    lin (fun ℓ : Σ b, ι b => u ℓ.1 ℓ.2) (fun ℓ => if e ℓ.1 = q then 1 else 0) =
      fun i => ∑ a, u (e.symm q) a i • (MvPowerSeries.X ⟨e.symm q, a⟩ : MvPowerSeries (Σ b, ι b) C) := by
  funext i
  unfold lin
  rw [Fintype.sum_sigma, Finset.sum_eq_single (e.symm q)]
  · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    have hq : e b ≠ q := fun h => hb (by rw [← h]; simp)
    simp [hq]
  · simp

theorem exists_germ_cols : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (g : PS X.C n (chD Ch.ch)), MvIsInt (vX_vp X) g → ∃ f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) f ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p _ la T io e _ y Ch X cx n B hB N k g hg
  classical
  letI := io.toAlgebra
  obtain ⟨BT, -, -, -, -, -, -, e7⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y Ch
  letI : Algebra T.Fr X.C := X.ιF.toAlgebra
  letI : Algebra T.V X.C := (X.ιF.comp (algebraMap T.V T.Fr)).toAlgebra
  haveI : IsScalarTower T.V T.Fr X.C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h1, h2, h3, h4⟩ := e7 X.C
  have hc := (h3 _).2 h4
  let eC := Fintype.equivFin (Col cx)
  let σ : Col cx → 𝓞 E →+* X.C := fun b => X.ιF.comp (io.comp (embK c b.1.1.1))
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct X.C BT a).mulVec (lieVec Ch X ℓ) =
      X.ιF (io (embK c ℓ.1 a)) • lieVec Ch X ℓ := by
    intro a ℓ
    funext i
    have h := congrArg X.ιF (congrFun (GlobalTheory.PowGerm.eigDirSt E H Dw l Xo c T io y Ch a ℓ) i)
    have hu : ∀ i, lieVec Ch X ℓ i = X.ιF (Ch.ch.uvec ℓ i) := fun i =>
      congrArg X.ιF (Ch.gen.1.2.2.2.2.2.2 ℓ i).symm
    simp only [Matrix.mulVec, dotProduct, dAct, h2, hu, Pi.smul_apply, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, dAct, FB.actK, MvPowerSeries.coeff_map, map_sum, map_mul, Pi.smul_apply,
      smul_eq_mul] at h ⊢
    exact h
  obtain ⟨K, hK⟩ := exists_germ_close (v := vX_vp X) BT (G := lawX Ch X) h1.symm (fgl Ch X).F_int
    (fun ℓ : Let cx => eC ℓ.1) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun b a => σ (eC.symm b) a)
    (fun a ℓ => by rw [eC.symm_apply_apply]; exact heig a _) (isIntV_jX X) hc H.w0
    (fun ℓ i => isIntV_jX X _) (fun b a => isIntV_ringHom X _ a)
    (fun x => (GlobalTheory.exists_integral_unit_matrix_gauge _ _ _ _ BT _ hc H.w0 _ n x).imp fun _ h => h.2)
    (polyH X.C cx) k g hg
  obtain ⟨N', hN'⟩ := exists_nat_ge ((N : ℝ) + K)
  obtain ⟨x, hx1, hx2⟩ := exists_cols hB N'
  let β : Col cx → Fin n → X.C := fun b j => jX X (B b.1.1 b.2 j)
  obtain ⟨f, hf, hv⟩ := hK N' (fun b => x (eC.symm b)) (fun b => β (eC.symm b)) (fun b j => isIntV_jX X _)
    (fun b j => by
      obtain ⟨z, hz⟩ := hx1 (eC.symm b) j
      have : β (eC.symm b) j - σ (eC.symm b) (x (eC.symm b) j) = (p : X.C) ^ N' * jX X (-z) := by
        show _ - X.ιF (io (embK c _ _)) = _
        rw [hz]
        show jX X _ - jX X _ = _
        simp
      rw [this]
      exact le_v_pow_mul X N' (isIntV_jX X _))
    (fun b b' => by
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.1 (hx2 (eC.symm b) (eC.symm b'))
      have : σ (eC.symm b') (H.w0 * ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j) =
          (p : X.C) ^ N' * σ (eC.symm b') (H.w0 * r) := by
        rw [show ∑ j, star (x (eC.symm b) j) * x (eC.symm b') j = _ from hr, mul_left_comm, map_mul, map_pow,
          map_natCast]
      rw [this]
      exact le_v_pow_mul X N' (isIntV_ringHom X _ _))
  have cX : ∀ q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch), MvPowerSeries.constantCoeff
      (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C) = 0 := fun q => by simp
  have hE : MvPowerSeries.HasSubst (expH Ch X cx) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun q =>
    nc_exPt (fgl Ch X) (fun i => by simp) q.2
  refine ⟨MvPowerSeries.subst (fun q : Fin (Fintype.card (Col cx)) × Fin (chD Ch.ch) =>
    (MvPowerSeries.X ⟨eC.symm q.1, q.2⟩ : MvPowerSeries (Σ _ : Col cx, Fin (chD Ch.ch)) X.C)) f,
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst _ hf
      (fun q α => by rw [MvPowerSeries.coeff_X]; split_ifs <;> simp [IsIntV]) cX, ?_⟩
  refine le_trans (WithTop.coe_le_coe.2 (by linarith)) (hv.trans (le_of_eq ?_))
  congr 2
  · have hA := GlobalTheory.ExpCoord.constantCoeff_dpolyN_eq_derivAt0 X.C (vX_vp X) _ (lawX Ch X) (fgl Ch X) (fun _ => rfl) n (LtN Dw n) (Let cx)
      (fun ℓ => ℓ.2.2) (fun ℓ => lieVec Ch X ⟨ℓ.1, ℓ.2.1⟩) (fun ℓ => β ℓ.1)
      (fun ℓ j => ⟨ℓ.1.1.1.1, Fin.castLE (rk_le _) ℓ.2, j⟩) (fun ℓ => frame Ch X ℓ.1.1.1 ℓ.2) (fun _ _ => rfl)
      (fun _ _ => rfl) (polyH X.C cx)
    unfold nabX nabValN
    rw [map_polyT]
    simp only [eC.symm_apply_apply, FB.hL, h2]
    exact (hA _).symm
  · rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero cX) hE]
    congr 2
    funext q
    rw [MvPowerSeries.subst_X hE]
    unfold colExp
    rw [lin_col eC (fun b : Col cx => frame Ch X b.1.1)]
    rfl

end GlobalTheory.ColApprox
end
end

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_germ_on_columns_same_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ (N k : ℕ) (g : PS X.C n (chD Ch.ch)), MvIsInt (vX_vp X) g → ∃ f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C, MvIsInt (vX_vp X) f ∧ (((N : ℝ) : ℝ) : WithTop ℝ) ≤ vX_vp X (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g - derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f)) := by
  atlas_forward_decl GlobalTheory.ColApprox.exists_germ_cols
end
