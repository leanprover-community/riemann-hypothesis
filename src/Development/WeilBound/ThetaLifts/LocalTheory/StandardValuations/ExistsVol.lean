import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.SplitProd
import Development.WeilBound.ThetaLifts.LocalTheory.IsArchimedeanLocalEquivariantMap
import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ValIffNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.WeilBound.ThetaLifts.LocalTheory.UatClosure
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.IntIndPow
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsUpperProjectionInverseTranspose
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ResCardAndUniformizer

section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M : Model σ X W} {M₁ : Model σ X₁ W₁}
  {ψ : AddChar (AF F) ℂ}

open Classical Filter in
theorem pure_cancel {κ : Type} [Fintype κ] {w : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hne : ∀ v, w v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, w v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (v : Pl F) {g : SInf F κ}
    (hg : g ≠ 0) {a b : (κ → Fv F v) → ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v a) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update w v b)) : a = b := by
  have := PositivityTheory.ThKF.tensInj F κ w hne hstd {v} 2 ![1, -1] ![g, g] ![Function.update w v a, Function.update w v b]
    (fun i u hu => by
      have : u ≠ v := fun e => hu (Finset.mem_singleton.2 e)
      fin_cases i <;> simp [Function.update_of_ne this]) (by simp [Fin.sum_univ_two, h])
  obtain ⟨z, hz⟩ : ∃ z, g z ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hg (SchwartzMap.ext hn)
  funext y
  let y' : ∀ u : ({v} : Finset (Pl F)), κ → Fv F u := fun u => (Finset.mem_singleton.1 u.2).symm ▸ y
  let m : MultilinearMap ℂ (fun u : ({v} : Finset (Pl F)) => (κ → Fv F u) → ℂ) ℂ :=
    (MultilinearMap.mkPiAlgebra ℂ _ ℂ).compLinearMap fun u => LinearMap.proj (y' u)
  let ez : SInf F κ →ₗ[ℂ] ℂ := ⟨⟨fun f => f z, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have h2 := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ ez (PiTensorProduct.lift m))) this
  have hm : ∀ c : (κ → Fv F v) → ℂ, m (fun u => Function.update w v c u) = c y := fun c => by
    simp only [m, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply]
    rw [Fintype.prod_eq_single (⟨v, Finset.mem_singleton_self v⟩ : ({v} : Finset (Pl F)))
      fun u hu => absurd (Subtype.ext (Finset.mem_singleton.1 u.2)) hu]
    simp [y']
  simp only [Fin.sum_univ_two, map_add, map_smul, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, PiTensorProduct.lift.tprod,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, LinearMap.mul_apply', hm] at h2
  have h3 : g z * (a y - b y) = 0 := by
    change (1 : ℂ) • (g z * a y) + (-1 : ℂ) • (g z * b y) = 0 at h2
    simp only [smul_eq_mul] at h2
    linear_combination h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hz)

theorem opF_eq {κ : Type} [Fintype κ] {T} {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB _) (h₁ : φ₁ ∈ SB _) (h : Acts (evFin F v) T φ φ₁) :
    opF v T φ = φ₁ := by
  have ex : ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) T φ φ₁ := ⟨φ₁, h₁, h⟩
  rw [opF, dif_pos ex]
  exact action_uniqueness F κ v T φ hφ _ _ ex.choose_spec.2 h

def dm {k : Type} [Field k] (Y Z : Matrix (Fin n) (Fin d) k) : k := ofM Y ⬝ᵥ ofM Z

def Hv (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F) (u : Matrix (Fin n) (Fin d) (AE F E)) (φ : Fl F v n d) : Fl F v n d :=
  schr (psiV ψ v) (locW v (M.co.e u)) φ

theorem acts_Hv {u} (hu : At (evFin F v) u) (φ : Fl F v n d) : Acts (evFin F v) (M.co.rho ψ u) φ (Hv M ψ v u φ) :=
  adjoint_statement.Heisenberg₂ F _ ψ v _ (hu.kd_map M.co.e.toLinearMap) φ

theorem Hv_mem (hψ : IsStd ψ) (u) {φ : Fl F v n d} (h : φ ∈ SB _) : Hv M ψ v u φ ∈ SB _ :=
  PositivityTheory.ThKH.Evl.schr_mem ((adjoint_statement.psi F ψ hψ).2 v).1 _ h

structure Lin (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (c₁ c₂ : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (Fv F v))
    (ι : Fl F v n d →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)) : Prop where
  bij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _)
  act : ∀ u, At (evFin F v) u → dm (c₁ u) (c₂ u) = 0 → ∀ φ ∈ SB _,
    ι (Hv M ψ v u φ) = fun Y => psiV ψ v (dm Y (c₂ u)) * ι φ (Y + c₁ u)
  sur : ∀ P Q, ∃ u, At (evFin F v) u ∧ c₁ u = P ∧ c₂ u = Q
  vac : ι (M.vac v) = intInd v

theorem lin_of (hψ : IsStd ψ) {π₁ π₀ : AE F E →+* Fv F v} {c₁ c₂ ι} (hι : M.IsLin ψ π₁ π₀ c₁ ι) (hv : ι (M.vac v) = intInd v)
    (hs : ∀ x u, At (evFin F v) x → x.map π₀ = 0 →
      symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) x u = sgl v (dm (c₁ x) (c₂ u)))
    (dec : ∀ u, At (evFin F v) u → ∃ u₁ u₀, At (evFin F v) u₁ ∧ At (evFin F v) u₀ ∧ u = u₁ + u₀ ∧ u₁.map π₀ = 0 ∧ u₀.map π₁ = 0 ∧
      c₁ u₁ = c₁ u ∧ c₂ u₀ = c₂ u)
    (sur : ∀ P Q, ∃ u, At (evFin F v) u ∧ c₁ u = P ∧ c₂ u = Q) : Lin M ψ v c₁ c₂ ι := by
  refine ⟨hι.bij, fun u hu h0 φ hφ => funext fun Y => ?_, sur, hv⟩
  obtain ⟨u₁, u₀, a1, a0, rfl, b1, b0, e1, e0⟩ := dec u hu
  have e : Hv M ψ v (u₁ + u₀) φ = Hv M ψ v u₁ (Hv M ψ v u₀ φ) := by
    have f := congrArg (evFin F v) ((M.co.form u₁ u₀).symm.trans (hs u₁ u₀ a1 b1))
    rw [ev_sgl, e1, e0, h0, map_sub, ev_dot, ev_dot] at f
    rw [Hv, Hv, Hv, KCo.schr_schr, map_add, locW_add]
    erw [f]
    simp
  obtain ⟨x, hx, x1, -⟩ := sur (Y + c₁ u₁) 0
  obtain ⟨x₁, x₀, xa, -, -, xb, -, xe, -⟩ := dec x hx
  rw [e, hι.trans u₁ a1 b1 _ (Hv_mem hψ _ hφ) _ (Hv_mem hψ _ (Hv_mem hψ _ hφ)) (acts_Hv a1 _), ← x1, ← xe,
    hι.mult u₀ a0 b0 φ hφ _ (Hv_mem hψ _ hφ) (acts_Hv a0 _) x₁ xa xb, hs x₁ u₀ xa xb, xe, x1, e1, e0]
  congr 1
  show psiV ψ v _ = _
  congr 1
  rw [dm, show ofM (Y + c₁ (u₁ + u₀)) = ofM Y + ofM (c₁ (u₁ + u₀)) from rfl, add_dotProduct]
  rw [show ofM (c₁ (u₁ + u₀)) ⬝ᵥ ofM (c₂ (u₁ + u₀)) = 0 from h0, add_zero]; rfl

variable (t) in

def cW (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ

variable (σ t X W) in

def cB (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (u : Matrix (Fin n) (Fin d) (AE F E)) : Matrix (Fin n) (Fin d) (Fv F v) :=
  -(b.1ᵀ * X.J.map t * u.map (piW (t.comp σ)) * (W.J.map t)ᵀ * c.1)

variable {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)}

theorem symp_c (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {u} (hu : At (evFin F v) u) (u') :
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u u' =
      sgl v (dm (cW t b c u) (cB σ t X W b c u') - dm (cW t b c u') (cB σ t X W b c u)) := by
  have key : ∀ U N : Matrix (Fin n) (Fin d) (Fv F v), dm ((b⁻¹).1 * U * (c⁻¹).1ᵀ) (-(b.1ᵀ * N * c.1)) = -(ofM (-N) ⬝ᵥ ofM (-U)) := by
    intro U N
    rw [dm, dotProduct_comm (ofM (-N)), dot_ofM, dot_ofM]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, Matrix.neg_mul, transpose_neg, neg_neg, trace_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (b⁻¹).1ᵀ, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul, trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [symp_eq h hG hu, coord, coord, incM_map h, incM_map h]
  congr 1
  have e : ∀ w : Matrix (Fin n) (Fin d) (AE F E), cB σ t X W b c w =
      -(b.1ᵀ * (X.J.map t * w.map (piW (t.comp σ)) * (W.J.map t)ᵀ) * c.1) := fun w => by simp only [cB, Matrix.mul_assoc]
  rw [e, e, cW, cW, key, key]
  ring

theorem dec_c (h : IsSec σ t sec) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evFin F v) u) :
    u = secM sec (u.map (piW t)) 0 + secM sec 0 (u.map (piW (t.comp σ))) :=
  h.extM (hu.kd_sub ((h.atM _ _).kd_add (h.atM _ _))) (by rw [Matrix.map_add _ (map_add _), h.fstM, h.fstM, add_zero])
    (by rw [Matrix.map_add _ (map_add _), h.sndM, h.sndM, zero_add])

theorem sur_c (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) (P Q) :
    ∃ u, At (evFin F v) u ∧ cW t b c u = P ∧ cB σ t X W b c u = Q := by
  obtain ⟨A, hA⟩ := hG.uA
  obtain ⟨B, hB⟩ := hG.uB
  rw [incM_map h] at hA hB
  refine ⟨secM sec (b.1 * P * c.1ᵀ) (-((A⁻¹).1 * (b⁻¹).1ᵀ * Q * (c⁻¹).1 * (B⁻¹).1ᵀ)), h.atM _ _, ?_, ?_⟩
  · rw [cW, h.fstM, cancel_lr]
  · rw [cB, h.sndM, ← hA, ← hB]
    simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A.1, Units.mul_inv, Matrix.one_mul, ← Matrix.mul_assoc b.1ᵀ, ← transpose_mul, Units.inv_mul, transpose_one,
      Matrix.one_mul, ← Matrix.mul_assoc (B⁻¹).1ᵀ, ← transpose_mul, Units.mul_inv, transpose_one, Matrix.one_mul, Units.inv_mul,
      Matrix.mul_one]

theorem local_splitting_linear_skew (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι} (hι : M.IsLinW ψ t b c ι)
    (hv : ι (M.vac v) = intInd v) : Lin M ψ v (cW t b c) (cB σ t X W b c) ι :=
  lin_of hψ hι hv (fun x u hx h0 => by
      rw [symp_c (b := b) (c := c) h hG hx, show cB σ t X W b c x = 0 by simp [cB, h0],
        show dm (cW t b c u) 0 = 0 from dotProduct_zero _, sub_zero])
    (fun u hu => ⟨_, _, h.atM _ _, h.atM _ _, dec_c h hu, h.sndM _ _, h.fstM _ _, by simp only [cW, h.fstM], by simp only [cB, h.sndM]⟩)
    (sur_c h hG)

theorem lin_Bar (hψ : IsStd ψ) (h : IsSec σ t sec) (hG : Grams σ t (incM F X.J) (incM F W.J)) {ι} (hι : M.IsLinBar ψ t b c ι)
    (hv : ι (M.vac v) = intInd v) : Lin M ψ v (cB σ t X W b c) (fun u => -cW t b c u) ι :=
  lin_of hψ hι hv (fun x u hx h0 => by
      rw [symp_c (b := b) (c := c) h hG hx, show cW t b c x = 0 by simp [cW, h0]]
      congr 1
      show (0 : Fin n × Fin d → Fv F v) ⬝ᵥ _ - _ = ofM (cB σ t X W b c x) ⬝ᵥ (-ofM (cW t b c u))
      rw [zero_dotProduct, zero_sub, dotProduct_neg, dotProduct_comm]; rfl)
    (fun u hu => ⟨_, _, h.atM _ _, h.atM _ _, (dec_c h hu).trans (add_comm _ _), h.fstM _ _, h.sndM _ _, by simp only [cB, h.sndM],
      by simp only [cW, h.fstM]⟩)
    fun P Q => let ⟨u, a, b, c⟩ := sur_c h hG (-Q) P; ⟨u, a, c, by rw [b, neg_neg]⟩

open Classical in
theorem ev_loc {B : Base F E} (hψ : IsStd B.ψ) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev} (hl : IsEvLoc M M₁ e ei ev)
    {u u₁} (hu : At (evFin F v) u) (hu₁ : At (evFin F v) u₁)
    (H : ∀ Φ ∈ schA F _, e (M.co.rho B.ψ u Φ) = M₁.co.rho B.ψ u₁ (e Φ)) {φ : Fl F v n d} (hφ : φ ∈ SB _) :
    ev v (Hv M B.ψ v u φ) = Hv M₁ B.ψ v u₁ (ev v φ) := by
  obtain ⟨f, hf⟩ := DFunLike.ne_iff.1 hl.ne
  have sb : ∀ {x : Fl F v n d}, x ∈ SB _ → ∀ w, Function.update M.vac v x w ∈ SB _ := fun {x} hx w => by
    rcases eq_or_ne w v with rfl | h
    · rwa [Function.update_self]
    · rw [Function.update_of_ne h]; exact (g.vac w).1
  have cf : ∀ x : Fl F v n d, ∀ᶠ w in Filter.cofinite, Function.update M.vac v x w = M.vac w := fun x => by
    filter_upwards [(Set.finite_singleton v).compl_mem_cofinite] with w hw using Function.update_of_ne hw _ _
  have st : ∀ x : Fl F v n d, ∀ᶠ w in Filter.cofinite, Function.update M.vac v x w =
      Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := fun x => by
    filter_upwards [cf x, g.std] with w h1 h2 using h1.trans h2
  have pe : ∀ {x : Fl F v n d}, x ∈ SB _ → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update M.vac v x)) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (Function.update M₁.vac v (ev v x)) := fun {x} hx => by
    rw [hl.pure f _ (sb hx) (cf x)]
    congr 1
    funext w
    rcases eq_or_ne w v with rfl | h
    · simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, (hl.vac w).1]
  have em : ev v φ ∈ SB _ := (hl.vac v).2 ▸ Submodule.mem_map_of_mem hφ
  have a1 := (PositivityTheory.ThKF.pureAct F _ v (M.co.rho B.ψ u) f _ (sb hφ) (st φ)).2.2 (Hv M B.ψ v u φ)
    (by rw [Function.update_self]; exact acts_Hv hu φ)
  have a2 := (PositivityTheory.ThKF.pureAct F _ v (M₁.co.rho B.ψ u₁) (ei f) (Function.update M₁.vac v (ev v φ)) (fun w => by
      rcases eq_or_ne w v with rfl | h
      · rwa [Function.update_self]
      · rw [Function.update_of_ne h]; exact (g₁.vac w).1) (by
      filter_upwards [(Set.finite_singleton v).compl_mem_cofinite, g₁.std] with w hw h2 using
        (Function.update_of_ne hw _ _).trans h2)).2.2 (Hv M₁ B.ψ v u₁ (ev v φ)) (by rw [Function.update_self]; exact acts_Hv hu₁ _)
  rw [Function.update_idem] at a1 a2
  refine pure_cancel (fun w => (g₁.vac w).2.1) g₁.std v hf ?_
  rw [← pe (Hv_mem hψ u hφ), ← a2, ← pe hφ, ← H _ (pure_mem_schA f _ (sb hφ) (st φ)), a1]

theorem Hv_zero (φ : Fl F v n d) : Hv M ψ v 0 φ = φ := by
  rw [Hv, map_zero, show locW v (0 : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) = (0, 0) from
    Prod.ext (funext fun _ => map_zero _) (funext fun _ => map_zero _), schr_zero']

def tmH {k : Type} [TopologicalSpace k] : (Fin n × Fin d → k) ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun Z := Matrix.of fun i j => Z (i, j)
  invFun Y p := Y p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun _ => continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id.matrix_elem _ _

theorem sb_comp {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) {Φ : B → ℂ} (h : Φ ∈ SB B) : Φ ∘ e ∈ SB A :=
  ⟨h.1.comp_continuous e.continuous, h.2.comp_homeomorph e⟩

theorem isPsi (hψ : IsStd ψ) (hu : PsiUnr ψ v) : IsPsi (psiV ψ v) :=
  ⟨((adjoint_statement.psi F ψ hψ).2 v).1, fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hψ _, fun x => by
    have := hu x
    simp only [int_iff] at this
    exact this⟩

theorem intInd_eq (Z : Fin n × Fin d → Fv F v) : intInd v (tmH Z) = one _ Z := by
  classical
  simp only [intInd, one, ind, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff, Set.indicator, map_one,
    Set.mem_setOf_eq, int_iff, Prod.forall]
  rfl

theorem ext_single {k : Type} [Field k] (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (i j) (s : k) :
    emb k jr * single i j s * (emb k jc)ᵀ = single (jr i) (jc j) s := by
  ext p q
  simp only [emb, Matrix.mul_apply, single_apply, ite_and, of_apply, transpose_apply, mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j (fun x _ hx => by simp [hx.symm]) (by simp)]
  simp only [eq_comm, if_true, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ]
  split_ifs <;> rfl

theorem ev_model [SecondCountableTopology (Fv F v)] [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)] {m : Measure (Fv F v)}
    (hm : IsVol m) {B : Base F E} (hψ : IsStd B.ψ) (hu : PsiUnr B.ψ v) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {i i' I e ei ev}
    (he : IsEv B M M₁ i i' I e) (hl : IsEvLoc M M₁ e ei ev) {c₁ c₂ ι c₁' c₂' ι₁} (L : Lin M B.ψ v c₁ c₂ ι)
    (L₁ : Lin M₁ B.ψ v c₁' c₂' ι₁) (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (P : Finset (Fin n × Fin d))
    (hE : ∀ z, c₁ (incM F i * z * (incM F i')ᵀ) = ext jr jc (c₁' z) ∧ c₂ (incM F i * z * (incM F i')ᵀ) = ext jr jc (c₂' z))
    (hT : ∀ p ∈ P, ∀ s, ∃ u ∈ I, At (evFin F v) u ∧ c₁ u = single p.1 p.2 s ∧ c₂ u = 0)
    (hM : ∀ p ∉ P, (∃ a b, p = (jr a, jc b)) ∨ ∀ s, ∃ u ∈ I, At (evFin F v) u ∧ c₁ u = 0 ∧ c₂ u = single p.1 p.2 s)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) :
    ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut P Z) + ext jr jc y) * wt P Z ∂(Measure.pi fun _ => m) := by
  obtain ⟨j, hj, hj'⟩ := kd_exists_inv L.bij
  have em : ∀ {φ : Fl F v n d}, φ ∈ SB _ → ev v φ ∈ SB _ := fun h => (hl.vac v).2 ▸ Submodule.mem_map_of_mem h
  let l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 0 ∘ₗ ι₁ ∘ₗ ev v ∘ₗ j ∘ₗ LinearMap.funLeft ℂ ℂ tmH.symm
  have hl1 : ∀ φ ∈ SB _, l (ι φ ∘ tmH) = ι₁ (ev v φ) 0 := fun φ h => by
    show ι₁ (ev v (j (ι φ))) 0 = _
    rw [hj' φ h]
  have d0 : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), dm Y 0 = 0 ∧ dm 0 Y = 0 := fun Y => ⟨dotProduct_zero _, zero_dotProduct _⟩
  have d1 : ∀ Y : Matrix (Fin n₁) (Fin d₁) (Fv F v), dm Y 0 = 0 ∧ dm 0 Y = 0 := fun Y => ⟨dotProduct_zero _, zero_dotProduct _⟩
  have x0 : ext jr jc (0 : Matrix _ _ (Fv F v)) = 0 := by simp [ext]
  have ae : ∀ {z : Matrix (Fin n₁) (Fin d₁) (AE F E)}, At (evFin F v) z → At (evFin F v) (incM F i * z * (incM F i')ᵀ) :=
    fun h => (h.kd_mul_left _).kd_mul_right _
  have inv : ∀ u, At (evFin F v) u → dm (c₁ u) (c₂ u) = 0 → (∀ φ ∈ SB _, ι₁ (ev v (Hv M B.ψ v u φ)) 0 = ι₁ (ev v φ) 0) →
      ∀ Φ ∈ SB (Fin n × Fin d → Fv F v), l (fun Y => psiV B.ψ v (Y ⬝ᵥ ofM (c₂ u)) * Φ (Y + ofM (c₁ u))) = l Φ := fun u a b c Φ hΦ => by
    obtain ⟨φ, h1, h2⟩ := L.bij.2.2 (sb_comp tmH.symm hΦ)
    have e1 : Φ = ι φ ∘ tmH := by rw [h2]; rfl
    rw [e1, hl1 φ h1, ← c φ h1, ← hl1 _ (Hv_mem hψ u h1), L.act u a b φ h1]
    rfl
  have invI : ∀ u ∈ I, At (evFin F v) u → ∀ φ ∈ SB _, ι₁ (ev v (Hv M B.ψ v u φ)) 0 = ι₁ (ev v φ) 0 := fun u hI a φ h => by
    rw [ev_loc hψ g g₁ hl a (u₁ := 0) (fun _ _ => smul_zero _) (fun Φ hΦ => by
      rw [he.inv u hI Φ hΦ, Darboux.rho, map_zero]; exact (schr_zero' _ _).symm) h, Hv_zero]
  have sg : ∀ (p : Fin n × Fin d) (s : Fv F v), ofM (single p.1 p.2 s) = Pi.single p s := fun p s => funext fun q => by
    simp [ofM, single_apply, Pi.single_apply, Prod.ext_iff, eq_comm]
  have hp := isPsi hψ hu
  have key := evInt hm hp P l (fun Z hZ => ?_) (fun Z hZ => ?_) (by
    rw [← funext intInd_eq, ← L.vac]
    refine (hl1 _ (g.vac v).1).trans ?_
    rw [(hl.vac v).1, L₁.vac]
    simp [intInd, Set.indicator, zero_mem])
  · obtain ⟨z, a, b, c⟩ := L₁.sur y 0
    have e1 := congrFun (L₁.act z a (by rw [c, (d1 _).1]) _ (em hφ)) 0
    rw [c, (d1 _).1, b, zero_add, AddChar.map_zero_eq_one, one_mul] at e1
    rw [← e1, ← ev_loc hψ g g₁ hl (ae a) a (he.Heisenberg₂ z) hφ, ← hl1 _ (Hv_mem hψ _ hφ),
      key _ (sb_comp tmH (L.bij.1 (Hv_mem hψ _ hφ))), L.act _ (ae a) (by rw [(hE z).2, c, x0, (d0 _).1]) φ hφ, (hE z).1, (hE z).2, b, c, x0]
    simp only [Function.comp, (d0 _).1, AddChar.map_zero_eq_one, one_mul]
    rfl
  · let S : AddSubmonoid (Fin n × Fin d → Fv F v) :=
      { carrier := {Z | ∀ Φ ∈ SB (Fin n × Fin d → Fv F v), l (fun Y => Φ (Y + Z)) = l Φ}
        zero_mem' := fun Φ _ => by simp
        add_mem' := fun {a b} ha hb Φ hΦ => by
          rw [← hb Φ hΦ, ← ha (fun Y => Φ (Y + b)) (sb_comp (Homeomorph.addRight b) hΦ)]
          simp [add_assoc] }
    show Z ∈ S
    rw [← Finset.univ_sum_single Z]
    refine S.sum_mem fun p _ => ?_
    by_cases hP : p ∈ P
    · obtain ⟨u, hI, a, b, c⟩ := hT p hP (Z p)
      intro Φ hΦ
      have := inv u a (by rw [c, (d0 _).1]) (invI u hI a) Φ hΦ
      rw [b, c, sg, show ofM (0 : Matrix (Fin n) (Fin d) (Fv F v)) = 0 from rfl] at this
      simpa using this
    · rw [hZ p hP, Pi.single_zero]; exact S.zero_mem
  · let S : AddSubmonoid (Fin n × Fin d → Fv F v) :=
      { carrier := {Z | ∀ Φ ∈ SB (Fin n × Fin d → Fv F v), l (fun Y => psiV B.ψ v (Y ⬝ᵥ Z) * Φ Y) = l Φ}
        zero_mem' := fun Φ _ => by simp
        add_mem' := fun {a b} ha hb Φ hΦ => by
          have := PositivityTheory.ThKH.Evl.schr_mem hp.cont (0, b) hΦ
          rw [show schr (psiV B.ψ v) (0, b) Φ = fun Y => psiV B.ψ v (Y ⬝ᵥ b) * Φ Y from funext fun _ => by simp [schr]] at this
          rw [← hb Φ hΦ, ← ha _ this]
          simp [AddChar.map_add_eq_mul, mul_assoc] }
    show Z ∈ S
    rw [← Finset.univ_sum_single Z]
    refine S.sum_mem fun p _ => ?_
    by_cases hP : p ∈ P
    · rw [hZ p hP, Pi.single_zero]; exact S.zero_mem
    intro Φ hΦ
    have o0 : ofM (0 : Matrix (Fin n) (Fin d) (Fv F v)) = 0 := rfl
    rcases hM p hP with ⟨a, b, rfl⟩ | h
    · obtain ⟨z, x1, x2, x3⟩ := L₁.sur 0 (single a b (Z (jr a, jc b)))
      have := inv _ (ae x1) (by rw [(hE z).1, x2, x0, (d0 _).2]) (fun φ h => by
        rw [ev_loc hψ g g₁ hl (ae x1) x1 (he.Heisenberg₂ z) h, L₁.act z x1 (by rw [x2, (d1 _).2]) _ (em h), x2]
        simp [(d1 _).2]) Φ hΦ
      rw [(hE z).1, (hE z).2, x2, x3, x0, ext, ext_single, sg (jr a, jc b), o0] at this
      simpa using this
    · obtain ⟨u, hI, a, b, c⟩ := h (Z p)
      have := inv u a (by rw [b, (d0 _).2]) (invI u hI a) Φ hΦ
      rw [b, c, sg, o0] at this
      simpa using this

end PositivityTheory.ThKG.Std
end
end

section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

variable (σ t) in

structure PE (J : Matrix (Fin n) (Fin n) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (b : GL (Fin n) (Fv F v)) (b₁ : GL (Fin n₁) (Fv F v))
    (ι : Matrix (Fin n) (Fin n₁) E) (sk : Fin n₁ → Fin n) : Prop where
  p1 : (b⁻¹).1 * ι.map t = emb (Fv F v) sk * (b₁⁻¹).1
  p2 : b.1ᵀ * J.map t * ι.map (t.comp σ) = emb (Fv F v) sk * (b₁.1ᵀ * J₁.map t)

variable (σ t) in

structure PX (J : Matrix (Fin n) (Fin n) E) (b : GL (Fin n) (Fv F v)) (x y : Fin n → E) (j₀ j₁ : Fin n) (ε : Fv F v) : Prop where
  x1 : (b⁻¹).1 *ᵥ (fun i => t (x i)) = Pi.single j₀ 1
  y1 : (b⁻¹).1 *ᵥ (fun i => t (y i)) = Pi.single j₁ 1
  x2 : (b.1ᵀ * J.map t) *ᵥ (fun i => t (σ (x i))) = Pi.single j₁ ε
  y2 : (b.1ᵀ * J.map t) *ᵥ (fun i => t (σ (y i))) = Pi.single j₀ 1

theorem pe_one (J : Matrix (Fin n) (Fin n) E) (b : GL (Fin n) (Fv F v)) : PE σ t J J b b 1 id := by
  have : emb (Fv F v) (id : Fin n → Fin n) = 1 := by ext i j; simp [emb, one_apply]
  refine ⟨?_, ?_⟩ <;> rw [this, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.one_mul]

theorem form_swap (hσ : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {ε : E} (hJ : ∀ i j, σ (J j i) = ε * J i j) (hε : ε * ε = 1)
    (p q : Fin n → E) : form σ J q p = ε * σ (form σ J p q) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hJ, Finset.mul_sum, PositivityTheory.ThK.Vac.sigma_sigma hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  linear_combination (-(q j * J j i * σ (p i))) * hε

theorem plane {B : Base F E} (hσ : IsCMExt F E σ) {H : Plane E n n₁} {i₀ i₁ : ℕ} (h : H.IsAdapted σ B X X₁ i₀ i₁) {ε : E}
    (hJ : ∀ i j, σ (X.J j i) = ε * X.J i j) (hε : ε * ε = 1) (w : B.P) {j₀ j₁ : Fin n} {sk : Fin n₁ → Fin n} (h0 : j₀.1 = i₀)
    (h1 : j₁.1 = i₁) (hs : ∀ j, (sk j).1 = skip i₀ i₁ j) (hi : Function.Injective sk) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = sk j)
    (n01 : j₀ ≠ j₁) (n0 : ∀ j, sk j ≠ j₀) (n1 : ∀ j, sk j ≠ j₁) :
    PE σ (B.τ w) X.J X₁.J (X.bas w) (X₁.bas w) H.ι sk ∧ PX σ (B.τ w) X.J (X.bas w) H.x H.y j₀ j₁ (B.τ w ε) := by
  set t := B.τ w
  set b := X.bas w
  set b₁ := X₁.bas w
  have c0 : ∀ r, b.1 r j₀ = t (H.x r) := (h.bas w j₀).1 h0
  have c1 : ∀ r, b.1 r j₁ = t (H.y r) := (h.bas w j₁).2.1 h1
  have cs : ∀ j r, b.1 r (sk j) = (H.ι.map t * b₁.1) r j := fun j => (h.bas w (sk j)).2.2 j (hs j)
  have e1 : b.1 * emb (Fv F w.1) sk = H.ι.map t * b₁.1 := by
    refine Matrix.ext fun r j => ?_
    rw [← cs]; simp [emb, Matrix.mul_apply]
  have R : ∀ (i : Fin n) (p q : Fin n → E), (∀ r, b.1 r i = t (p r)) →
      ((b.1ᵀ * X.J.map t) *ᵥ fun r => t (σ (q r))) i = t (form σ X.J p q) := fun i p q hp => by
    rw [← mulVec_mulVec]
    simp only [form, dotProduct, mulVec, transpose_apply, hp, map_sum, map_mul, map_apply]
  have S : ∀ (j : Fin n₁) (q : Fin n → E), (∀ u, form σ X.J (H.ι *ᵥ u) q = 0) →
      ((b.1ᵀ * X.J.map t) *ᵥ fun r => t (σ (q r))) (sk j) = 0 := fun j q hq => by
    have a : ∀ k, ((H.ι.map t)ᵀ *ᵥ (X.J.map t *ᵥ fun r => t (σ (q r)))) k = 0 := fun k => by
      have := congrArg t (hq (Pi.single k 1))
      simpa only [form, dotProduct, mulVec, transpose_apply, map_sum, map_mul, map_apply, map_zero, Pi.single_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using this
    have : ((b.1 * emb (Fv F w.1) sk)ᵀ *ᵥ (X.J.map t *ᵥ fun r => t (σ (q r)))) j = 0 := by
      rw [e1, transpose_mul, ← mulVec_mulVec, show (H.ι.map t)ᵀ *ᵥ _ = 0 from funext a, mulVec_zero]; rfl
    rw [transpose_mul, ← mulVec_mulVec, mulVec_mulVec _ b.1ᵀ] at this
    simpa [emb, mulVec, dotProduct] using this
  have col : ∀ (j : Fin n) (p : Fin n → E), (∀ r, b.1 r j = t (p r)) → (b⁻¹).1 *ᵥ (fun i => t (p i)) = Pi.single j 1 := fun j p hp => by
    rw [show (fun i => t (p i)) = b.1 *ᵥ Pi.single j 1 from funext fun r => by simp [← hp], mulVec_mulVec, Units.inv_mul, one_mulVec]
  have yx : form σ X.J H.y H.x = ε := by rw [form_swap hσ hJ hε, h.xy, map_one, mul_one]
  refine ⟨⟨?_, ?_⟩, col _ _ c0, col _ _ c1, funext fun i => ?_, funext fun i => ?_⟩
  · rw [← Matrix.mul_one (H.ι.map t), ← Units.mul_inv b₁, ← Matrix.mul_assoc (H.ι.map t), ← e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  · refine Matrix.ext fun i k => ?_
    have a : (b.1ᵀ * X.J.map t * H.ι.map (t.comp σ)) i k = ((b.1ᵀ * X.J.map t) *ᵥ fun r => t (σ ((H.ι *ᵥ Pi.single k 1) r))) i := by
      simp [Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply]
    rcases hc i with rfl | rfl | ⟨j, rfl⟩
    · rw [a, R _ _ _ c0, form_swap hσ hJ hε, (h.orth _).1]
      simp [emb, Matrix.mul_apply, fun j => (n0 j).symm]
    · rw [a, R _ _ _ c1, form_swap hσ hJ hε, (h.orth _).2]
      simp [emb, Matrix.mul_apply, fun j => (n1 j).symm]
    · have g : (H.ι.map t)ᵀ * X.J.map t * H.ι.map (t.comp σ) = X₁.J.map t := by
        rw [← h.gram]
        refine Matrix.ext fun p q => ?_
        simp [Matrix.mul_apply]
      have : ((b.1 * emb (Fv F w.1) sk)ᵀ * X.J.map t * H.ι.map (t.comp σ)) j k = (b₁.1ᵀ * X₁.J.map t) j k := by
        rw [e1, transpose_mul, ← g]; simp only [Matrix.mul_assoc]
      rw [transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc b.1ᵀ] at this
      rw [Matrix.mul_apply (M := emb (Fv F w.1) sk)]
      rw [Matrix.mul_apply] at this
      simpa [emb, hi.eq_iff] using this
  · rcases hc i with rfl | rfl | ⟨j, rfl⟩
    · rw [R _ _ _ c0, h.xx, map_zero, Pi.single_eq_of_ne n01]
    · rw [R _ _ _ c1, yx, Pi.single_eq_same]
    · rw [S _ _ fun u => (h.orth u).1, Pi.single_eq_of_ne (n1 j)]
  · rcases hc i with rfl | rfl | ⟨j, rfl⟩
    · rw [R _ _ _ c0, h.xy, map_one, Pi.single_eq_same]
    · rw [R _ _ _ c1, h.yy, map_zero, Pi.single_eq_of_ne n01.symm]
    · rw [S _ _ fun u => (h.orth u).2, Pi.single_eq_of_ne (n0 j)]

variable {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)} {b₁ : GL (Fin n₁) (Fv F v)} {c₁ : GL (Fin d₁) (Fv F v)}

theorem adelic_inclusion_map_place_section (h : IsSec σ t sec) {α β : Type} (J : Matrix α β E) : (incM F J).map (piW (t.comp σ)) = J.map (t.comp σ) :=
  Matrix.ext fun i j => incM_map' h J i j

theorem emb_c (h : IsSec σ t sec) {ι ι' jr jc} (a : PE σ t X.J X₁.J b b₁ ι jr) (a' : PE σ t W.J W₁.J c c₁ ι' jc) (z) :
    cW t b c (incM F ι * z * (incM F ι')ᵀ) = ext jr jc (cW t b₁ c₁ z) ∧
      cB σ t X W b c (incM F ι * z * (incM F ι')ᵀ) = ext jr jc (cB σ t X₁ W₁ b₁ c₁ z) := by
  constructor
  · rw [cW, Matrix.map_mul, Matrix.map_mul, transpose_map, incM_map h, incM_map h]
    calc _ = ((b⁻¹).1 * ι.map t) * z.map (piW t) * ((c⁻¹).1 * ι'.map t)ᵀ := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [a.p1, a'.p1]; simp only [ext, cW, transpose_mul, Matrix.mul_assoc]
  · rw [cB, Matrix.map_mul, Matrix.map_mul, transpose_map, adelic_inclusion_map_place_section h, adelic_inclusion_map_place_section h]
    calc _ = -((b.1ᵀ * X.J.map t * ι.map (t.comp σ)) * z.map (piW (t.comp σ)) * (c.1ᵀ * W.J.map t * ι'.map (t.comp σ))ᵀ) := by
          simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = _ := by
          rw [a.p2, a'.p2]
          simp only [ext, cB, transpose_mul, transpose_transpose, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

variable (t) in

def v1 (b : GL (Fin n) (Fv F v)) (p : Fin n → AE F E) : Fin n → Fv F v := (b⁻¹).1 *ᵥ fun i => piW t (p i)

variable (σ t) in

def v2 (J : Matrix (Fin n) (Fin n) E) (b : GL (Fin n) (Fv F v)) (p : Fin n → AE F E) : Fin n → Fv F v :=
  (b.1ᵀ * J.map t) *ᵥ fun i => piW (t.comp σ) (p i)

theorem rk_c (p : Fin n → AE F E) (q : Fin d → AE F E) : cW t b c (vecMulVec p q) = vecMulVec (v1 t b p) (v1 t c q) ∧
    cB σ t X W b c (vecMulVec p q) = -vecMulVec (v2 σ t X.J b p) (v2 σ t W.J c q) := by
  have e : ∀ π : AE F E →+* Fv F v, (vecMulVec p q).map π = vecMulVec (fun i => π (p i)) fun j => π (q j) := fun π =>
    Matrix.ext fun i j => map_mul π _ _
  constructor
  · rw [cW, e, mul_vecMulVec, vecMulVec_mul, vecMul_transpose]; rfl
  · rw [cB, e, mul_vecMulVec, Matrix.mul_assoc, vecMulVec_mul, show (W.J.map t)ᵀ * c.1 = (c.1ᵀ * W.J.map t)ᵀ by simp, vecMul_transpose]
    rfl

theorem vec_ex (h : IsSec σ t sec) {J : Matrix (Fin n) (Fin n) E} (hJ : IsUnit (J.map t)) (r r' : Fin n → Fv F v) :
    ∃ p, At (evFin F v) p ∧ v1 t b p = r ∧ v2 σ t J b p = r' := by
  obtain ⟨A, hA⟩ := hJ
  refine ⟨fun i => sec ((b.1 *ᵥ r) i, (((A⁻¹).1 * (b⁻¹).1ᵀ) *ᵥ r') i), fun u hu => funext fun i => h.at' _ u hu, ?_, ?_⟩
  · simp only [v1, h.fst]
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  · simp only [v2, h.snd]
    rw [mulVec_mulVec, ← hA, Matrix.mul_assoc, ← Matrix.mul_assoc A.1, Units.mul_inv, Matrix.one_mul, ← transpose_mul, Units.inv_mul,
      transpose_one, one_mulVec]

theorem vec_sub (h : IsSec σ t sec) {J J₁ ι sk} (a : PE σ t J J₁ b b₁ ι sk) (p : Fin n₁ → AE F E) :
    v1 t b (incM F ι *ᵥ p) = emb (Fv F v) sk *ᵥ v1 t b₁ p ∧ v2 σ t J b (incM F ι *ᵥ p) = emb (Fv F v) sk *ᵥ v2 σ t J₁ b₁ p := by
  have e : ∀ π : AE F E →+* Fv F v, (fun i => π ((incM F ι *ᵥ p) i)) = (incM F ι).map π *ᵥ fun i => π (p i) := fun π =>
    funext fun i => RingHom.map_mulVec π _ _ i
  constructor
  · rw [v1, e, incM_map h, mulVec_mulVec, a.p1, ← mulVec_mulVec]; rfl
  · rw [v2, e, adelic_inclusion_map_place_section h, mulVec_mulVec, a.p2, ← mulVec_mulVec]; rfl

theorem vec_ex' (h : IsSec σ t sec) {J J₁ ι sk} (a : PE σ t J J₁ b b₁ ι sk) (hJ : IsUnit (J₁.map t)) (j : Fin n₁) (s s' : Fv F v) :
    ∃ p, At (evFin F v) (incM F ι *ᵥ p) ∧ v1 t b (incM F ι *ᵥ p) = Pi.single (sk j) s ∧
      v2 σ t J b (incM F ι *ᵥ p) = Pi.single (sk j) s' := by
  obtain ⟨p, h0, h1, h2⟩ := vec_ex (b := b₁) h hJ (Pi.single j s) (Pi.single j s')
  have e : ∀ s : Fv F v, emb (Fv F v) sk *ᵥ Pi.single j s = Pi.single (sk j) s := fun s => funext fun i => by
    simp [emb, Pi.single_apply]
  exact ⟨p, fun u hu => by rw [← mulVec_smul, h0 u hu, mulVec_zero], by rw [(vec_sub h a p).1, h1, e], by rw [(vec_sub h a p).2, h2, e]⟩

theorem vec_inc (h : IsSec σ t sec) {J x y j₀ j₁ ε} (a : PX σ t J b x y j₀ j₁ ε) :
    v1 t b (incV F x) = Pi.single j₀ 1 ∧ v2 σ t J b (incV F x) = Pi.single j₁ ε ∧
      v1 t b (incV F y) = Pi.single j₁ 1 ∧ v2 σ t J b (incV F y) = Pi.single j₀ 1 := by
  simp only [v1, v2, incV, (h.inc _).1, (h.inc _).2]
  exact ⟨a.x1, a.x2, a.y1, a.y2⟩

theorem vec_smul {J : Matrix (Fin n) (Fin n) E} (e : AE F E) (p : Fin n → AE F E) :
    v1 t b (e • p) = piW t e • v1 t b p ∧ v2 σ t J b (e • p) = piW (t.comp σ) e • v2 σ t J b p := by
  simp only [v1, v2, ← mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  exact ⟨rfl, rfl⟩

theorem vmv {k : Type} [Field k] (i : Fin n) (j : Fin d) (a b : k) : vecMulVec (Pi.single i a) (Pi.single j b) = single i j (a * b) := by
  ext p q
  simp only [vecMulVec_apply, Pi.single_apply, single_apply, eq_comm]
  split_ifs <;> simp_all

theorem sneg {k : Type} [Field k] (i : Fin n) (j : Fin d) (a : k) : single i j (-a) = -single i j a := by
  ext p q; simp only [single_apply, Matrix.neg_apply]; split_ifs <;> simp

theorem at_l {p : Fin n → AE F E} (h : At (evFin F v) p) (q : Fin d → AE F E) : At (evFin F v) (vecMulVec p q) := fun u hu => by
  ext i j
  have := congrFun (h u hu) i
  rw [Matrix.smul_apply, vecMulVec_apply, ← smul_mul_assoc, show u • p i = 0 from this, zero_mul]; rfl

theorem at_r (p : Fin n → AE F E) {q : Fin d → AE F E} (h : At (evFin F v) q) : At (evFin F v) (vecMulVec p q) := fun u hu => by
  ext i j
  have := congrFun (h u hu) j
  rw [Matrix.smul_apply, vecMulVec_apply, ← mul_smul_comm, show u • q j = 0 from this, mul_zero]; rfl

theorem col_el (h : IsSec σ t sec) {x y j₀ j₁} (a : PX σ t W.J c x y j₀ j₁ (-1)) {p : Fin n → AE F E} {i s s'}
    (h1 : v1 t b p = Pi.single i s) (h2 : v2 σ t X.J b p = Pi.single i s') :
    cW t b c (vecMulVec p (incV F x)) = single i j₀ s ∧ cB σ t X W b c (vecMulVec p (incV F x)) = single i j₁ s' := by
  rw [(rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, h1, h2, (vec_inc h a).1, (vec_inc h a).2.1, vmv, vmv, mul_one, mul_neg_one, sneg, neg_neg]
  exact ⟨rfl, rfl⟩

theorem row_el (h : IsSec σ t sec) {x y i₀ i₁} (a : PX σ t X.J b x y i₀ i₁ 1) {q : Fin d → AE F E} {j s s'}
    (h1 : v1 t c q = Pi.single j s) (h2 : v2 σ t W.J c q = Pi.single j s') :
    cW t b c (vecMulVec (incV F x) q) = single i₀ j s ∧ cB σ t X W b c (vecMulVec (incV F x) q) = single i₁ j (-s') := by
  rw [(rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, h1, h2, (vec_inc h a).1, (vec_inc h a).2.1, vmv, vmv, one_mul, one_mul, sneg]
  exact ⟨rfl, rfl⟩

theorem idem_smul (h : IsSec σ t sec) (l : AE F E) : piW t (idem F v • l) = piW t l ∧ piW (t.comp σ) (idem F v • l) = piW (t.comp σ) l := by
  have : evFin F v (idem F v) = 1 := ev_sgl 1
  rw [(h.smul _ _).1, (h.smul _ _).2, this, one_mul, one_mul]
  exact ⟨rfl, rfl⟩

theorem shiftA_c (h : IsSec σ t sec) {H : Plane E n n₁} {H' : Plane E d d₁} {i₀ i₁ j₀ j₁} (a : PX σ t X.J b H.x H.y i₀ i₁ 1)
    (a' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (l : (AE F E)ˣ) :
    cW t b c (idem F v • shiftA H H' l) = single i₀ j₁ (piW t l) ∧
      cB σ t X W b c (idem F v • shiftA H H' l) = single i₁ j₀ (-piW (t.comp σ) l) := by
  have e : idem F v • shiftA H H' l = vecMulVec ((idem F v • (l : AE F E)) • incV F H.x) (incV F H'.y) := by
    rw [shiftA, ← smul_assoc, smul_vecMulVec]
  rw [e, (rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, (vec_smul (σ := σ) (J := X.J) _ _).1, (vec_smul (σ := σ) (J := X.J) _ _).2, (vec_inc h a).1, (vec_inc h a).2.1,
    (vec_inc h a').2.2.1, (vec_inc h a').2.2.2, (idem_smul h _).1, (idem_smul h _).2, ← Pi.single_smul, ← Pi.single_smul, vmv, vmv]
  simp [sneg]

theorem shiftB_c (h : IsSec σ t sec) {H : Plane E n n₁} {H' : Plane E d d₁} {i₀ i₁ j₀ j₁} (a : PX σ t X.J b H.x H.y i₀ i₁ 1)
    (a' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (l : (AE F E)ˣ) :
    cB σ t X W b c (idem F v • shiftB σ H H' l) = single i₀ j₁ (piW t l) ∧
      -cW t b c (idem F v • shiftB σ H H' l) = single i₁ j₀ (-piW (t.comp σ) l) := by
  have e : idem F v • shiftB σ H H' l = vecMulVec ((idem F v • cA σ (l : AE F E)) • incV F H.y) (incV F H'.x) := by
    rw [shiftB, ← smul_assoc, smul_vecMulVec]
  rw [e, (rk_c (σ := σ) (X := X) (W := W) _ _).1, (rk_c _ _).2, (vec_smul (σ := σ) (J := X.J) _ _).1, (vec_smul (σ := σ) (J := X.J) _ _).2, (vec_inc h a).2.2.1, (vec_inc h a).2.2.2,
    (vec_inc h a').1, (vec_inc h a').2.1, (idem_smul h _).1, (idem_smul h _).2, (h.conj _).1, (h.conj _).2, ← Pi.single_smul,
    ← Pi.single_smul, vmv, vmv]
  simp [sneg]

theorem inB_mem (h : IsSec σ t sec) {B : Base F E} (hb : IsSplitBasis t X.L b) {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {k}
    (hk : k ∈ K) : inB t b k ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) := by
  have to' : ∀ z ∈ latHat X, (fun i => piW t (z i)) ∈ splitLat t X.L := fun z hz => by
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, -, ha, x, hx, rfl⟩ := hz
      exact ⟨fun i => evFin F v a ⊗ₜ[F] x i, AddSubgroup.subset_closure ⟨_, ha v, x, hx, rfl⟩, funext fun i => by
        rw [Pi.smul_apply, (h.smul _ _).1, incV, (h.inc _).1]; rfl⟩
    | zero => simp only [Pi.zero_apply, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => simp only [Pi.add_apply, map_add]; exact add_mem ha hb
    | neg a _ ha => simp only [Pi.neg_apply, map_neg]; exact neg_mem ha
  have fr : ∀ y ∈ latLoc F X.L v, ∃ z ∈ latHat X, (fun i => piW t (z i)) = splitVec t y := fun y hy => by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      refine ⟨sgl v a • incV F x, AddSubgroup.subset_closure ⟨sgl v a, map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun u => ?_,
        x, hx, rfl⟩, funext fun i => by rw [Pi.smul_apply, (h.smul _ _).1, incV, (h.inc _).1, ev_sgl]; rfl⟩
      rcases eq_or_ne u v with rfl | hu
      · rwa [ev_sgl]
      · rw [show evFin F u (sgl v a) = 0 from evalV_singleFin_ne hu a]; exact zero_mem _
    | zero => exact ⟨0, zero_mem _, funext fun _ => (map_zero _).trans (map_zero _).symm⟩
    | add a b _ _ ha hb =>
      obtain ⟨p, p1, p2⟩ := ha
      obtain ⟨q, q1, q2⟩ := hb
      exact ⟨p + q, add_mem p1 q1, funext fun i => by
        rw [Pi.add_apply, map_add, congrFun p2 i, congrFun q2 i]; exact (map_add _ _ _).symm⟩
    | neg a _ ha =>
      obtain ⟨p, p1, p2⟩ := ha
      exact ⟨-p, neg_mem p1, funext fun i => by rw [Pi.neg_apply, map_neg, congrFun p2 i]; exact (map_neg _ _).symm⟩
  have key : ∀ k ∈ K, ∀ i j, (inB t b k).1 i j ∈ 𝒪[Fv F v] := fun k hk i j => by
    obtain ⟨y, hy, e⟩ := (hb (Pi.single j 1)).1 fun i => by rw [Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    obtain ⟨z, hz, e'⟩ := fr y hy
    have := hb.mem_iff.1 (to' _ (((hK k).1 hk).2 z hz).1) i
    rw [show (fun i => piW t ((mat k *ᵥ z) i)) = (mat k).map (piW t) *ᵥ fun i => piW t (z i) from
      funext fun i => RingHom.map_mulVec _ _ _ i, e', e, mulVec_mulVec, mulVec_mulVec, mulVec_single_one] at this
    exact (int_iff _).1 this
  refine (mem_KO_iff _).2 ⟨key k hk, ?_⟩
  rw [show (inB t b k)⁻¹ = inB t b k⁻¹ by simp [inB, mul_assoc]]
  exact key _ (inv_mem hk)

end PositivityTheory.ThKG.Std
end
end

section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

theorem cont_piW (t : E →ₐ[F] Fv F v) : Continuous (piW t) := by
  have hev : Continuous (evFin F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact (continuous_splitProj t).comp (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap
    (fun a b => map_mul (evFin F v) a b) hev)

theorem at_mul {a b : AE F E} (ha : At (evFin F v) (a - 1)) (hb : At (evFin F v) (b - 1)) : At (evFin F v) (a * b - 1) := fun u hu => by
  rw [show a * b - 1 = (a - 1) * b + (b - 1) by ring, smul_add, ← smul_mul_assoc, ha u hu, hb u hu, zero_mul, add_zero]

theorem at_idAt {l : (AE F E)ˣ} (h : l ∈ idAt E (evFin F v)) : At (evFin F v) ((l : AE F E) - 1) := by
  induction h using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => intro u _; simp
  | mul a b _ _ ha hb => exact at_mul ha hb
  | inv a _ ha =>
    intro u hu
    rw [show ((a⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -(((a : AE F E) - 1) * (a⁻¹ : (AE F E)ˣ)) by simp [sub_mul], smul_neg,
      ← smul_mul_assoc, ha u hu, zero_mul, neg_zero]

theorem ext1 (h : IsSec σ t sec) {a b : AE F E} (ha : At (evFin F v) (a - 1)) (hb : At (evFin F v) (b - 1)) (h1 : piW t a = piW t b)
    (h2 : piW (t.comp σ) a = piW (t.comp σ) b) : a = b := by
  have := ha.kd_sub hb
  rw [sub_sub_sub_cancel_right] at this
  exact sub_eq_zero.1 (h.ext _ this (by rw [map_sub, h1, sub_self]) (by rw [map_sub, h2, sub_self]))

def uI (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : idAt E (evFin F v) :=
  have at1 : ∀ p, At (evFin F v) (1 + sec p - 1) := fun p => by rw [add_sub_cancel_left]; exact h.at' p
  have m : ∀ x y : (Fv F v)ˣ, (1 + sec (x - 1, y - 1)) * (1 + sec ((x⁻¹ : (Fv F v)ˣ) - 1, (y⁻¹ : (Fv F v)ˣ) - 1)) = 1 := fun x y =>
    ext1 h (at_mul (at1 _) (at1 _)) (fun u _ => by simp) (by simp [h.fst]) (by simp [h.snd])
  ⟨⟨1 + sec (x - 1, y - 1), 1 + sec ((x⁻¹ : (Fv F v)ˣ) - 1, (y⁻¹ : (Fv F v)ˣ) - 1), m x y, by rw [mul_comm]; exact m x y⟩,
    Subgroup.subset_closure (at1 _)⟩

theorem uI_fst (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : piW t ((uI h x y).1 : AE F E) = x := by
  show piW t (1 + _) = _
  simp [h.fst]

theorem uI_snd (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : piW (t.comp σ) ((uI h x y).1 : AE F E) = y := by
  show piW _ (1 + _) = _
  simp [h.snd]

def cmp (t : E →ₐ[F] Fv F v) : idAt E (evFin F v) →* (Fv F v)ˣ :=
  (Units.map (piW t).toMonoidHom).comp (idAt E (evFin F v)).subtype

theorem cmp_val (l : idAt E (evFin F v)) : (cmp t l : Fv F v) = piW t (l.1 : AE F E) := rfl

theorem ext2 (h : IsSec σ t sec) {a b : idAt E (evFin F v)} (h1 : cmp t a = cmp t b) (h2 : cmp (t.comp σ) a = cmp (t.comp σ) b) :
    a = b := Subtype.ext (Units.ext (ext1 h (at_idAt a.2) (at_idAt b.2) (congrArg Units.val h1) (congrArg Units.val h2)))

theorem cmp_uI (h : IsSec σ t sec) (x y : (Fv F v)ˣ) : cmp t (uI h x y) = x ∧ cmp (t.comp σ) (uI h x y) = y :=
  ⟨Units.ext (uI_fst h x y), Units.ext (uI_snd h x y)⟩

theorem chr_id (hσ : IsCMExt F E σ) (χ : Chr F E) (l : idAt E (evFin F v)) :
    (χ l.1 : ℂ) = chrW χ t (cmp t l) * chrW χ (t.comp σ) (cmp (t.comp σ) l) := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  obtain ⟨⟨sec', h'⟩, -⟩ := section_statement F E σ hσ v (t.comp σ)
  have e : l = uI h (cmp t l) 1 * uI h 1 (cmp (t.comp σ) l) := ext2 h (by simp [cmp_uI]) (by simp [cmp_uI])
  conv_lhs => rw [e]
  rw [Subgroup.coe_mul, map_mul, Circle.coe_mul, (h.idele _ _ (at_idAt (uI h _ 1).2) (uI_fst h _ _) (uI_snd h _ _)).1 χ,
    (h'.idele _ _ (at_idAt (uI h 1 _).2) (uI_snd h _ _) (by rw [comp_comp hσ]; exact uI_fst h _ _)).1 χ]

theorem abs_id (hσ : IsCMExt F E σ) (l : idAt E (evFin F v)) :
    (absE F E l.1 : ℝ) = GlobalTheory.SplitWeil.nabs _ (cmp t l) * GlobalTheory.SplitWeil.nabs _ (cmp (t.comp σ) l) := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  have e1 : l.1 = GlobalTheory.Doubling.ideleAt F E v (GlobalTheory.Doubling.unitFin F E v l.1) := Units.ext (by
    change (l.1 : AE F E) = 1 - GlobalTheory.EmbChart.tensAt E v 1 + GlobalTheory.EmbChart.tensAt E v (compFin F E v l.1)
    have o := off_of_at (at_idAt l.2)
    rw [← PositivityTheory.Member.ZakTransform.ep_smul, ← map_one (compFin F E v), ← PositivityTheory.Member.ZakTransform.ep_smul]
    rw [sub_smul, sub_smul, one_smul, one_smul] at o
    rw [← o, sub_add_cancel])
  have e2 : evFin F v (Algebra.norm (AF F) (l.1 : AE F E)) = cmp t l * cmp (t.comp σ) l := by
    have := congrArg (piW t) (GlobalTheory.Doubling.algebraMap_norm_eq hσ (l.1 : AE F E))
    rw [Algebra.algebraMap_eq_smul_one, (h.smul _ _).1, map_one, mul_one, map_mul] at this
    rw [this]
    exact congrArg _ (h.conj _).1
  rw [e1, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_unitFin, e2, coe_nnnorm, norm_mul,
    norm_nabs, norm_nabs]

theorem units_eq (h : IsSec σ t sec) : {l | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} =
    {l | valuation _ (cmp t l : Fv F v) = 1 ∧ valuation _ (cmp (t.comp σ) l : Fv F v) = 1} := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  ext l
  constructor
  · intro hl
    have key : ∀ s : E →ₐ[F] Fv F v, valuation _ (cmp s l : Fv F v) = 1 := fun s => by
      have hc : Continuous fun a : idAt E (evFin F v) => ‖(cmp s a : Fv F v)‖ :=
        ((cont_piW s).comp (Units.continuous_val.comp continuous_subtype_val)).norm
      obtain ⟨C, hC⟩ := (IsCompact.image hl hc).bddAbove
      have hb : ∀ n : ℤ, ‖(cmp s l : Fv F v)‖ ^ n ≤ C := fun n => by
        have := hC ⟨l ^ n, subset_closure ⟨n, rfl⟩, rfl⟩
        simpa only [map_zpow, Units.val_zpow_eq_zpow_val, norm_zpow] using this
      have h0 : 0 < ‖(cmp s l : Fv F v)‖ := norm_pos_iff.2 (cmp s l).ne_zero
      rw [val_iff_norm]
      by_contra hne
      rcases lt_or_gt_of_ne hne with h1 | h1
      · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ((one_lt_inv₀ h0).2 h1)
        exact absurd (hb (-n)) (by rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]; exact not_le.2 hn)
      · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h1
        exact absurd (hb n) (by rw [zpow_natCast]; exact not_le.2 hn)
    exact ⟨key _, key _⟩
  · rintro ⟨h1, h2⟩
    have cs : Continuous sec := by
      have : sec = fun p => sgl v p.1 • sec (1, 0) + sgl v p.2 • sec (0, 1) := funext fun p =>
        sub_eq_zero.1 (h.ext _ ((h.at' p).kd_sub ((at_sgl_smul _ _).kd_add (at_sgl_smul _ _)))
          (by simp [(h.smul _ _).1, h.fst, ev_sgl]) (by simp [(h.smul _ _).2, h.snd, ev_sgl]))
      have c1 : Continuous (sgl (F := F) v) := continuous_const.prodMk (continuous_singleFin v)
      rw [this]
      exact ((c1.comp continuous_fst).smul continuous_const).add ((c1.comp continuous_snd).smul continuous_const)
    have cu : Continuous fun p : (Fv F v)ˣ × (Fv F v)ˣ => uI h p.1 p.2 := by
      refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
      · exact continuous_const.add (cs.comp (((Units.continuous_val.comp continuous_fst).sub continuous_const).prodMk
          ((Units.continuous_val.comp continuous_snd).sub continuous_const)))
      · exact continuous_const.add (cs.comp (((Units.continuous_coe_inv.comp continuous_fst).sub continuous_const).prodMk
          ((Units.continuous_coe_inv.comp continuous_snd).sub continuous_const)))
    have ck : IsCompact {x : (Fv F v)ˣ | valuation _ (x : Fv F v) = 1} := by
      rw [Units.isEmbedding_val₀.isCompact_iff]
      have : Units.val '' {x : (Fv F v)ˣ | valuation _ (x : Fv F v) = 1} =
          {x | valuation _ x ≤ valuation (Fv F v) 1} ∩ Metric.sphere 0 1 := by
        ext x
        simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, mem_sphere_zero_iff_norm, ← val_iff_norm, map_one]
        exact ⟨by rintro ⟨u, hu, rfl⟩; exact ⟨hu.le, hu⟩, fun hx => let ⟨u, hu⟩ := exists_unit hx.2; ⟨u, hu ▸ hx.2, hu⟩⟩
      rw [this]
      exact (IsNonarchimedeanLocalField.isCompact_closedBall _ _).inter_right Metric.isClosed_sphere
    refine ((ck.prod ck).image cu).closure_of_subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨(cmp t (l ^ n), cmp (t.comp σ) (l ^ n)), ⟨by simp [h1], by simp [h2]⟩, ext2 h (cmp_uI h _ _).1 (cmp_uI h _ _).2⟩

theorem idele_int (hσ : IsCMExt F E σ) [SecondCountableTopology (Fv F v)] [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)]
    {m : Measure (Fv F v)} (hm : IsVol m) {ψ : AddChar (Fv F v) ℂ} (hψ : IsPsi ψ) {ϖ : (Fv F v)ˣ} (hϖ : IsUnif ϖ) (χ : Chr F E)
    (hχ : ∀ x, chrW χ (t.comp σ) x = (chrW χ t x)⁻¹) {c : ℕ} (hν : CondLE ϖ (c + 1) (chrW χ t)) (hν' : ¬ CondLE ϖ c (chrW χ t))
    (μ : @Measure (idAt E (evFin F v)) (borel _)) (hμ : @Measure.IsHaarMeasure _ _ _ (borel _) μ)
    (h1 : μ {l | IsCompact (closure (Subgroup.zpowers l : Set (idAt E (evFin F v))))} = 1) (C : ℂ) (z : ℕ) :
    @integral _ _ _ _ (borel _) μ (fun l => dl (chrW χ t) (piW t (l.1 : AE F E)) * gI m ψ (chrW χ t) (piW (t.comp σ) (l.1 : AE F E)) * C *
      (χ l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ z) = gI m ψ (chrW χ t) (((ϖ : Fv F v) ^ (c + 1))⁻¹) * (chrW χ t ϖ : ℂ) ^ (c + 1) *
        ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (c + 1)) ^ z * C := by
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hσ v t
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  letI : MeasurableSpace (idAt E (evFin F v)) := borel _
  haveI : BorelSpace (idAt E (evFin F v)) := ⟨rfl⟩
  rw [units_eq h] at h1
  set U := {l : idAt E (evFin F v) | valuation _ (cmp t l : Fv F v) = 1 ∧ valuation _ (cmp (t.comp σ) l : Fv F v) = 1} with hU
  have hc : ∀ s : E →ₐ[F] Fv F v, Continuous fun a : idAt E (evFin F v) => ‖(cmp s a : Fv F v)‖ := fun s =>
    ((cont_piW s).comp (Units.continuous_val.comp continuous_subtype_val)).norm
  have mU : MeasurableSet U := by
    simp only [hU, val_iff_norm]
    exact ((isClosed_eq (hc _) continuous_const).inter (isClosed_eq (hc _) continuous_const)).measurableSet
  rw [← integral_mul_left_eq_self _ (uI h 1 (ϖ ^ (c + 1))⁻¹)]
  have hn : GlobalTheory.SplitWeil.nabs _ (ϖ ^ (c + 1))⁻¹ = (GlobalTheory.SplitWeil.resCard (Fv F v) : ℝ) ^ (c + 1) := by
    rw [← norm_nabs, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, norm_inv, norm_pow,
      norm_nabs, GlobalTheory.GLDoubling.nabs_unif hϖ, inv_pow, inv_inv]
  rw [integral_congr_ae (g := U.indicator fun _ => gI m ψ (chrW χ t) (((ϖ : Fv F v) ^ (c + 1))⁻¹) * (chrW χ t ϖ : ℂ) ^ (c + 1) *
        ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (c + 1)) ^ z * C) (Filter.Eventually.of_forall fun l => ?_), integral_indicator mU]
  · simp [Measure.real, h1]
  beta_reduce
  rw [chr_id (t := t) hσ, abs_id (t := t) hσ, ← cmp_val, ← cmp_val, map_mul, map_mul, (cmp_uI h _ _).1, (cmp_uI h _ _).2, one_mul, hχ]
  by_cases hl : l ∈ U
  · rw [Set.indicator_of_mem hl, dl_unit _ hl.1, mul_comm (ϖ ^ (c + 1))⁻¹, Units.val_mul, gI_unit hm _ hl.2, GlobalTheory.SplitWeil.nabs_mul,
      nabs_of_valuation_eq_one hl.1, nabs_of_valuation_eq_one hl.2, hn]
    simp only [map_mul, map_inv, map_pow, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      one_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
    field_simp
  · rw [Set.indicator_of_notMem hl]
    by_cases h2 : valuation _ (cmp t l : Fv F v) = 1
    · rw [gI_zero hm hψ hϖ hν hν' fun h3 => hl ⟨h2, ?_⟩]
      · simp
      · rwa [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, mul_right_comm,
          inv_mul_cancel₀ (pow_ne_zero _ ϖ.ne_zero), one_mul] at h3
    · simp [dl_of_ne h2]

end PositivityTheory.ThKG.Std
end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}
  {b : GL (Fin n) (Fv F v)} {c : GL (Fin d) (Fv F v)} {b₁ : GL (Fin n₁) (Fv F v)} {c₁ : GL (Fin d₁) (Fv F v)}
  [SecondCountableTopology (Fv F v)] [MeasurableSpace (Fv F v)] [BorelSpace (Fv F v)] {m : Measure (Fv F v)}

theorem ext_neg {k : Type} [Field k] (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (y : Matrix (Fin n₁) (Fin d₁) k) :
    -(emb k jr * y * (emb k jc)ᵀ) = emb k jr * (-y) * (emb k jc)ᵀ := by simp

theorem lin_uniq {M : Model σ X W} (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (g : M.IsGood B.ψ) {c₁ c₂ ι ι'}
    (L : Lin M B.ψ v c₁ c₂ ι) (L' : Lin M B.ψ v c₁ c₂ ι') {φ : Fl F v n d} (hφ : φ ∈ SB _) : ι' φ = ι φ := by
  haveI := hm.haar
  obtain ⟨f, hf⟩ := exists_sinf F (Fin n × Fin d)
  have hl : IsEvLoc M M LinearMap.id (ContinuousLinearMap.id _ _) fun _ => LinearMap.id :=
    ⟨fun e => by
      have : f = 0 := DFunLike.congr_fun e f
      simp [this] at hf, fun _ => ⟨rfl, Submodule.map_id _⟩, fun _ _ _ _ => rfl⟩
  have o : ∀ k, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := fun k => Matrix.map_one _ (map_zero _) (map_one _)
  have he : IsEv B M M 1 1 ∅ LinearMap.id := ⟨fun _ h => h, fun z Φ _ => by simp [o], fun _ h => h.elim, _, _, hl.ne, hl.vac, hl.pure⟩
  have x : ∀ y : Matrix (Fin n) (Fin d) (Fv F v), ext id id y = y := fun y =>
    Matrix.ext fun i j => ext_mid Function.injective_id Function.injective_id y i j
  funext y
  refine (ev_model hm hB.std hu g g he hl L L' id id ∅ (fun z => by simp [o, x]) (fun _ h => by simp at h)
    (fun p _ => Or.inl ⟨p.1, p.2, rfl⟩) hφ y).trans ?_
  have : ∀ Z : Fin n × Fin d → Fv F v, tm (cut ∅ Z) = 0 := fun Z => by ext i j; simp [tm, cut]
  simp only [this, zero_add, x, wt, Finset.notMem_empty, if_false]
  rw [integral_const_mul, integral_fintype_prod_eq_prod (fun _ : Fin n × Fin d => ind (1 : Fv F v))]
  simp [int_ind_one hm]

section
variable {X₀ : Spc F E n} {b₀ : GL (Fin n) (Fv F v)} {M : Model σ X W} {M₁ : Model σ X₀ W₁} {H' : Plane E d d₁} {jc : Fin d₁ → Fin d}
  {j₀ j₁ : Fin d}

theorem ev0W (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁} (L : Lin M B.ψ v (cW t b c) (cB σ t X W b c) ι)
    (L₁ : Lin M₁ B.ψ v (cW t b₀ c₁) (cB σ t X₀ W₁ b₀ c₁) ι₁) (hJ : IsUnit (X.J.map t)) (pe : PE σ t X.J X₀.J b b₀ 1 id)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) : ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut (Finset.univ.filter fun p => p.2 = j₀) Z) + ext id jc y) *
      wt (Finset.univ.filter fun p => p.2 = j₀) Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ i s s', ∃ u ∈ iso0 (F := F) n H', At (evFin F v) u ∧ cW t b c u = single i j₀ s ∧ cB σ t X W b c u = single i j₁ s' :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex (b := b) h hJ (Pi.single i s) (Pi.single i s'); ⟨_, ⟨p, rfl⟩, at_l a _, col_el h px' x y⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ id jc _ (emb_c h pe pe') (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · simpa [(Finset.mem_filter.1 hp).2] using el p.1 s 0
  · rcases hc p.2 with a | a | ⟨j, a⟩
    · exact absurd (by simp [a]) hp
    · exact Or.inr fun s => by simpa [a] using el p.1 0 s
    · exact Or.inl ⟨p.1, j, Prod.ext rfl a⟩

theorem ev0B (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ 1 H'.ι (iso0 n H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁}
    (L : Lin M B.ψ v (cB σ t X W b c) (fun u => -cW t b c u) ι)
    (L₁ : Lin M₁ B.ψ v (cB σ t X₀ W₁ b₀ c₁) (fun u => -cW t b₀ c₁ u) ι₁) (hJ : IsUnit (X.J.map t)) (pe : PE σ t X.J X₀.J b b₀ 1 id)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) : ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut (Finset.univ.filter fun p => p.2 = j₁) Z) + ext id jc y) *
      wt (Finset.univ.filter fun p => p.2 = j₁) Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ i s s', ∃ u ∈ iso0 (F := F) n H', At (evFin F v) u ∧ cB σ t X W b c u = single i j₁ s' ∧ -cW t b c u = single i j₀ s :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex (b := b) h hJ (Pi.single i (-s)) (Pi.single i s')
      ⟨_, ⟨p, rfl⟩, at_l a _, (col_el h px' x y).2, by rw [(col_el h px' x y).1, sneg, neg_neg]⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ id jc _ (fun z => ⟨(emb_c h pe pe' z).2, by
    rw [(emb_c h pe pe' z).1]; exact ext_neg _ _ _⟩) (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · simpa [(Finset.mem_filter.1 hp).2] using el p.1 0 s
  · rcases hc p.2 with a | a | ⟨j, a⟩
    · exact Or.inr fun s => by simpa [a] using el p.1 s 0
    · exact absurd (by simp [a]) hp
    · exact Or.inl ⟨p.1, j, Prod.ext rfl a⟩

end

section
variable {M : Model σ X W} {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
  {i₀ i₁ : Fin n} {j₀ j₁ : Fin d}

theorem evA (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ H.ι H'.ι (isoA H H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁} (L : Lin M B.ψ v (cW t b c) (cB σ t X W b c) ι)
    (L₁ : Lin M₁ B.ψ v (cW t b₁ c₁) (cB σ t X₁ W₁ b₁ c₁) ι₁) (hJ : IsUnit (X.J.map t)) (hJ' : IsUnit (W₁.J.map t))
    (pe : PE σ t X.J X₁.J b b₁ H.ι jr) (px : PX σ t X.J b H.x H.y i₀ i₁ 1) (hr : ∀ i, i = i₀ ∨ i = i₁ ∨ ∃ j, i = jr j)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    (P : Finset (Fin n × Fin d)) (hP : ∀ p, p ∈ P ↔ p.2 = j₀ ∨ p.1 = i₀ ∧ p.2 ≠ j₁)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) :
    ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut P Z) + ext jr jc y) * wt P Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ i s s', ∃ u ∈ isoA (F := F) H H', At (evFin F v) u ∧ cW t b c u = single i j₀ s ∧ cB σ t X W b c u = single i j₁ s' :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex (b := b) h hJ (Pi.single i s) (Pi.single i s')
      ⟨_, Or.inl ⟨p, rfl⟩, at_l a _, col_el h px' x y⟩
  have el' : ∀ j s s', ∃ u ∈ isoA (F := F) H H', At (evFin F v) u ∧ cW t b c u = single i₀ (jc j) s ∧
      cB σ t X W b c u = single i₁ (jc j) s' :=
    fun j s s' => let ⟨p, a, x, y⟩ := vec_ex' h pe' hJ' j s (-s')
      ⟨_, Or.inr ⟨p, rfl⟩, at_r _ a, (row_el h px x y).1, by rw [(row_el h px x y).2, neg_neg]⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ jr jc _ (emb_c h pe pe') (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · rcases hc p.2 with a | a | ⟨j, a⟩
    · simpa [a] using el p.1 s 0
    · rcases (hP p).1 hp with x | x
      · simpa [x] using el p.1 s 0
      · exact absurd a x.2
    · rcases (hP p).1 hp with x | x
      · simpa [x] using el p.1 s 0
      · simpa [x.1, a] using el' j s 0
  · by_cases a1 : p.2 = j₁
    · exact Or.inr fun s => by simpa [a1] using el p.1 0 s
    rcases hc p.2 with a | a | ⟨j, a⟩
    · exact absurd ((hP p).2 (Or.inl a)) hp
    · exact absurd a a1
    · rcases hr p.1 with x | x | ⟨i, x⟩
      · exact absurd ((hP p).2 (Or.inr ⟨x, a1⟩)) hp
      · exact Or.inr fun s => by simpa [a, x] using el' j 0 s
      · exact Or.inl ⟨i, j, Prod.ext x a⟩

theorem evB (hm : IsVol m) (hB : B.IsGood σ) (hu : PsiUnr B.ψ v) (h : IsSec σ t sec) (g : M.IsGood B.ψ) (g₁ : M₁.IsGood B.ψ) {e ei ev}
    (he : IsEv B M M₁ H.ι H'.ι (isoB H H') e) (hl : IsEvLoc M M₁ e ei ev) {ι ι₁}
    (L : Lin M B.ψ v (cB σ t X W b c) (fun u => -cW t b c u) ι)
    (L₁ : Lin M₁ B.ψ v (cB σ t X₁ W₁ b₁ c₁) (fun u => -cW t b₁ c₁ u) ι₁) (hJ : IsUnit (X₁.J.map t)) (hJ' : IsUnit (W.J.map t))
    (pe : PE σ t X.J X₁.J b b₁ H.ι jr) (px : PX σ t X.J b H.x H.y i₀ i₁ 1) (hr : ∀ i, i = i₀ ∨ i = i₁ ∨ ∃ j, i = jr j)
    (pe' : PE σ t W.J W₁.J c c₁ H'.ι jc) (px' : PX σ t W.J c H'.x H'.y j₀ j₁ (-1)) (hc : ∀ i, i = j₀ ∨ i = j₁ ∨ ∃ j, i = jc j)
    (P : Finset (Fin n × Fin d)) (hP : ∀ p, p ∈ P ↔ p.1 = i₁ ∨ p.2 = j₁ ∧ p.1 ≠ i₀)
    {φ : Fl F v n d} (hφ : φ ∈ SB _) (y) :
    ι₁ (ev v φ) y = ∫ Z, ι φ (tm (cut P Z) + ext jr jc y) * wt P Z ∂(Measure.pi fun _ => m) := by
  have el : ∀ j s s', ∃ u ∈ isoB (F := F) H H', At (evFin F v) u ∧ cB σ t X W b c u = single i₁ j s' ∧ -cW t b c u = single i₀ j s :=
    fun j s s' => let ⟨p, a, x, y⟩ := vec_ex (b := c) h hJ' (Pi.single j (-s)) (Pi.single j (-s'))
      ⟨_, Or.inl ⟨p, rfl⟩, at_r _ a, by rw [(row_el h px x y).2, neg_neg], by rw [(row_el h px x y).1, sneg, neg_neg]⟩
  have el' : ∀ i s s', ∃ u ∈ isoB (F := F) H H', At (evFin F v) u ∧ cB σ t X W b c u = single (jr i) j₁ s' ∧
      -cW t b c u = single (jr i) j₀ s :=
    fun i s s' => let ⟨p, a, x, y⟩ := vec_ex' h pe hJ i (-s) s'
      ⟨_, Or.inr ⟨p, rfl⟩, at_l a _, (col_el h px' x y).2, by rw [(col_el h px' x y).1, sneg, neg_neg]⟩
  refine ev_model hm hB.std hu g g₁ he hl L L₁ jr jc _ (fun z => ⟨(emb_c h pe pe' z).2, by
    rw [(emb_c h pe pe' z).1]; exact ext_neg _ _ _⟩) (fun p hp s => ?_) (fun p hp => ?_) hφ y
  · rcases (hP p).1 hp with x | x
    · simpa [x] using el p.2 0 s
    · rcases hr p.1 with a | a | ⟨i, a⟩
      · exact absurd a x.2
      · simpa [a] using el p.2 0 s
      · simpa [x.1, a] using el' i 0 s
  · by_cases a1 : p.1 = i₀
    · exact Or.inr fun s => by simpa [a1] using el p.2 s 0
    rcases hr p.1 with a | a | ⟨i, a⟩
    · exact absurd a a1
    · exact absurd ((hP p).2 (Or.inl a)) hp
    · rcases hc p.2 with x | x | ⟨j, x⟩
      · exact Or.inr fun s => by simpa [a, x] using el' i s 0
      · exact absurd ((hP p).2 (Or.inr ⟨x, a1⟩)) hp
      · exact Or.inl ⟨i, j, Prod.ext a x⟩

end

theorem cone_val {β : ℕ} {X : Spc F E (β + 2)} {X₁ : Spc F E β} {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hm : IsVol m) (hB : B.IsGood σ)
    (hu : PsiUnr B.ψ v) {c₁ c₂ ι c₁' c₂' ι₁} (L : Lin M B.ψ v c₁ c₂ ι) (L₁ : Lin M₁ B.ψ v c₁' c₂' ι₁)
    {ev : Fl F v (β + 2) d →ₗ[ℂ] Fl F v β d₁} (em : (SB _).map ev = SB _) {jc : Fin d₁ → Fin d} {P : Finset (Fin (β + 2) × Fin d)}
    (hev : ∀ φ ∈ SB _, ∀ y, ι₁ (ev φ) y = ∫ Z, ι φ (tm (cut P Z) + ext mid jc y) * wt P Z ∂(Measure.pi fun _ => m))
    {ϖ : (Fv F v)ˣ} (hϖ : IsUnif ϖ) (χ : Chr F E) (hχ : ∀ x, chrW χ (t.comp σ) x = (chrW χ t x)⁻¹) {κ : ℕ}
    (hν : CondLE ϖ (κ + 1) (chrW χ t)) (hν' : ¬ CondLE ϖ κ (chrW χ t)) {e : Fin (β + 2) → Fin d} {e₁ : Fin β → Fin d₁}
    {φ φ₁} (hφ : φ ∈ SB _) (hφ₁ : φ₁ ∈ SB _) (a : ι φ = std (chrW χ t) ϖ (κ + 1) e) (a₁ : ι₁ φ₁ = std (chrW χ t) ϖ (κ + 1) e₁)
    {om : Rep σ X W} {K : Subgroup (UA σ X.J)} {μ : LocMeas K} (hμ : μ.Is)
    (hK : ∀ k ∈ kAt K (evFin F v), Acts (evFin F v) (om (k, 1)) φ φ) {u : (AE F E)ˣ → Matrix (Fin (β + 2)) (Fin d) (AE F E)}
    (hs : ∀ l, c₁ (idem F v • u l) = single 0 (e (Fin.last _)) (piW t l) ∧
      c₂ (idem F v • u l) = single (Fin.last _) (e 0) (-piW (t.comp σ) l))
    (hc : Function.Injective jc) (hei : Function.Injective e) (he : ∀ i, jc (e₁ i) = e (mid i))
    (h0 : ∀ j, e 0 ≠ jc j) (h1 : ∀ j, e (Fin.last _) ≠ jc j) (hP : ∀ i j, (mid i, jc j) ∉ P)
    (ha : (Fin.last _, e 0) ∈ P) (hb : (0, e (Fin.last _)) ∉ P)
    (hAB : ((∀ j, j ≠ Fin.last _ → (0, e j) ∉ P) ∧ ∀ i, (mid i, e 0) ∉ P) ∨
      ((∀ i, i ≠ 0 → (i, e (Fin.last _)) ∉ P) ∧ ∀ j, (Fin.last _, e (mid j)) ∉ P)) {r : ℕ}
    (g : Fin r → Fin (β + 2) × Fin d) (hg : Function.Injective g) (h : ∀ p, p ∈ Set.range g ↔ p ∈ P ∧ p.2 ∉ Set.range e) (z : ℕ) :
    coneF B M om μ v ev u χ z φ = (gI m (psiV B.ψ v) (chrW χ t) (((ϖ : Fv F v) ^ (κ + 1))⁻¹) * (chrW χ t ϖ : ℂ) ^ (κ + 1) *
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1)) ^ z * (((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1))⁻¹) ^ r) • φ₁ := by
  have dms : ∀ (Y : Matrix (Fin (β + 2)) (Fin d) (Fv F v)) i j s, dm Y (single i j s) = Y i j * s := fun Y i j s => by
    simp [dm, dotProduct, ofM, single_apply, Fintype.sum_prod_type, ite_and]
  have l0 : (0 : Fin (β + 2)) ≠ Fin.last _ := by simp [Fin.ext_iff]
  have key : ∀ k ∈ kAt K (evFin F v), ∀ l, ev (opF v (fun Φ => M.co.rho B.ψ (idem F v • u l) (om (k, 1) Φ)) φ) =
      ((((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1))⁻¹) ^ r *
        (dl (chrW χ t) (piW t l) * gI m (psiV B.ψ v) (chrW χ t) (piW (t.comp σ) l))) • φ₁ := fun k hk l => by
    have at' : At (evFin F v) (idem F v • u l) := at_sgl_smul 1 _
    have sb := Hv_mem (M := M) hB.std (idem F v • u l) hφ
    rw [opF_eq hφ sb fun r hr => by
      show M.co.rho B.ψ _ (om (k, 1) _) = _
      rw [hK k hk r hr]; exact acts_Hv at' φ r hr]
    refine L₁.bij.2.1 (em ▸ Submodule.mem_map_of_mem sb) ((SB _).smul_mem _ hφ₁) (funext fun y => ?_)
    rw [hev _ sb, L.act _ at' (by rw [(hs l).1, (hs l).2, dms, single_apply_of_ne _ _ _ _ _ fun h => l0 h.1, zero_mul]) φ hφ,
      (hs l).1, (hs l).2, a, map_smul, a₁, Pi.smul_apply, smul_eq_mul,
      ← int_cone hm hϖ hc hei he h0 h1 P hP ha hb hAB g hg h]
    congr 1
    funext Z
    beta_reduce
    rw [dms, add_assoc, Matrix.add_apply, ext_off y (Or.inr h0), add_zero, mul_neg, mul_comm (tm _ _ _)]
    simp [tm, cut, ha]
  funext y
  have i1 := idele_int (t := t) hB.cm hm (isPsi hB.std hu) hϖ χ hχ hν hν' (μ.xf v) (hμ.xf v).1 (hμ.xf v).2
    ((((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1))⁻¹) ^ r * φ₁ y) z
  rw [coneF, integral_congr_ae (Filter.Eventually.of_forall fun k => (congrArg _ (funext fun l => by
    rw [key k.1 k.2, Pi.smul_apply, smul_eq_mul]; ring)).trans i1), integral_const, Measure.real, (hμ.kf v).2]
  simp [mul_assoc]

end PositivityTheory.ThKG.Std
end
end

section
set_option linter.unusedSectionVars false

noncomputable section

open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil PositivityTheory.ThK.SplitLoc

namespace PositivityTheory.ThKG.Std

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d a a' : ℕ} {ν α β : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}

def InR (ϖ : kˣ) (c : ℕ) (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) : Prop :=
  ∀ i j, valuation k (Y i j) ≤ valuation k (rad ϖ c e j)

open Classical in
theorem prod_ind (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) :
    ∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) (Y p.1 p.2) = if InR ϖ c e Y then 1 else 0 := by
  simp only [ind, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, true_imp_iff, InR, Prod.forall]
  congr

theorem InR.mul {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (h : InR ϖ c e Y) {g : Matrix (Fin n) (Fin n) k}
    (hg : ∀ i j, g i j ∈ 𝒪[k]) : InR ϖ c e (g * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact (valuation k).map_sum_le fun l _ => by rw [map_mul]; exact (mul_le_of_le_one_left' (hg i l)).trans (h l j)

open Classical in
theorem std_mul {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) (g : GL (Fin n) k) (z : ℂ) :
    std ν ϖ c e (g.1 * Y) * (ν (gdet g) : ℂ) * apow (gdet g) z =
      (KO k (Fin n) : Set _).indicator (fun _ => if InR ϖ c e Y then 1 else 0) g := by
  have hb : (g.1 * Y).submatrix id e = g.1 := by
    rw [show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, hY, Matrix.mul_one]
  rw [std, hb, prod_ind]
  by_cases hg : g ∈ KO k (Fin n)
  · have hv := valuation_gdet_of_mem_KO hg
    rw [Set.indicator_of_mem hg, show g.1.det = (gdet g : k) from rfl, dl_unit _ hv, apow_of_valuation_eq_one hv]
    rw [mem_KO_iff] at hg
    have : InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y := ⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩
    simp [this]
  · rw [Set.indicator_of_notMem hg]
    by_cases h1 : InR ϖ c e (g.1 * Y)
    · have h2 : ∀ i j, valuation k (g.1 i j) ≤ 1 := fun i j => by
        have := h1 i (e j)
        rwa [rad_e, map_one, show (g.1 * Y) i (e j) = g.1 i j from congrFun (congrFun hb i) j] at this
      rw [dl_of_ne, mul_zero, zero_mul, zero_mul]
      intro hd
      refine hg ((mem_KO_iff _).2 ⟨h2, fun i j => ?_⟩)
      show valuation k _ ≤ 1
      rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hd,
        inv_one, one_mul, adjugate_apply]
      refine val_det fun p q => ?_
      rw [updateRow_apply]
      split_ifs
      · rw [Pi.single_apply]; split_ifs <;> simp
      · exact h2 p q
    · simp [h1]

theorem std_sing {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) (g : Matrix (Fin n) (Fin n) k) :
    std ν ϖ c e (g * Y) = 0 := by
  rw [std, show (g * Y).submatrix id e = g * Y.submatrix id e from rfl, det_mul, hY, mul_zero, dl_of_ne (by simp), mul_zero]

variable [MeasurableSpace k] [BorelSpace k]

theorem int_KO (A : ℂ) : ∫ g, (KO k (Fin n) : Set _).indicator (fun _ => A) g ∂haarVol (KO k (Fin n)) = A := by
  rw [integral_indicator isOpen_KO.measurableSet]
  simp [Measure.real, haarVol_self isOpen_KO le_rfl]

theorem bigF_sing (μ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) :
    bigF μ ϖ ν (std ν ϖ c e) Y = 0 := by simp [bigF, shellSum, shell, std_sing hY]

theorem smallF_sing (μ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : (Y.submatrix id e).det = 0) :
    smallF μ ν (std ν ϖ c e) Y = 0 := by simp [smallF, std_sing hY]

open Classical in
theorem smallF_std {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) :
    smallF (haarVol (KO k (Fin n))) ν (std ν ϖ c e) Y = if InR ϖ c e Y then 1 else 0 := by
  simp only [smallF, std_mul hY, int_KO]

open Classical in
theorem bigF_std (hϖ : IsUnif ϖ) {e : Fin n → Fin d} {Y : Matrix (Fin n) (Fin d) k} (hY : Y.submatrix id e = 1) :
    bigF (haarVol (KO k (Fin n))) ϖ ν (std ν ϖ c e) Y = if InR ϖ c e Y then 1 else 0 := by
  rw [bigF, shellSum, finsum_eq_single _ ⟨0, antitone_const⟩]
  · simp only [shell, std_mul hY, shellSet_zero]
    rw [setIntegral_indicator isOpen_KO.measurableSet, Set.inter_self, ← integral_indicator isOpen_KO.measurableSet, int_KO]
  · intro m hm
    simp only [shell, std_mul hY]
    refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => Set.indicator_of_notMem (fun hK => hm (Subtype.ext (funext fun i => ?_))) _
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
    have h1 := (mem_KO_iff _).1 ((Subgroup.mul_mem_cancel_left _ hx).1 ((Subgroup.mul_mem_cancel_right _ hy).1 hK))
    have h2 : valuation k ((ϖ : k) ^ m.1 i) ≤ 1 := by simpa [diagGL_val] using (show valuation k _ ≤ 1 from h1.1 i i)
    have h3 : valuation k ((ϖ : k) ^ (-m.1 i)) ≤ 1 := by
      have := (show valuation k _ ≤ 1 from h1.2 i i)
      rw [show (diagGL fun i => ϖ ^ m.1 i)⁻¹ = diagGL fun i => ϖ ^ (-m.1 i) from inv_eq_of_mul_eq_one_right (Units.ext (by
        simp [diagGL_val, funext_iff, zpow_ne_zero]))] at this
      simpa [diagGL_val] using this
    rw [map_zpow₀, hϖ, zpow_le_one_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one] at h2 h3
    show m.1 i = 0
    omega

def eA (a a' : ℕ) (i : Fin a) : Fin (a + a') := finSumFinEquiv (Sum.inl i)

def eB (a a' : ℕ) (i : Fin a') : Fin (a + a') := finSumFinEquiv (Sum.inr i)

def low (y : Matrix (Fin a') (Fin a) k) : GL (Fin (a + a')) k :=
  ⟨(fromBlocks 1 0 y 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    (fromBlocks 1 0 (-y) 1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm,
    by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp, by rw [submatrix_mul_equiv, fromBlocks_multiply]; simp⟩

theorem gdet_low (y : Matrix (Fin a') (Fin a) k) : gdet (low y) = 1 := Units.ext (by
  show det (Matrix.submatrix _ _ _) = 1
  rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; simp)

theorem rad_AB (j : Fin a') : rad ϖ c (eA a a') (finSumFinEquiv (Sum.inr j)) = (ϖ : k) ^ c :=
  if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h

theorem rad_BA (j : Fin a) : rad ϖ c (eB a a') (finSumFinEquiv (Sum.inl j)) = (ϖ : k) ^ c :=
  if_neg fun ⟨_, h⟩ => by simpa using finSumFinEquiv.injective h

theorem low_X (y : Matrix (Fin a') (Fin a) k) : ∀ i (j : Fin a ⊕ Fin a'), (X0 k finSumFinEquiv * (invT (low y)).1 : Matrix (Fin a) (Fin (a + a')) k) i (finSumFinEquiv j) =
    fromBlocks (1 : Matrix (Fin a) (Fin a) k) 0 (-y) (1 : Matrix (Fin a') (Fin a') k) j (Sum.inl i) := fun i j => by
    refine (frameMatrixFirstColumnBlock_mul_apply finSumFinEquiv (invT (low y)).1 i _).trans ?_
    simp [invT_val, low]

theorem low_Y (y : Matrix (Fin a') (Fin a) k) : ∀ i (j : Fin a ⊕ Fin a'), (Y0 k finSumFinEquiv * (low y).1 : Matrix (Fin a') (Fin (a + a')) k) i (finSumFinEquiv j) =
    fromBlocks (1 : Matrix (Fin a) (Fin a) k) 0 y 1 (Sum.inr i) j := fun i j => by
    refine (frameMatrixSecondColumnBlock_mul_apply finSumFinEquiv (low y).1 i _).trans ?_
    simp [low]

open Classical in
theorem pRam_low (hϖ : IsUnif ϖ) (y : Matrix (Fin a') (Fin a) k) : pRam a a' ϖ ν β (std ν ϖ c (eA a a')) (low y) =
    if ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c) then 1 else 0 := by
  have e := low_X (k := k) y
  rw [pRam, bigZetaIntegral_eq, gdet_low, bigF_std hϖ (by
    ext i j; rw [submatrix_apply, eA, id]; erw [e]; simp [one_apply, eq_comm])]
  simp only [map_one, Units.val_one, apow_one, one_mul]
  refine if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl
  · have := h j (finSumFinEquiv (Sum.inr i))
    erw [e, rad_AB] at this
    simpa using this
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · erw [e, show finSumFinEquiv (Sum.inl j) = eA a a' j from rfl, rad_e]
      simp only [fromBlocks_apply₁₁, one_apply]; split_ifs <;> simp
    · erw [e, rad_AB]; simpa using h j i

open Classical in
theorem pRam'_low (y : Matrix (Fin a') (Fin a) k) : pRam' a a' ν α (std ν ϖ c (eB a a')) (low y) =
    if ∀ i j, valuation k (y i j) ≤ valuation k ((ϖ : k) ^ c) then 1 else 0 := by
  have e := low_Y (k := k) y
  have hY : (Y0 k finSumFinEquiv * (low y).1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a') = 1 := by
    ext i j; rw [submatrix_apply, eB, id, e]; simp
  rw [pRam', smallP, gdet_low]
  erw [smallF_std hY]
  simp only [map_one, Units.val_one, apow_one, one_mul]
  refine if_congr ⟨fun h i j => ?_, fun h i j => ?_⟩ rfl rfl
  · have := h i (finSumFinEquiv (Sum.inl j))
    erw [e, rad_BA] at this
    simpa using this
  · obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j
    · erw [e, rad_BA]; simpa using h i j
    · erw [e, show finSumFinEquiv (Sum.inr j) = eB a a' j from rfl, rad_e]
      simp only [fromBlocks_apply₂₂, one_apply]; split_ifs <;> simp

theorem pRam_ne (hϖ : IsUnif ϖ) : pRam a a' ϖ ν β (std ν ϖ c (eA a a')) ≠ 0 := fun h => by
  have := congrFun h (low 0)
  rw [pRam_low hϖ] at this
  simp at this

theorem std_pair (H : HidaSetting a a' ϖ α β ν) (hr : ¬ IsUnram ν) (hc : 1 ≤ c) (hν : CondLE ϖ c ν) :
    pRam a a' ϖ ν β (std ν ϖ c (eA a a')) = pRam' a a' ν α (std ν ϖ c (eB a a')) := by
  funext h
  let s : Fin a ⊕ Fin a' ≃ Fin (a + a') := finSumFinEquiv
  set N := h.1.submatrix s s with hN
  set N' := (h⁻¹).1.submatrix s s with hN'
  have hNN : N * N' = 1 := by rw [hN, hN', submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv]
  by_cases hD : N.toBlocks₂₂.det = 0
  · have h1 : N'.toBlocks₁₁.det = 0 := by
      by_contra h1
      rw [← fromBlocks_toBlocks N, ← fromBlocks_toBlocks N', fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hNN
      obtain ⟨-, -, e1, e2⟩ := hNN
      have e3 : N.toBlocks₂₁ = -(N.toBlocks₂₂ * N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹) := by
        rw [← Matrix.neg_mul, ← eq_neg_of_add_eq_zero_left e1, Matrix.mul_nonsing_inv_cancel_right _ _ (Ne.isUnit h1)]
      have e4 : N.toBlocks₂₂ * (N'.toBlocks₂₂ - N'.toBlocks₂₁ * N'.toBlocks₁₁⁻¹ * N'.toBlocks₁₂) = 1 := by
        rw [← e2, e3]; simp only [Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc]; abel
      have := congrArg det e4
      rw [det_mul, hD, zero_mul, det_one] at this
      exact zero_ne_one this
    have a1 : ((X0 k finSumFinEquiv * (invT h).1 : Matrix (Fin a) (Fin (a + a')) k).submatrix id (eA a a')).det = 0 := by
      rw [← det_transpose, ← h1]; congr 1; ext i j
      exact frameMatrixFirstColumnBlock_mul_apply s (invT h).1 j _
    have a2 : ((Y0 k finSumFinEquiv * h.1 : Matrix (Fin a') (Fin (a + a')) k).submatrix id (eB a a')).det = 0 := by
      rw [← hD]; congr 1; ext i j
      exact frameMatrixSecondColumnBlock_mul_apply s h.1 i _
    rw [pRam, bigZetaIntegral_eq, pRam', smallP]
    erw [bigF_sing _ a1, smallF_sing _ a2]
    simp
  · set y := N.toBlocks₂₂⁻¹ * N.toBlocks₂₁ with hy
    set b := h * (low y)⁻¹ with hb
    have eb : b.1.submatrix s s = N * fromBlocks 1 0 (-y) 1 := by
      rw [hb, Units.val_mul, ← submatrix_mul_equiv _ _ _ s]
      congr 1
      ext i j; simp [low, s]
    have e21 : (b.1.submatrix s s).toBlocks₂₁ = 0 := by
      rw [eb, ← fromBlocks_toBlocks N, fromBlocks_multiply]
      simp [hy, Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hD)]
    have hu : IsBlockUpper b := fun i j => congrFun (congrFun e21 i) j
    have hdet : (blkA b).det * (blkD b).det ≠ 0 := by
      have : b.1.det = (blkA b).det * (blkD b).det := by
        rw [← det_submatrix_equiv_self s, ← fromBlocks_toBlocks (b.1.submatrix s s), e21, det_fromBlocks_zero₂₁]; rfl
      rw [← this]; exact b.det_ne_zero
    have hh : h = b * low y := by simp [hb]
    rw [hh, (pRam_mem H hr (std_mem H.unif hc hν _)).2 b _ hu (Units.mk0 _ (left_ne_zero_of_mul hdet))
      (Units.mk0 _ (right_ne_zero_of_mul hdet)) rfl rfl, (pRam'_mem H (std_mem H.unif hc hν _)).2 b _ hu
      (Units.mk0 _ (left_ne_zero_of_mul hdet)) (Units.mk0 _ (right_ne_zero_of_mul hdet)) rfl rfl, pRam_low H.unif, pRam'_low]

omit [MeasurableSpace k] [BorelSpace k] in
theorem std_left {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (Y : Matrix (Fin n) (Fin d) k) :
    (ν (gdet g) : ℂ) * std ν ϖ c e (g.1 * Y) = std ν ϖ c e Y := by
  have hv := valuation_gdet_of_mem_KO hg
  rw [mem_KO_iff] at hg
  have : InR ϖ c e (g.1 * Y) ↔ InR ϖ c e Y := ⟨fun h => by simpa [← Matrix.mul_assoc] using h.mul hg.2, fun h => h.mul hg.1⟩
  rw [std, std, prod_ind, prod_ind, show (g.1 * Y).submatrix id e = g.1 * Y.submatrix id e from rfl, det_mul,
    show g.1.det = (gdet g : k) from rfl, dl_mul_unit hv, dl_unit _ hv]
  rw [propext this, mul_left_comm, ← mul_assoc (ν _ : ℂ), Units.mul_inv, one_mul]

omit [MeasurableSpace k] [BorelSpace k] in
theorem omA_std {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : omA ν β g 1 (std ν ϖ c e) = std ν ϖ c e := by
  funext Y
  rw [← std_left (inv_mem hg) Y]
  simp [omA, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]

omit [MeasurableSpace k] [BorelSpace k] in
theorem omB_std {e : Fin n → Fin d} {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) : omB ν α g 1 (std ν ϖ c e) = std ν ϖ c e := by
  funext Y
  rw [← std_left (inv_mem (invT_mem_KO hg)) Y, invT_inv_val, gdet, map_inv, ← gdet, gdet_invT, inv_inv]
  simp [omB, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg), gdet]

end PositivityTheory.ThKG.Std
end
end

section
noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

open PositivityTheory.ThK.SplitLoc

local instance measFv (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

local instance scFv (v : Pl F) : SecondCountableTopology (Fv F v) := (GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Fv F v)).1

theorem exists_vol (v : Pl F) : ∃ m : Measure (Fv F v), IsVol m :=
  ⟨Measure.addHaarMeasure ⟨⟨_, IsNonarchimedeanLocalField.isCompact_closedBall _ (valuation (Fv F v) 1)⟩, by
    rw [(isClopen_ball one_ne_zero).2.interior_eq]; exact ⟨0, by simp⟩⟩, inferInstance, Measure.addHaarMeasure_self⟩

def skF {n n₁ : ℕ} (h : n = n₁ + 2) (i₀ i₁ : ℕ) (j : Fin n₁) : Fin n := ⟨skip i₀ i₁ j, by
  have := j.2; unfold skip; split_ifs <;> omega⟩

theorem skF_inj {n n₁ : ℕ} (h : n = n₁ + 2) (i₀ i₁ : ℕ) : Function.Injective (skF h i₀ i₁) := fun a b e => Fin.ext (by
  have := congrArg Fin.val e
  simp only [skF, skip] at this
  split_ifs at this <;> omega)

theorem skF_cover {n n₁ : ℕ} (h : n = n₁ + 2) {j₀ j₁ : Fin n} (l : j₀.1 < j₁.1) (i : Fin n) :
    i = j₀ ∨ i = j₁ ∨ ∃ j, i = skF h j₀ j₁ j := by
  have := i.2
  have := j₁.2
  by_cases a : i.1 = j₀.1
  · exact Or.inl (Fin.ext a)
  by_cases b : i.1 = j₁.1
  · exact Or.inr (Or.inl (Fin.ext b))
  refine Or.inr (Or.inr ?_)
  by_cases c : i.1 < j₀.1
  · exact ⟨⟨i.1, by omega⟩, Fin.ext (by simp [skF, skip, c])⟩
  by_cases d : i.1 < j₁.1
  · exact ⟨⟨i.1 - 1, by omega⟩, Fin.ext (by simp only [skF, skip]; split_ifs <;> omega)⟩
  · exact ⟨⟨i.1 - 2, by omega⟩, Fin.ext (by simp only [skF, skip]; split_ifs <;> omega)⟩

theorem skF_ne {n n₁ : ℕ} (h : n = n₁ + 2) {j₀ j₁ : Fin n} (l : j₀.1 < j₁.1) (j : Fin n₁) :
    skF h j₀ j₁ j ≠ j₀ ∧ skF h j₀ j₁ j ≠ j₁ := by
  constructor <;> intro e <;> have := congrArg Fin.val e <;> simp only [skF, skip] at this <;> split_ifs at this <;> omega

theorem skF_mid (b : ℕ) : skF (rfl : b + 2 = b + 2) (0 : Fin (b + 2)).1 (Fin.last (b + 1)).1 = mid := funext fun j => Fin.ext (by
  have := j.2
  show skip 0 (b + 1) j = j + 1
  unfold skip; split_ifs <;> omega)

variable {B : Base F E}

theorem plane' (hσ : IsCMExt F E σ) {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ : Fin n}
    (h : H.IsAdapted σ B X X₁ j₀ j₁) {ε : E} (hJ : ∀ i j, σ (X.J j i) = ε * X.J i j) (hε : ε * ε = 1) (w : B.P) (l : j₀.1 < j₁.1) :
    PE σ (B.τ w) X.J X₁.J (X.bas w) (X₁.bas w) H.ι (skF h.rank j₀ j₁) ∧ PX σ (B.τ w) X.J (X.bas w) H.x H.y j₀ j₁ (B.τ w ε) :=
  plane hσ h hJ hε w rfl rfl (fun _ => rfl) (skF_inj _ _ _) (skF_cover _ l) (fun e => by rw [e] at l; omega)
    (fun j => (skF_ne _ l j).1) fun j => (skF_ne _ l j).2

theorem cond_ex {ν : (Fv F v)ˣ →* ℂˣ} (h : ∃ e, CondLE (unifAt v) e ν) (hr : ¬ GlobalTheory.SplitWeil.IsUnram ν) :
    ∃ κ, condExp ν = κ + 1 ∧ CondLE (unifAt v) (κ + 1) ν ∧ ¬ CondLE (unifAt v) κ ν := by
  have m : CondLE (unifAt v) (condExp ν) ν := Nat.sInf_mem h
  have h0 : condExp ν ≠ 0 := fun e => hr fun x hx => by
    rw [e] at m
    exact m x ⟨hx, by simpa using (valuation (Fv F v)).map_sub_le hx.le (map_one _).le⟩
  obtain ⟨κ, hκ⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact ⟨κ, hκ, by rw [hκ] at m; exact m, fun e => Nat.notMem_of_lt_sInf (s := {c | CondLE (unifAt v) c ν}) (by
    show κ < condExp ν
    omega) e⟩

theorem eps_eq {m : Measure (Fv F v)} (hm : IsVol m) {ψ : AddChar (AF F) ℂ} (hψ : IsPsi (psiV ψ v)) {ν : (Fv F v)ˣ →* ℂˣ} {κ : ℕ}
    (h : condExp ν = κ + 1) (hν : CondLE (unifAt v) (κ + 1) ν) (z : ℕ) :
    gI m (psiV ψ v) ν (((unifAt v : Fv F v) ^ (κ + 1))⁻¹) * (ν (unifAt v) : ℂ) ^ (κ + 1) *
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1)) ^ z = eps ψ ν (1 - z) := by
  have q := (GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F v).1
  have q0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have g : gI m (psiV ψ v) ν (((unifAt v : Fv F v) ^ condExp ν)⁻¹) =
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ condExp ν)⁻¹ * gauss ψ ν := by
    letI : Fintype (Res (Fv F v) (condExp ν))ˣ := Fintype.ofFinite _
    rw [gI_gauss (ϖ := unifAt v) hm hψ exists_isUnif.choose_spec (by omega) (h ▸ hν), gauss]
    congr
    exact Subsingleton.elim _ _
  rw [eps, ← h, g, q, show -(condExp ν : ℤ) * (1 - z) = (condExp ν * z : ℕ) - (condExp ν : ℕ) by push_cast; ring, zpow_sub₀ q0,
    zpow_natCast, zpow_natCast, pow_mul]
  ring

theorem data {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om' R Rf} (T : IsMatched B G X om om' R Rf) (w : B.P) (hw : w.1 ∈ X.T)
    {sec} (h : IsSec σ (B.τ w) sec) {κ : ℕ} (hν : CondLE (unifAt w.1) (κ + 1) (chrW X.ν (B.τ w))) :
    ∃ ι ι' φ φ', Lin G.M B.ψ w (cW (B.τ w) (G.V.bas w) (G.W.bas w)) (cB σ (B.τ w) G.V G.W (G.V.bas w) (G.W.bas w)) ι ∧
      Lin G.M' B.ψ w (cB σ (B.τ w) G.V' G.W (G.V'.bas w) (G.W.bas w)) (fun u => -cW (B.τ w) (G.V'.bas w) (G.W.bas w) u) ι' ∧
      φ ∈ SB _ ∧ φ' ∈ SB _ ∧ ι φ = std (chrW X.ν (B.τ w)) (unifAt w.1) (κ + 1) (eA a a') ∧
      ι' φ' = std (chrW X.ν (B.τ w)) (unifAt w.1) (κ + 1) (eB a a') ∧ Rf.p w φ = Rf.p' w φ' ∧ Rf.p w φ ≠ 0 ∧
      (∀ K, IsStab B K → ∀ k ∈ kAt K (evFin F w), Acts (evFin F w) (om (k, 1)) φ φ) ∧
      ∀ K, IsStab B K → ∀ k ∈ kAt K (evFin F w), Acts (evFin F w) (om' (k, 1)) φ' φ' := by
  have t := T.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  obtain ⟨hα, hβ, e, hcond, hram, -⟩ := PositivityTheory.ThK.SplitAsm.split_character_facts F E B X a a' w (B.τ w) t.chars
  have hS : HidaSetting a a' (unifAt w.1) (chrW X.α (B.τ w)) (chrW X.β (B.τ w)) (chrW X.ν (B.τ w)) :=
    ⟨exists_isUnif.choose_spec, hα, hβ, e, t.geo.lt, t.geo.even, hcond⟩
  obtain ⟨ι, ι', l, l', v1, v2, z⟩ := T.fin.zeta w hw
  have L := local_splitting_linear_skew hB.std h (grams h t.geo.hV t.geo.hW) l v1
  have L' := lin_Bar hB.std h (grams h t.geo.hV' t.geo.hW) l' v2
  obtain ⟨φ, s, a1⟩ := L.bij.2.2 (std_mem hS.unif (by omega) hν (eA a a'))
  obtain ⟨φ', s', a2⟩ := L'.bij.2.2 (std_mem hS.unif (by omega) hν (eB a a'))
  refine ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, (z φ s φ' s').2 ?_, fun h0 => ?_, fun K hK k hk => ?_, fun K hK k hk => ?_⟩
  · rw [a1, a2]; exact std_pair hS (hram hw) (by omega) hν
  · have := (z φ s 0 (zero_mem _)).1 (by rw [h0, map_zero])
    rw [a1, map_zero] at this
    refine pRam_ne (a' := a') (β := chrW X.β (B.τ w)) hS.unif (this.trans ?_)
    funext g; simp [smallP, smallF]
  · obtain ⟨j, l1, u1, g1, -⟩ := model_alt hB t.geo.hV t.geo.hW (t.geo.hM.vac w) t.weil (t.geo.hV.bas w) (t.geo.hW.bas w)
      (ν := chrW X.ν (B.τ w)) (β := chrW X.β (B.τ w)) (MonoidHom.ext fun x => by
        rw [chrW_div, chrW_conj hB.cm _ t.chars.resα, chrW_conj hB.cm _ t.chars.resβ, Chars.ν, chrW_div, inv_div_inv])
      (chrW_conj hB.cm _ t.chars.resβ)
    have J := local_splitting_linear_skew hB.std h (grams h t.geo.hV t.geo.hW) l1 u1
    obtain ⟨φ₁, b1, b2, b3⟩ := g1 k (uat_closure hk.2) φ s
    rw [lin_uniq hm hB hu t.geo.hM L J s, a1, omA_std (inB_mem h (t.geo.hV.bas w) hK hk.1), ← a1, lin_uniq hm hB hu t.geo.hM L J b1] at b3
    rwa [L.bij.2.1 b1 s b3] at b2
  · obtain ⟨j, l1, u1, g1, -⟩ := model_Bar hB t.geo.hV' t.geo.hW (t.geo.hM'.vac w) t.weil' (t.geo.hV'.bas w) (t.geo.hW.bas w)
      (δ := 1) (fun x => by rw [one_mul]; exact hu x) (one_smul _ _).symm
    have J := lin_Bar hB.std h (grams h t.geo.hV' t.geo.hW) l1 u1
    obtain ⟨φ₁, b1, b2, b3⟩ := g1 k (uat_closure hk.2) φ' s'
    rw [lin_uniq hm hB hu t.geo.hM' L' J s', a2] at b3
    erw [omB_std (inB_mem h (t.geo.hV'.bas w) hK hk.1)] at b3
    erw [← a2] at b3
    rw [lin_uniq hm hB hu t.geo.hM' L' J b1] at b3
    rwa [L'.bij.2.1 b1 s' b3] at b2

theorem nu_data {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} (t : IsTriple B G X om om') (w : B.P) (hw : w.1 ∈ X.T) :
    (∀ x, chrW X.ν ((B.τ w).comp σ) x = (chrW X.ν (B.τ w) x)⁻¹) ∧ ∃ κ, condExp (chrW X.ν (B.τ w)) = κ + 1 ∧
      CondLE (unifAt w.1) (κ + 1) (chrW X.ν (B.τ w)) ∧ ¬ CondLE (unifAt w.1) κ (chrW X.ν (B.τ w)) := by
  obtain ⟨-, -, e, ⟨c, h1, h2⟩, hram, -⟩ := PositivityTheory.ThK.SplitAsm.split_character_facts F E B X a a' w (B.τ w) t.chars
  refine ⟨fun x => ?_, cond_ex ⟨c, e ▸ h1.div h2⟩ (hram hw)⟩
  rw [Chars.ν, chrW_div, chrW_div, chrW_conj t.base.cm _ t.chars.resα, chrW_conj t.base.cm _ t.chars.resβ, inv_div_inv, inv_div]

theorem eA_val {a a' : ℕ} (i : Fin a) : (eA a a' i).1 = i := rfl

theorem eB_val {a a' : ℕ} (i : Fin a') : (eB a a' i).1 = a + i := rfl

theorem unit_J {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (h : IsSec σ t sec) {r s r' s'} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    IsUnit (X.J.map t) ∧ IsUnit (W.J.map t) := by
  have := grams h hX hW
  rw [← incM_map h, ← incM_map h]
  exact ⟨this.uA, this.uB⟩

theorem stdB : StdB := by
  refine ⟨1, fun F E _ _ _ _ _ σ B a b G G₁ H H' cf e ei ev e' ei' ev' he hl he' hl' K μ hK hμ X om om' R Rf om₁ om₁' R₁ Rf₁ T T₁ w hw => ?_⟩
  have t := T.triple
  have t₁ := T₁.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  have hϖ : IsUnif (unifAt w.1) := exists_isUnif.choose_spec
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm w (B.τ w)
  obtain ⟨hc, κ, k1, k2, k3⟩ := nu_data t w hw
  obtain ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, mt, -, -, fx⟩ := data T w hw h k2
  obtain ⟨ι₁, ι₁', φ₁, φ₁', L₁, L₁', s₁, s₁', b1, b2, mt₁, ne₁, -, -⟩ := data T₁ w hw h k2
  have lt : (eB a (b + 2) 0).1 < (eB a (b + 2) (Fin.last _)).1 := by simp [eB_val]
  obtain ⟨pe', px'⟩ := plane' hB.cm (j₀ := eB a (b + 2) 0) (j₁ := eB a (b + 2) (Fin.last _)) cf.hH' (ε := -1)
    (fun i j => by rw [t.geo.hW.skew, neg_one_mul]) (by simp) w lt
  obtain ⟨pe, px⟩ := plane' hB.cm (j₀ := 0) (j₁ := Fin.last _) cf.hH (ε := 1) (fun i j => by rw [t.geo.hV'.herm, one_mul]) (by simp) w
    (by simp)
  rw [map_neg, map_one] at px'
  rw [map_one] at px
  have cv := skF_cover (rfl : b + 2 = b + 2) (j₀ := 0) (j₁ := Fin.last _) (by simp)
  rw [skF_mid] at pe cv
  have cv' := skF_cover cf.hH'.rank lt
  have nz := skF_ne cf.hH'.rank lt
  set jc := skF cf.hH'.rank (eB a (b + 2) 0) (eB a (b + 2) (Fin.last _)) with hjc
  have e1 : ev w φ = ((((GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ^ (κ + 1))⁻¹) ^ a) • φ₁ := by
    refine L₁.bij.2.1 ((hl.vac w).2 ▸ Submodule.mem_map_of_mem s) ((SB _).smul_mem _ s₁) (funext fun y => ?_)
    rw [ev0W hm hB hu h t.geo.hM t₁.geo.hM he hl L L₁ (unit_J h t.geo.hV t.geo.hW).1 (by rw [cf.eV]; exact pe_one _ _) pe' px' cv' s,
      a1, map_smul, b1]
    exact int_ev hm hϖ (skF_inj _ _ _) (fun i => Fin.ext (by simp [hjc, skF, skip, eA_val, eB_val])) _
      (fun ⟨i, hi⟩ => by have := congrArg Fin.val hi; have := i.2; simp [eA_val, eB_val] at *; omega) (fun j => (nz j).1.symm) y
  let P : Finset (Fin (b + 2) × Fin (a + (b + 2))) :=
    Finset.univ.filter fun p => p.1 = Fin.last _ ∨ p.2 = eB a (b + 2) (Fin.last _) ∧ p.1 ≠ 0
  have hP : ∀ p, p ∈ P ↔ p.1 = Fin.last _ ∨ p.2 = eB a (b + 2) (Fin.last _) ∧ p.1 ≠ 0 := fun p => by simp [P]
  have ml : ∀ i : Fin b, mid i ≠ Fin.last (b + 1) := fun i h => by have := congrArg Fin.val h; simp [mid] at this; omega
  have ei2 : Function.Injective (eB a (b + 2)) := fun _ _ h => by simpa using finSumFinEquiv.injective h
  have e2 := cone_val hm hB hu L' L₁' (hl'.vac w).2 (fun φ s y => evB hm hB hu h t.geo.hM' t₁.geo.hM' he' hl' L' L₁'
      (unit_J h t₁.geo.hV' t₁.geo.hW).1 (unit_J h t.geo.hV' t.geo.hW).2 pe px cv pe' px' cv' P hP s y) hϖ X.ν hc k2 k3 s' s₁' a2 b2 hμ
    (fx K hK) (shiftB_c h px px') (skF_inj _ _ _) ei2
    (fun i => Fin.ext (by have := i.2; show skip (a + 0) (a + (b + 1)) (a + i) = a + (i + 1)
                          unfold skip; split_ifs <;> omega))
    (fun j => (nz j).1.symm) (fun j => (nz j).2.symm) (fun i j => by simp [hP, ml, (nz j).2]) (by simp [hP]) (by simp [hP])
    (Or.inl ⟨fun j _ => by simp [hP], fun i => by simp [hP, ml, ei2.eq_iff]⟩) (fun j => (Fin.last _, eA a (b + 2) j))
    (fun _ _ h => by simpa [eA] using h) (fun p => by
      rw [hP]
      refine ⟨?_, fun ⟨x, y⟩ => ?_⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Or.inl rfl, fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi⟩
      · obtain ⟨j | j, hj⟩ := finSumFinEquiv.surjective p.2
        · exact ⟨j, Prod.ext (x.resolve_right fun x => y ⟨_, x.1.symm⟩).symm hj⟩
        · exact absurd ⟨j, hj⟩ y) ((a - (b + 2)) / 2 + 1)
  have q0 : (GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ≠ 0 := by
    rw [(GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F w).1]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
  refine ⟨φ, s, φ', s', mt, ?_, ?_⟩
  · rw [e1, map_smul]; exact smul_ne_zero (by positivity) ne₁
  · rw [e2, e1, eps_eq hm (isPsi hB.std hu) k1 k2, map_smul, map_smul, mt₁, smul_smul]
    simp

theorem stdA_gen {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'} {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')}
    (eV : G₁.V' = G.V') (hH : H.IsAdapted σ B G.V G₁.V 0 (b + 1)) (hH' : H'.IsAdapted σ B G.W G₁.W 0 (b + 1))
    {e ei ev e' ei' ev'} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e) (hl : IsEvLoc G.M G₁.M e ei ev)
    (he' : IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e') (hl' : IsEvLoc G.M' G₁.M' e' ei' ev') {K : Subgroup (UA σ G.V.J)} {μ : LocMeas K}
    (hK : IsStab B K) (hμ : μ.Is) {X om om' R Rf om₁ om₁' R₁ Rf₁} (T : IsMatched B G X om om' R Rf)
    (T₁ : IsMatched B G₁ X om₁ om₁' R₁ Rf₁) (w : B.P) (hw : w.1 ∈ X.T) :
    ∃ φ ∈ SB _, ∃ φ' ∈ SB _, Rf.p w φ = Rf.p' w φ' ∧ Rf₁.p' w (ev' w φ') ≠ 0 ∧
      Rf₁.p w (coneF B G.M om μ w (ev w) (shiftA H H') X.ν ((b + 2 - a') / 2) φ) =
        eps B.ψ (chrW X.ν (B.τ w)) (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) • Rf₁.p' w (ev' w φ') := by
  have t := T.triple
  have t₁ := T₁.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  have hϖ : IsUnif (unifAt w.1) := exists_isUnif.choose_spec
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm w (B.τ w)
  obtain ⟨hc, κ, k1, k2, k3⟩ := nu_data t w hw
  obtain ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, mt, -, fx, -⟩ := data T w hw h k2
  obtain ⟨ι₁, ι₁', φ₁, φ₁', L₁, L₁', s₁, s₁', b1, b2, mt₁, ne₁, -, -⟩ := data T₁ w hw h k2
  have lt : (eA (b + 2) a' 0).1 < (eA (b + 2) a' (Fin.last _)).1 := by simp [eA_val]
  obtain ⟨pe', px'⟩ := plane' hB.cm (j₀ := eA (b + 2) a' 0) (j₁ := eA (b + 2) a' (Fin.last _)) hH' (ε := -1)
    (fun i j => by rw [t.geo.hW.skew, neg_one_mul]) (by simp) w lt
  obtain ⟨pe, px⟩ := plane' hB.cm (j₀ := 0) (j₁ := Fin.last _) hH (ε := 1) (fun i j => by rw [t.geo.hV.herm, one_mul]) (by simp) w
    (by simp)
  rw [map_neg, map_one] at px'
  rw [map_one] at px
  have cv := skF_cover (rfl : b + 2 = b + 2) (j₀ := 0) (j₁ := Fin.last _) (by simp)
  rw [skF_mid] at pe cv
  have cv' := skF_cover hH'.rank lt
  have nz := skF_ne hH'.rank lt
  set jc := skF hH'.rank (eA (b + 2) a' 0) (eA (b + 2) a' (Fin.last _)) with hjc
  have e1 : ev' w φ' = ((((GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ^ (κ + 1))⁻¹) ^ a') • φ₁' := by
    refine L₁'.bij.2.1 ((hl'.vac w).2 ▸ Submodule.mem_map_of_mem s') ((SB _).smul_mem _ s₁') (funext fun y => ?_)
    rw [ev0B hm hB hu h t.geo.hM' t₁.geo.hM' he' hl' L' L₁' (unit_J h t.geo.hV' t.geo.hW).1 (by rw [eV]; exact pe_one _ _) pe' px' cv' s',
      a2, map_smul, b2]
    exact int_ev hm hϖ (skF_inj _ _ _) (fun i => Fin.ext (by
        show skip 0 (b + 1) (b + i) = b + 2 + i
        unfold skip; split_ifs <;> omega)) _
      (fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi) (fun j => (nz j).2.symm) y
  let P : Finset (Fin (b + 2) × Fin (b + 2 + a')) :=
    Finset.univ.filter fun p => p.2 = eA (b + 2) a' 0 ∨ p.1 = 0 ∧ p.2 ≠ eA (b + 2) a' (Fin.last _)
  have hP : ∀ p, p ∈ P ↔ p.2 = eA (b + 2) a' 0 ∨ p.1 = 0 ∧ p.2 ≠ eA (b + 2) a' (Fin.last _) := fun p => by simp [P]
  have m0 : ∀ i : Fin b, mid i ≠ 0 := fun i h => by simpa [mid] using congrArg Fin.val h
  have ei2 : Function.Injective (eA (b + 2) a') := fun _ _ h => by simpa using finSumFinEquiv.injective h
  have e2 := cone_val hm hB hu L L₁ (hl.vac w).2 (fun φ s y => evA hm hB hu h t.geo.hM t₁.geo.hM he hl L L₁
      (unit_J h t.geo.hV t.geo.hW).1 (unit_J h t₁.geo.hV t₁.geo.hW).2 pe px cv pe' px' cv' P hP s y) hϖ X.ν hc k2 k3 s s₁ a1 b1 hμ
    (fx K hK) (shiftA_c h px px') (skF_inj _ _ _) ei2
    (fun i => Fin.ext (by have := i.2; show skip 0 (b + 1) i = i + 1
                          unfold skip; split_ifs <;> omega))
    (fun j => (nz j).1.symm) (fun j => (nz j).2.symm) (fun i j => by simp [hP, m0, (nz j).1]) (by simp [hP]) (by simp [hP, ei2.eq_iff])
    (Or.inr ⟨fun i hi => by simp [hP, hi, ei2.eq_iff], fun j => by simp [hP, m0, ei2.eq_iff]⟩) (fun j => (0, eB (b + 2) a' j))
    (fun _ _ h => by simpa [eB] using h) (fun p => by
      rw [hP]
      refine ⟨?_, fun ⟨x, y⟩ => ?_⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Or.inr ⟨rfl, fun hi => by simpa using finSumFinEquiv.injective hi⟩,
          fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi⟩
      · obtain ⟨j | j, hj⟩ := finSumFinEquiv.surjective p.2
        · exact absurd ⟨j, hj⟩ y
        · exact ⟨j, Prod.ext (x.resolve_left fun x => y ⟨_, x.symm⟩).1.symm hj⟩) ((b + 2 - a') / 2)
  have q0 : (GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ≠ 0 := by
    rw [(GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F w).1]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
  refine ⟨φ, s, φ', s', mt, ?_, ?_⟩
  · rw [e1, map_smul, ← mt₁]; exact smul_ne_zero (by positivity) ne₁
  · rw [e2, e1, eps_eq hm (isPsi hB.std hu) k1 k2, map_smul, map_smul, mt₁, smul_smul]

theorem stdA : StdA :=
  ⟨1, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf _ _ _ _ _ _ he hl he' hl' _ _ hK hμ _ _ _ _ _ _ _ _ _ T T₁ w hw => by
    simpa only [map_one, Units.val_one, one_mul] using stdA_gen cf.eV cf.hH cf.hH' he hl he' hl' hK hμ T T₁ w hw⟩

end PositivityTheory.ThKG.Std
end
end
