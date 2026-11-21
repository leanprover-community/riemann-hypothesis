import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureUAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousTensMap

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.TruncFix

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def idem (T : Finset (Pl F)) : AF F := ∑ v ∈ T, GlobalTheory.LatVac.liftV v 1

theorem evFin_liftV_one (v w : Pl F) : evFin F w (GlobalTheory.LatVac.liftV v 1) = if w = v then 1 else 0 := by
  by_cases h : w = v
  · subst h; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
  · rw [if_neg h]; exact GlobalTheory.ThK.LocalOps.evFin_of_at h (GlobalTheory.LatVac.at_liftV v 1)

theorem evFin_idem (T : Finset (Pl F)) (w : Pl F) : evFin F w (idem T) = if w ∈ T then 1 else 0 := by
  classical
  simp only [idem, map_sum, evFin_liftV_one]
  rw [Finset.sum_ite_eq]

theorem idem_mul_idem (T : Finset (Pl F)) : idem T * idem T = idem T := by
  classical
  conv_lhs => rw [idem, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, ← idem, evFin_idem, if_pos hv]

theorem idem_insert {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) :
    idem (insert v T) = GlobalTheory.LatVac.liftV v 1 + idem T := by
  classical
  rw [idem, Finset.sum_insert hv]; rfl

theorem liftV_mul_idem {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) : GlobalTheory.LatVac.liftV v 1 * idem T = 0 := by
  classical
  rw [GlobalTheory.ThK.LocalOps.liftV_one_mul, evFin_idem, if_neg hv, map_zero]

theorem idem_singleton (v : Pl F) : idem ({v} : Finset (Pl F)) = GlobalTheory.LatVac.liftV v 1 := by
  simp [idem]

def truncMat {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) := 1 + e • (A - 1)

theorem truncMat_mul {n : ℕ} {e : AF F} (he : e * e = e) {A B : Matrix (Fin n) (Fin n) (AE F E)} (h : A * B = 1) :
    truncMat e A * truncMat e B = 1 := by
  simp only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, he, Matrix.sub_mul, Matrix.mul_sub, h]
  have he2 : e ^ 2 = e := by rw [sq, he]
  match_scalars <;> ring_nf <;> simp only [he2] <;> ring

theorem truncMat_transpose {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    (truncMat e A)ᵀ = truncMat e Aᵀ := by
  simp [truncMat, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_sub]

theorem truncMat_map (σ : E →ₐ[F] E) {n : ℕ} (e : AF F) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    (truncMat e A).map (cA σ) = truncMat e (A.map (cA σ)) := by
  ext i j
  by_cases h : i = j <;> simp [truncMat, Matrix.one_apply, h]

theorem truncMat_unitary {n : ℕ} {e : AF F} (he : e * e = e) {A Ab J : Matrix (Fin n) (Fin n) (AE F E)}
    (h : Aᵀ * J * Ab = J) : (truncMat e A)ᵀ * J * truncMat e Ab = J := by
  have h' : Aᵀ * (J * Ab) = J := by rw [← Matrix.mul_assoc, h]
  rw [truncMat_transpose]
  simp only [truncMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h']
  have he2 : e ^ 2 = e := by rw [sq, he]
  match_scalars <;> ring_nf <;> simp only [he2] <;> ring

variable {σ : E →ₐ[F] E}

def truncU (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) : UA σ J :=
  ⟨⟨truncMat (idem T) k.1.1, truncMat (idem T) k.1.inv, truncMat_mul (idem_mul_idem T) k.1.val_inv,
    truncMat_mul (idem_mul_idem T) k.1.inv_val⟩, by
    show (truncMat (idem T) k.1.1)ᵀ * incM F J * (truncMat (idem T) k.1.1).map (cA σ) = incM F J
    rw [truncMat_map]
    exact truncMat_unitary (idem_mul_idem T) k.2⟩

theorem mat_truncU (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    mat (truncU T k) = truncMat (idem T) (mat k) := rfl

theorem mat_truncU_inv (T : Finset (Pl F)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    mat (truncU T k)⁻¹ = truncMat (idem T) (mat k⁻¹) := rfl

theorem truncU_insert {T : Finset (Pl F)} {v : Pl F} (hv : v ∉ T) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) :
    truncU (insert v T) k = truncU {v} k * truncU T k := by
  refine Subtype.ext (Units.ext ?_)
  show truncMat (idem (insert v T)) (mat k) = truncMat (idem {v}) (mat k) * truncMat (idem T) (mat k)
  have h0 : GlobalTheory.LatVac.liftV v 1 * idem T = 0 := liftV_mul_idem hv
  rw [idem_insert hv, idem_singleton]
  unfold truncMat
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h0,
    zero_smul, add_zero, add_smul]
  abel

theorem truncU_mem_UAt (v : Pl F) {n : ℕ} {X : Spc F E n} (k : UA σ X.J) :
    truncU {v} k ∈ UAt σ X (evFin F v) := by
  intro u hu
  rw [mat_truncU, idem_singleton]
  simp only [truncMat, add_sub_cancel_left, smul_smul]
  rw [mul_comm, GlobalTheory.ThK.LocalOps.liftV_one_mul, hu, map_zero, zero_smul]

end GlobalTheory.TruncFix
end
end

section
noncomputable section

namespace GlobalTheory.ThKLevel

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

variable (σ) in

def latLevel (W : Spc F E d) : Subgroup (UA σ W.J) where
  carrier := {k | k ∈ GlobalTheory.ThKAdm.FinPt σ W ∧ ∀ w : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W w,
    mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W w ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W w}
  one_mem' := ⟨(UAtSub σ W (fun a : AF F => a.2)).one_mem, fun w z hz => by
    simp only [inv_one]
    rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.one_mulVec]
    exact ⟨hz, hz⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(UAtSub σ W (fun a : AF F => a.2)).mul_mem hx hy, fun w z hz => ⟨?_, ?_⟩⟩
    · rw [show mat (x * y) = mat x * mat y from rfl, ← Matrix.mulVec_mulVec]
      exact (hx' w _ (hy' w z hz).1).1
    · rw [mul_inv_rev, show mat (y⁻¹ * x⁻¹) = mat y⁻¹ * mat x⁻¹ from rfl, ← Matrix.mulVec_mulVec]
      exact (hy' w _ (hx' w z hz).2).2
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨(UAtSub σ W (fun a : AF F => a.2)).inv_mem hx, fun w z hz => ⟨(hx' w z hz).2, ?_⟩⟩
    rw [inv_inv]
    exact (hx' w z hz).1

theorem mem_latLevel {W : Spc F E d} {k : UA σ W.J} : k ∈ latLevel σ W ↔ k ∈ GlobalTheory.ThKAdm.FinPt σ W ∧
    ∀ w : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W w,
      mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W w ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W w := Iff.rfl

theorem latLevel_le (W : Spc F E d) : (latLevel σ W : Set (UA σ W.J)) ⊆ GlobalTheory.ThKAdm.FinPt σ W := fun _ h => h.1

end GlobalTheory.ThKLevel

end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LatAtClosed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def intAt (F : Type) [Field F] [NumberField F] (v : Pl F) : AddSubgroup (AF F) where
  carrier := {a | At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨fun u _ => by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [smul_add, ha u hu, hb u hu, add_zero]
    · rw [map_add]; exact add_mem ha' hb'
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [smul_neg, ha u hu, neg_zero]
    · rw [map_neg]; exact neg_mem ha'

theorem continuous_evFin' (v : Pl F) : Continuous (evFin F v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_liftV (v : Pl F) : Continuous (GlobalTheory.LatVac.liftV v) := by
  show Continuous fun x => ((0 : Ainf F), singleFin v x)
  exact continuous_const.prodMk (continuous_singleFin v)

theorem isClosed_intAt (v : Pl F) : IsClosed (intAt F v : Set (AF F)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have h1 : IsClosed {a : AF F | At (evFin F v) a} := by
    have : {a : AF F | At (evFin F v) a} = ⋂ u : AF F, ⋂ (_ : evFin F v u = 0), {a | u • a = 0} := by
      ext a; simp [At]
    rw [this]
    exact isClosed_iInter fun u => isClosed_iInter fun _ =>
      isClosed_eq (continuous_const.mul continuous_id) continuous_const
  have h2 : IsClosed {a : AF F | evFin F v a ∈ v.adicCompletionIntegers F} :=
    (GroundTheory.Global.isClosed_adicCompletionIntegers v).preimage (continuous_evFin' v)
  exact h1.inter h2

theorem isCompact_intAt (v : Pl F) : IsCompact (intAt F v : Set (AF F)) := by
  refine ((PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_liftV v)).of_isClosed_subset
    (isClosed_intAt v) ?_
  rintro a ⟨ha, ha'⟩
  refine ⟨evFin F v a, ha', ?_⟩
  rw [← GlobalTheory.ThK.LocalOps.liftV_one_mul]
  have := GlobalTheory.ThK.partFin_of_at (M := AF F) (v := v) ha
  exact this

theorem isCompact_latAt {d : ℕ} (W : Spc F E d) (hL : W.L.IsLattice E) (v : Pl F) :
    IsCompact ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) := by
  have hZ : (W.L.restrictScalars ℤ).FG := hL.fg.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  have hxL : ∀ k, x k ∈ W.L := fun k => by
    have : x k ∈ Submodule.span ℤ (Set.range x) := Submodule.subset_span ⟨k, rfl⟩
    rw [hx] at this; exact this
  let g : (Fin m → AF F) → Fin d → AE F E := fun c => ∑ k, c k • fun i => inclR (F := F) (AF F) (x k i)
  have hg : Continuous g :=
    continuous_finset_sum _ fun k _ => by
      have hk : Continuous fun c : Fin m → AF F => c k := continuous_apply k
      exact hk.smul (continuous_const (y := fun i => inclR (F := F) (AF F) (x k i)))
  have heq : ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) =
      g '' Set.pi Set.univ fun _ => (intAt F v : Set (AF F)) := by
    ext z
    constructor
    · intro hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, ha', y, hy, rfl⟩ := hy
        have hy' : y ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hy
        obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy'
        refine ⟨fun k => n k • a, fun k _ => zsmul_mem (show a ∈ intAt F v from ⟨ha, ha'⟩) _, ?_⟩
        funext i
        simp only [g, Finset.sum_apply, Pi.smul_apply, map_sum, map_zsmul, Finset.smul_sum, smul_comm a, smul_assoc]
      | zero => exact ⟨0, fun k _ => zero_mem _, by simp [g]⟩
      | add y z _ _ hy hz =>
        obtain ⟨c, hc, rfl⟩ := hy
        obtain ⟨c', hc', rfl⟩ := hz
        exact ⟨c + c', fun k _ => add_mem (hc k trivial) (hc' k trivial), by
          simp only [g, Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      | neg y _ hy =>
        obtain ⟨c, hc, rfl⟩ := hy
        exact ⟨-c, fun k _ => neg_mem (hc k trivial), by
          simp only [g, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]⟩
    · rintro ⟨c, hc, rfl⟩
      refine sum_mem fun k _ => AddSubgroup.subset_closure ⟨c k, (hc k trivial).1, (hc k trivial).2, x k, hxL k, rfl⟩
  rw [heq]
  exact (isCompact_univ_pi fun _ => isCompact_intAt v).image hg

theorem isClosed_latAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ)
    (W : Spc F E d), W.L.IsLattice E → ∀ v : Pl F,
    IsClosed ((GlobalTheory.InertSph.latAt W v : AddSubgroup (Fin d → AE F E)) : Set (Fin d → AE F E)) := by
  intro F E _ _ _ _ _ d W hL v
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : T2Space (AE F E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  exact (isCompact_latAt W hL v).isClosed

end GlobalTheory.LatAtClosed
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweLocal
open scoped TensorProduct Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open MeasureTheory

noncomputable section

namespace GlobalTheory.HoweLocal.LocUnitNonsplit

variable {F : Type} [Field F] [NumberField F]

theorem lintegral_eq_of_acts {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (hT : ∀ ν : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂ν)
    {φ φ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ SB (κ → Fv F v)) (hφ₁ : φ₁ ∈ SB (κ → Fv F v))
    (hact : Acts (evFin F v) T φ φ₁)
    (μ : @Measure (κ → Fv F v) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mV : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  let ev : (κ → AF F) → (κ → Fv F v) := fun x i => evFin F v (x i)
  have hevc : Continuous ev :=
    continuous_pi fun i => (GlobalTheory.LatAtClosed.continuous_evFin' v).comp (continuous_apply i)
  have hevm : Measurable ev := hevc.measurable
  let φ₀ : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1
  have hφ₀ : φ₀ ∈ SB (κ → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ 0 = 1 := by
    show Set.indicator _ 1 0 = 1
    rw [Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} from
      fun k => zero_mem _)]
    rfl
  let lift : (κ → Fv F v) → (κ → AF F) := fun a i => GlobalTheory.LatVac.liftV v (a i)
  have hlc : Continuous lift :=
    continuous_pi fun i => (GlobalTheory.LatAtClosed.continuous_liftV v).comp (continuous_apply i)
  have hat : ∀ a, At (evFin F v) (lift a) := fun a u hu => by
    funext i; exact GlobalTheory.LatVac.at_liftV v (a i) u hu
  have hevl : ∀ a, ev (lift a) = a := fun a => by
    funext i; exact GlobalTheory.LatVac.evFin_liftV v (a i)
  have hev_add : ∀ x y, ev (x + y) = ev x + ev y := fun x y => by
    funext i; exact map_add (evFin F v) (x i) (y i)

  have hRc : Continuous R := by
    have e : R = fun x => tens (evFin F v) φ₀ R (x - lift (ev x)) := by
      funext x
      have h1 : R (x - lift (ev x)) = R x := by
        rw [sub_eq_add_neg]
        refine (hR φ₀ hφ₀).1 x _ ?_
        intro u hu
        rw [smul_neg, hat (ev x) u hu, neg_zero]
      have h2 : (fun i => evFin F v ((x - lift (ev x)) i)) = 0 := by
        funext i
        show evFin F v (x i - GlobalTheory.LatVac.liftV v (evFin F v (x i))) = 0
        rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self]
      show R x = φ₀ (fun i => evFin F v ((x - lift (ev x)) i)) * R (x - lift (ev x))
      rw [h2, hφ₀0, one_mul, h1]
    rw [e]
    exact (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hR φ₀ hφ₀).2).comp
      (continuous_id.sub (hlc.comp hevc))
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (κ → AF F), ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let d : (κ → AF F) → ENNReal := fun x => ‖R x‖ₑ ^ 2
  have hd : Measurable d := hRc.measurable.enorm.pow_const 2
  let m : Measure (κ → Fv F v) := (ν.withDensity d).map ev
  have hmint : ∀ f : (κ → Fv F v) → ENNReal, Measurable f → ∫⁻ y, f y ∂m = ∫⁻ x, d x * f (ev x) ∂ν := by
    intro f hf
    rw [lintegral_map hf hevm]
    exact lintegral_withDensity_eq_lintegral_mul ν hd (hf.comp hevm)
  have hsq : ∀ ψ' ∈ SB (κ → Fv F v), ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂m = ∫⁻ x, ‖tens (evFin F v) ψ' R x‖ₑ ^ 2 ∂ν := by
    intro ψ' hψ'
    rw [hmint _ (hψ'.1.continuous.measurable.enorm.pow_const 2)]
    congr 1
    funext x
    simp only [tens, d, ev, enorm_mul, mul_pow]
    ring

  haveI hinv : m.IsAddLeftInvariant := by
    constructor
    intro a
    ext s hs
    rw [Measure.map_apply (measurable_const_add a) hs]
    have hs' : MeasurableSet ((fun y => a + y) ⁻¹' s) := measurable_const_add a hs
    rw [← lintegral_indicator_one hs', ← lintegral_indicator_one hs, hmint _ (measurable_one.indicator hs'),
      hmint _ (measurable_one.indicator hs)]
    refine Eq.trans ?_ (lintegral_add_right_eq_self (fun x => d x * s.indicator 1 (ev x)) (lift a))
    congr 1
    funext x
    have e1 : d (x + lift a) = d x := by
      show ‖R (x + lift a)‖ₑ ^ 2 = ‖R x‖ₑ ^ 2
      rw [(hR φ₀ hφ₀).1 x _ (hat a)]
    have e2 : ev (x + lift a) = a + ev x := by rw [hev_add, hevl, add_comm]
    show d x * ((fun y => a + y) ⁻¹' s).indicator 1 (ev x) = d (x + lift a) * s.indicator 1 (ev (x + lift a))
    rw [e1, e2]
    rfl

  let U : Set (κ → Fv F v) := φ₀ ⁻¹' {1}
  have hUo : IsOpen U := hφ₀.1.isOpen_fiber 1
  have hU0 : (0 : κ → Fv F v) ∈ U := hφ₀0
  have hUm : m U < ⊤ := by
    calc m U = ∫⁻ y, U.indicator 1 y ∂m := (lintegral_indicator_one hUo.measurableSet).symm
    _ ≤ ∫⁻ y, ‖φ₀ y‖ₑ ^ 2 ∂m := lintegral_mono fun y => by
        by_cases hy : y ∈ U
        · rw [Set.indicator_of_mem hy]
          have h1 : φ₀ y = 1 := hy
          rw [h1]; simp
        · simp [hy]
    _ = ∫⁻ x, ‖tens (evFin F v) φ₀ R x‖ₑ ^ 2 ∂ν := hsq φ₀ hφ₀
    _ < ⊤ := by
        have hL := GlobalTheory.TorusDilate.memLp_of_mem_schA ν hν (hR φ₀ hφ₀).2
        have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hL.eLpNorm_lt_top
        simpa using h2
  haveI : IsLocallyFiniteMeasure m := ⟨fun y => ⟨(fun z => -y + z) ⁻¹' U,
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using hU0)),
    by rw [measure_preimage_add]; exact hUm⟩⟩

  let c := m.addHaarScalarFactor μ
  have hmc : ∀ ψ' ∈ SB (κ → Fv F v), ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂m = c * ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂μ := by
    intro ψ' hψ'
    have hc : Continuous fun y => ‖ψ' y‖ ^ 2 := hψ'.1.continuous.norm.pow 2
    have hcs : HasCompactSupport fun y => ‖ψ' y‖ ^ 2 :=
      hψ'.2.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    have key := Measure.integral_isAddLeftInvariant_eq_smul_of_hasCompactSupport m μ hc hcs
    have conv : ∀ ρ : Measure (κ → Fv F v), IsFiniteMeasureOnCompacts ρ →
        ∫⁻ y, ‖ψ' y‖ₑ ^ 2 ∂ρ = ENNReal.ofReal (∫ y, ‖ψ' y‖ ^ 2 ∂ρ) := by
      intro ρ _
      rw [ofReal_integral_eq_lintegral_ofReal (hc.integrable_of_hasCompactSupport hcs)
        (Filter.Eventually.of_forall fun _ => by positivity)]
      congr 1
      funext y
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [conv m inferInstance, key, ← conv _ inferInstance, lintegral_smul_measure]
    rfl
  have hc0 : (c : ENNReal) ≠ 0 := by
    intro h0
    have h1 := hmc φ₀ hφ₀
    rw [h0, zero_mul, hsq φ₀ hφ₀] at h1
    refine GlobalTheory.TorusDilate.lintegral_sq_ne_zero ν hν
      (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hR φ₀ hφ₀).2) ?_ h1
    show φ₀ (fun i => evFin F v ((0 : κ → AF F) i)) * R 0 ≠ 0
    have h2 : (fun i => evFin F v ((0 : κ → AF F) i)) = 0 := by funext i; exact map_zero _
    rw [h2, hφ₀0, one_mul]
    exact hR0
  have hU := hT ν hν _ (hR φ hφ).2
  rw [hact R (hR φ hφ)] at hU
  have hmm : ∫⁻ y, ‖φ₁ y‖ₑ ^ 2 ∂m = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂m := by rw [hsq φ₁ hφ₁, hsq φ hφ, hU]
  rw [hmc φ₁ hφ₁, hmc φ hφ] at hmm
  exact (ENNReal.mul_right_inj hc0 ENNReal.coe_ne_top).1 hmm

end GlobalTheory.HoweLocal.LocUnitNonsplit

open GlobalTheory.HoweLocal.LocUnitNonsplit in

theorem GlobalTheory.HoweLocal.LocUnitNonsplit.isUnitaryOn_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a b : ℕ)
    (JA : Matrix (Fin a) (Fin a) E) (B : Spc F E b) (κ : Type) [Fintype κ]
    (dA : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F B.J)) κ) (ψ : AddChar (AF F) ℂ)
    (omB : UA σ B.J →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → IsUSplitting (adeleClass F) ψ dA (actB (cA σ)) omB →
    ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) → ∀ [Invertible (2 : Fv F v)],
    ∀ (eB : UAtGrp σ B (evFin F v) ≃* UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J)),
      GlobalTheory.HoweLocal.IsCompIso σ B v eB →
    ∀ omL : UG (GlobalTheory.HoweLocal.cv σ v) (GlobalTheory.HoweLocal.Jv v B.J) →* Module.End ℂ ((κ → Fv F v) → ℂ),
      (∀ g, ∀ φ ∈ SB (κ → Fv F v), omL g φ ∈ SB (κ → Fv F v) ∧
        Acts (evFin F v) (omB (eB.symm g).1) φ (omL g φ)) →
    ∀ co : Darboux (symp (R := Fv F v) (GlobalTheory.HoweLocal.cv σ v) (-1) (GlobalTheory.HoweLocal.Jv v JA)
        (GlobalTheory.HoweLocal.Jv v B.J)) κ,
      (∀ x, co.e x = GlobalTheory.LatVac.locCo dA v (x.map (GlobalTheory.HoweLocal.liftE v))) →
    IsUnitaryOn (sbClass (Fv F v)) omL := by
  intro F E _ _ _ _ _ σ a b JA B κ _ dA ψ omB hstd hsplit v hv _ eB hcomp omL hL co hco
  intro μ hμ g φ hφ
  exact lintegral_eq_of_acts v (omB (eB.symm g).1) (fun ν hν Φ hΦ => hsplit.unit ν hν _ Φ hΦ) hφ (hL g φ hφ).1
    (hL g φ hφ).2 μ hμ
end
end
