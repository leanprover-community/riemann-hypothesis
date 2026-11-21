import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.AdDecompK
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.CwInvIota
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.SchwartzOfConstantPolynomialOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingGrp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaA
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ContinuousIns

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem crd_add_k (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add, Finsupp.coe_add, Pi.add_apply]
theorem crd_fin_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) : (d.crd Z k).2 = 0 := by
  have h := congrArg (fun M => d.crd M k) hZ
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, Matrix.zero_apply, map_zero, Finsupp.coe_zero,
    Pi.zero_apply, smul_eq_mul] at h
  have h2 := congrArg Prod.snd h
  have e : ∀ c : AF F, (finOne F * c).2 = c.2 := fun c => by
    show (1 : Af F) * c.2 = c.2
    exact one_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [← e]
  exact h2
theorem loc_add_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {Z : Mx F E d.m d.n} (hZ : d.cw w Z = 0) (X : Mx F E d.m d.n) :
    R.loc w (X + Z) = R.loc w X := by
  have : d.cw w (X + Z) = d.cw w X := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at hZ ⊢
    rw [Matrix.map_add _ (map_add _), hZ, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [this]
def psiW_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2
theorem vg_tens_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g = R.tens w (fP 1) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  ring
theorem psiW_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w X := by
  intro X Z h1 h2
  have e1 : (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' (X + Z))) = ∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X) :=
    Finset.prod_congr rfl fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w' (h1 w' (Finset.ne_of_mem_erase hw'))]
  have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
    funext k
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_add_k]
    show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_fin_k h2, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k
  rw [e1, e2]
theorem gauss_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ X Z, (∀ w, d.cw w Z = 0) → (∏ w, fP 1 (R.loc w (X + Z))) = ∏ w, fP 1 (R.loc w X) := by
  intro X Z h
  exact Finset.prod_congr rfl fun w _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w (h w)]
theorem fP_smul_one_k (c : ℂ) (u : Fin d.m → Fin d.n → ℂ) : fP (c • (1 : PX d.m d.n)) u = c * fP 1 u := by
  simp only [fP, evX, MvPolynomial.smul_eq_C_mul, mul_one, MvPolynomial.eval_C, map_one, one_mul]
theorem isSchwartz_fourierProjection_one : IsSw (fP (1 : PX d.m d.n)) := by
  obtain ⟨φ, hφ⟩ := KMain.schwartz_polyGauss (m := d.m) (n := d.n) (2 * Real.pi) (by positivity) 1
  exact ⟨φ, hφ⟩
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem iota_vg_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (hy : InK (mR y))
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) :
    ∃ c : ℂ, d.T (d.om (R.ι w y) Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R (c • g) := by
  obtain ⟨L, hL⟩ := hO F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hld, -, hk⟩ := hI F E σ d R w L hL
  have h1 := (hL y _ _root_.PositivityTheory.SiegelWeilFormula.Avac.isSchwartz_fourierProjection_one).2 (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_indep_k R g w) Φ hΦ (hT.trans (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R g w))
  refine ⟨F0 p q e y, ?_⟩
  rw [h1, hk y 1 hy, hld.kvac y hy, _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_tens_k R _ w]
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k, Pi.smul_apply, smul_eq_mul, _root_.PositivityTheory.SiegelWeilFormula.Avac.fP_smul_one_k]
  ring
theorem dZ_conjT_k {ζ : ℂ} : (dZ d.n ζ)ᴴ = dZ d.n (star ζ) := by
  simp [dZ, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_smul]
theorem star_zeta_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : star R.ζ = R.ζ⁻¹ := by
  rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
theorem kdec_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : d.G)
    (hk : d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) :
    ∃ y : GR d.n, InK (mR y) ∧ d.cw w (inFrame d.b (R.ι w y)) = d.cw w (inFrame d.b k) := by
  have hζ0 := Krd.zeta_ne R.hζ
  obtain ⟨M, hM⟩ : ∃ M, M = d.cw w (inFrame d.b k) := ⟨_, rfl⟩
  have hY := Krd.inG_conj R.hζ M (hM ▸ _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.form_w_k d R w k)
  have hMM : Mᴴ * M = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 (hM ▸ hk)
  refine ⟨mkGR _ hY, ⟨hY, ?_⟩, ?_⟩
  · show (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)ᴴ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹) = 1
    have hA : (dZ d.n R.ζ)ᴴ = dZ d.n R.ζ⁻¹ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k]
    have hB : (dZ d.n R.ζ⁻¹)ᴴ = dZ d.n R.ζ := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.dZ_conjT_k, star_inv₀, _root_.PositivityTheory.SiegelWeilFormula.Avac.star_zeta_k, inv_inv]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, hB]
    calc dZ d.n R.ζ * (Mᴴ * dZ d.n R.ζ⁻¹) * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹)
        = dZ d.n R.ζ * (Mᴴ * (dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) * M) * dZ d.n R.ζ⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, hMM, Matrix.mul_one, Krd.dZ_mul_inv hζ0]
  · rw [← hM]
    have h := R.at_w w (mkGR _ hY)
    calc d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))
        = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w (mkGR _ hY)))) := by
          rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
      _ = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * M * dZ d.n R.ζ⁻¹ * dZ d.n R.ζ) := by rw [h]; rfl
      _ = M := by
          simp only [Matrix.mul_assoc]
          rw [Krd.dZ_inv_mul hζ0, Matrix.mul_one, ← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
theorem cw_inv_iota_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (y : GR d.n) (k : d.G) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b (R.ι w y)⁻¹) * d.cw w' (inFrame d.b k) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k]
theorem peel_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : Finset (InfinitePlace F)) :
    ∀ k : d.G, (∀ w ∈ S, d.cw w (inFrame d.b k) * (d.cw w (inFrame d.b k))ᴴ = 1) →
      (∀ w ∉ S, d.cw w (inFrame d.b k) = 1) → ∀ g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), ∀ Φ ∈ d.sch,
        d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g → ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' := by
  induction S using Finset.induction_on with
  | empty =>
    intro k _ h1 g hg Φ hΦ hT
    obtain ⟨g', hg', H⟩ := hA F E σ d k (fun w => h1 w (Finset.notMem_empty w)) g hg
    exact ⟨g', hg', H _ (_root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_indep_k R) Φ hΦ hT⟩
  | insert w S hw ih =>
    intro k h0 h1 g hg Φ hΦ hT
    obtain ⟨y, hy, hyw⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.kdec_k R w k (h0 w (Finset.mem_insert_self w S))
    have hinv : ∀ w', w' ≠ w → d.cw w' (inFrame d.b (R.ι w y)⁻¹) = 1 := fun w' h => by
      rw [← map_inv]; exact R.off_w w w' y⁻¹ h
    have e1 : d.cw w (inFrame d.b (R.ι w y)⁻¹) * d.cw w (inFrame d.b (R.ι w y)) = 1 := by
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k, _root_.PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics.cw_one_k]
    have hkw : d.cw w (inFrame d.b ((R.ι w y)⁻¹ * k)) = 1 := by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, ← hyw, e1]
    have hkw' : ∀ w', w' ≠ w → d.cw w' (inFrame d.b ((R.ι w y)⁻¹ * k)) = d.cw w' (inFrame d.b k) := fun w' h => by
      rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.cw_inv_iota_k, hinv w' h, Matrix.one_mul]
    obtain ⟨g₁, hg₁, e₁⟩ := ih ((R.ι w y)⁻¹ * k)
      (fun w' h => by
        rw [hkw' w' (fun e => hw (e ▸ h))]
        exact h0 w' (Finset.mem_insert_of_mem h))
      (fun w' h => by
        by_cases e : w' = w
        · rw [e, hkw]
        · rw [hkw' w' e]
          exact h1 w' fun h' => (Finset.mem_insert.1 h').elim e h)
      g hg Φ hΦ hT
    obtain ⟨c, e₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.iota_vg_k hO hI R w y hy (d.ok.dbl.weil.2.1.pres _ Φ hΦ) e₁
    refine ⟨c • g₁, Submodule.smul_mem _ c hg₁, ?_⟩
    rw [show k = R.ι w y * ((R.ι w y)⁻¹ * k) from (mul_inv_cancel_left _ _).symm, map_mul, Module.End.mul_apply]
    exact e₂
theorem vg_K'_k (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hT : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g)
    {k : d.G} (hk : k ∈ d.K) : ∃ g' ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F), d.T (d.om k Φ) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g' :=
  _root_.PositivityTheory.SiegelWeilFormula.Avac.peel_k hO hI hA R Finset.univ k (fun w _ => ((d.ok.stdK k).1 hk).1 w) (fun w h => absurd (Finset.mem_univ w) h) g hg Φ hΦ hT
theorem vac_K'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac := by
  let S' : Submodule ℂ d.Fn :=
    { carrier := {Φ | Φ ∈ d.sch ∧ ∀ k ∈ d.K, d.T (d.om k Φ) ∈ R.vac}
      zero_mem' := ⟨zero_mem _, fun k _ => by
        rw [map_zero]
        have : d.T 0 = 0 := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_zero
        rw [this]; exact zero_mem _⟩
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun k hk => by
        rw [map_add]
        have : d.T (d.om k a + d.om k b) = d.T (d.om k a) + d.T (d.om k b) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_add _ _
        rw [this]; exact add_mem (ha.2 k hk) (hb.2 k hk)⟩
      smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun k hk => by
        rw [map_smul]
        have : d.T (c • d.om k a) = c • d.T (d.om k a) := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_smul _ _
        rw [this]; exact Submodule.smul_mem _ c (ha.2 k hk)⟩ }
  have hle : R.vac ≤ S'.map (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    have hm : _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g ∈ d.schM := (hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg))
    obtain ⟨Φ, hΦ, e⟩ := (hT.1 F E σ d).2.1 _ hm
    refine ⟨Φ, ⟨hΦ, fun k hk => ?_⟩, e⟩
    obtain ⟨g', hg', e'⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_K'_k hO hI hA R hg hΦ e hk
    rw [e']; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R hg'
  intro Φ hΦ hv k hk
  obtain ⟨Φ', hΦ', e⟩ := hle hv
  have : Φ' = Φ := _root_.PositivityTheory.SiegelWeilFormula.Avac.T_inj_k hT.1 hΦ'.1 hΦ e
  rw [← this]
  exact hΦ'.2 k hk
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : Fin d.m × Fin d.n × Fin 2 → Af F :=
  fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0
def ext_k (X' : Mx F E d.m L.n) : Mx F E d.m d.n := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0
theorem choose_em_k (j : Fin L.n) (h : ∃ j', L.em j' = L.em j) : h.choose = j := L.inj h.choose_spec
theorem ext_sub_k (X : Mx F E d.m d.n) (hX : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em) = X := by
  funext a i
  by_cases h : ∃ j, L.em j = i
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]
  · have : i = L.i₀ := by
      by_contra hi
      exact h ((L.rng i).1 hi)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_neg h]
    rw [this, hX]
theorem crd_ext_k (X' : Mx F E d.m L.n) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') k).2 = _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (fun k' => (L.sd.crd X' k').2) k := by
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl
theorem continuous_ins_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (F := F)) := by
  refine continuous_pi fun k => ?_
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]; exact continuous_apply _
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h]; exact continuous_const
def prj_k (z : Fin d.m × Fin d.n × Fin 2 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)
theorem prj_ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z) = z := by
  funext k
  have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L k.2.1 h]
theorem SB_ins_k {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) ∈ SB (Fin d.m × Fin L.n × Fin 2 → Af F) := by
  refine ⟨hg.1.comp_continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L), ?_⟩
  have hc : IsCompact (_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L '' tsupport g) := hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  refine (tsupport_comp_subset_preimage g (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L)).trans fun z hz => ⟨_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z, hz, _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_ins_k L z⟩
theorem sum_loc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X : Mx F E d.m d.n) :
    ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R.fr w)⁻¹).1 *ᵥ fun b => d.cw w X b i) a‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply, norm_star]
  rfl
theorem hζ'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ = 1 ∨ R.ζ = Complex.I := by
  rcases R.hζ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2
theorem gauss_ext_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (w : InfinitePlace F) (X' : Mx F E d.m L.n) :
    fP 1 (R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = fP 1 (R'.loc w X') := by
  suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') a i‖ ^ 2 by
    simp only [fP, gs, key, evX, map_one]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k]
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
  · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    have : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b i) = 0 := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]
    simp [this]
  · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
    have e : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b (L.em j)) = fun b => L.sd.cw w X' b j := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L j h]
    rw [e]
    exact norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R')
      (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R) (R'.hfr w) (R.hfr w) _
theorem res_vg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) :
    (fun X' => _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := by
  funext X'
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => _root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_ext_k L R R' w X'
  · congr 1
    funext k
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.crd_ext_k L X' k
def resL_k : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L)
theorem res_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ R.vac) : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L f ∈ R'.vac := by
  have : R.vac ≤ R'.vac.comap (_root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) ∈ R'.vac
    have e : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vg_k L R R' g
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R' (_root_.PositivityTheory.SiegelWeilFormula.Avac.SB_ins_k L hg)
  exact this hf
theorem vac_res'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac := by
  intro Φ hΦ hv
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ R'.vac := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vac_k L R R' hv
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ L.sd.schM := (hF F E σ L.sd R').1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R' h1)
  obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ h2
  refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
  rw [e]
  show d.T Φ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em)) = d.T Φ X
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_sub_k L X hX]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem vacK_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hO : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.FinAct_k) : _root_.PositivityTheory.SiegelWeilFormula.VacK_k := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_K'_k hT hF hO hI hA R, _root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R, fun L R' => _root_.PositivityTheory.SiegelWeilFormula.Avac.vac_res'_k L hT hF R R'⟩
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end
