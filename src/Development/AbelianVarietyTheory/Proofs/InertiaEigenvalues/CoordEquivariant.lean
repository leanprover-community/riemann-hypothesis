import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAdicModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwistStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodCoefficientRingPadicIntegersFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltration
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwise
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamFilGradedSymbolToTateTwist
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleTwistCoboundaryOnBallStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinfStatement

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.LocalIntegers.goodO_integers | exact GlobalTheory.LocalIntegers.goodO_integers | (intros; apply GlobalTheory.LocalIntegers.goodO_integers <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  first | exact @GlobalTheory.Cyc.isCrys_Ks_of_finrank | exact GlobalTheory.Cyc.isCrys_Ks_of_finrank | (intros; apply GlobalTheory.Cyc.isCrys_Ks_of_finrank <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_inf_filtration_ne_succ : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W), Module.Finite E ↥D → (∀ a, F (a + 1) ≤ F a) → {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  first | exact @GlobalTheory.finite_jumps_inf_filtration | exact GlobalTheory.finite_jumps_inf_filtration | (intros; apply GlobalTheory.finite_jumps_inf_filtration <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_adapted_to_separated_filtration : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  first | exact @GlobalTheory.exists_family_adapted_filtration | exact GlobalTheory.exists_family_adapted_filtration | (intros; apply GlobalTheory.exists_family_adapted_filtration <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serreTate_linearIndependent_of_weightwise : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l)), (∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E)) → ∀ (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ), (∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k) → (∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) → ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) → LinearIndependent (PadicComplex l) e := by
  first | exact @GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | exact GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | (intros; apply GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ThetaL P AI → ∀ (K : FinExt l), ∃ sy : ℤ → P.R.BdR → PadicComplex l, ∀ a : ℤ, (∀ x ∈ (P.PD K).Fil a, ∀ y ∈ (P.PD K).Fil a, sy a (x + y) = sy a x + sy a y) ∧ (∀ (c : Om l), ∀ x ∈ (P.PD K).Fil a, sy a (algebraMap (Om l) P.R.BdR c * x) = (c : PadicComplex l) * sy a x) ∧ (∀ x ∈ (P.PD K).Fil a, sy a x = 0 ↔ x ∈ (P.PD K).Fil (a + 1)) ∧ ∀ (g : GQ l), ∀ x ∈ (P.PD K).Fil a, sy a (P.actQdR g x) = chiC P.χQ a g * AI.actC g (sy a x) := by
  first | exact @GlobalTheory.DeRhamSymbol.exists_symbol | exact GlobalTheory.DeRhamSymbol.exists_symbol | (intros; apply GlobalTheory.DeRhamSymbol.exists_symbol <;> assumption)
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.InvDescent

theorem exists_invariant_of_subgroup {G F Ω V : Type} [Group G] [Field F] [Field Ω]
    [AddCommGroup V] [Module Ω V] (H : Subgroup G) [Finite (G ⧸ H)]
    (ι : F →* Ω) (σ : G → Ω →* Ω) (hσ : ∀ g h c, σ (g * h) c = σ g (σ h c))
    (hσ1 : ∀ c, σ 1 c = c)
    (hH : ∀ g, g ∈ H ↔ ∀ c, σ g (ι c) = ι c)
    (A : G → V →+ V) (hA : ∀ g h v, A (g * h) v = A g (A h v))
    (hAs : ∀ g (c : Ω) v, A g (c • v) = σ g c • A g v)
    (N₀ N₁ : Submodule Ω V) (hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀)
    (y : V) (hy : ∀ h ∈ H, A h y = y) (h0 : y ∈ N₀) (h1 : y ∉ N₁) :
    ∃ z, (∀ g, A g z = z) ∧ z ∈ N₀ ∧ z ∉ N₁ := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _

  have key : ∀ (v : V), (∀ h ∈ H, A h v = v) → ∀ g g' : G,
      (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g' → A g v = A g' v := by
    intro v hv g g' hgg'
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ H, g' = g * h :=
      ⟨g⁻¹ * g', QuotientGroup.eq.mp hgg', by group⟩
    rw [hA, hv h hh]
  have hfix : ∀ c : F, ∀ h ∈ H, A h (ι c • y) = ι c • y := by
    intro c h hh
    rw [hAs, hy h hh, ((hH h).mp hh) c]

  let T : F → V := fun c => ∑ q : G ⧸ H, A q.out (ι c • y)
  have hTinv : ∀ c g, A g (T c) = T c := by
    intro c g
    simp only [T, map_sum, ← hA]
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun q => ?_)
    apply key _ (hfix c)
    rw [MulAction.toPerm_apply, QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]
  have hT0 : ∀ c, T c ∈ N₀ := by
    intro c
    refine Submodule.sum_mem _ (fun q _ => ?_)
    rw [hAs]
    exact N₀.smul_mem _ (hN _ _ h0)
  by_contra hcon
  push Not at hcon
  have hT1 : ∀ c, T c ∈ N₁ := fun c => hcon (T c) (hTinv c) (hT0 c)

  let χ : G ⧸ H → (F →* Ω) := fun q => (σ q.out).comp ι
  have hσinv : ∀ g x, σ g⁻¹ (σ g x) = x := by
    intro g x
    rw [← hσ, inv_mul_cancel, hσ1]
  have hχ : Function.Injective χ := by
    intro q q' hqq'
    have hcq : ∀ c : F, σ q.out (ι c) = σ q'.out (ι c) := fun c => DFunLike.congr_fun hqq' c
    have hmem : q.out⁻¹ * q'.out ∈ H := by
      rw [hH]
      intro c
      rw [hσ, ← hcq, hσinv]
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.mpr hmem
  have hli : LinearIndependent Ω (fun q => (χ q : F → Ω)) :=
    (linearIndependent_monoidHom F Ω).comp χ hχ

  let w : G ⧸ H → V ⧸ N₁ := fun q => N₁.mkQ (A q.out y)
  have hrel : ∀ c : F, ∑ q, χ q c • w q = 0 := by
    intro c
    have hz := (Submodule.Quotient.mk_eq_zero N₁).mpr (hT1 c)
    simp only [T, hAs] at hz
    rw [← Submodule.mkQ_apply, map_sum] at hz
    simpa [χ, w] using hz
  have hw : ∀ q, w q = 0 := by
    intro q
    rw [← Module.forall_dual_apply_eq_zero_iff Ω]
    intro φ
    have hsum : ∑ q', φ (w q') • (χ q' : F → Ω) = 0 := by
      funext c
      have hcq := congrArg φ (hrel c)
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hcq
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hcq]
      exact Finset.sum_congr rfl (fun q' _ => mul_comm _ _)
    exact Fintype.linearIndependent_iff.mp hli _ hsum q
  have hy1 : A (QuotientGroup.mk (1 : G) : G ⧸ H).out y = y := by
    rw [key y hy _ 1 (QuotientGroup.out_eq' _)]
    exact hy 1 H.one_mem
  have hw1 := hw (QuotientGroup.mk 1)
  simp only [w, Submodule.mkQ_apply, hy1, Submodule.Quotient.mk_eq_zero] at hw1
  exact h1 hw1

variable {l : ℕ} [Fact l.Prime]

theorem smul_mem_Fil (P : LocPrime l) (K : FinExt l) (a : ℤ) (c : Om l) {x : P.R.BdR}
    (hx : x ∈ (P.PD K).Fil a) : c • x ∈ (P.PD K).Fil a := by

  have hint : IsIntegral ℚ_[l] c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  obtain ⟨K', hcK⟩ : ∃ K' : FinExt l, c ∈ K'.1 :=
    ⟨⟨IntermediateField.adjoin ℚ_[l] {c}, IntermediateField.adjoin.finiteDimensional hint⟩,
      IntermediateField.mem_adjoin_simple_self ℚ_[l] c⟩
  have hx' : x ∈ (P.PD K').Fil a := by
    rw [← SetLike.mem_coe, ← P.PD_Fil K K' a]
    exact hx
  rw [← SetLike.mem_coe, P.PD_Fil K K' a, SetLike.mem_coe]
  exact ((P.PD K').Fil a).smul_mem (⟨c, hcK⟩ : K'.1) hx'

def filOm (P : LocPrime l) (K : FinExt l) (a : ℤ) : Submodule (Om l) P.R.BdR where
  carrier := ((P.PD K).Fil a : Set P.R.BdR)
  zero_mem' := ((P.PD K).Fil a).zero_mem
  add_mem' := fun h h' => ((P.PD K).Fil a).add_mem h h'
  smul_mem' := fun c _ hx => smul_mem_Fil P K a c hx

theorem finite_quot (K E : FinExt l) : Finite (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) := by
  classical
  have : FiniteDimensional ℚ_[l] E.1 := E.2

  let f : (↥(GK K) ⧸ (GK E).subgroupOf (GK K)) → (E.1 →ₐ[ℚ_[l]] Om l) :=
    fun q => ((q.out : GQ l) : Om l →ₐ[ℚ_[l]] Om l).comp E.1.val
  refine Finite.of_injective f (fun q q' hqq' => ?_)
  have hres : ∀ x : E.1, (q.out : GQ l) x = (q'.out : GQ l) x := fun x => DFunLike.congr_fun hqq' x
  rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
  refine QuotientGroup.eq.mpr ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ ∈ IntermediateField.fixingSubgroup E.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' := hres ⟨x, hx⟩
  simp only at hx'
  rw [AlgEquiv.mul_apply, ← hx']
  exact AlgEquiv.symm_apply_apply _ _

theorem jump_descends (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l) (_hKE : K.1 ≤ E.1)
    (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l])
    (hM : ∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) (a : ℤ) (y : Fin d → P.R.BdR)
    (hy : ∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (y i)) = y)
    (h0 : ∀ i, y i ∈ (P.PD K).Fil a) (h1 : ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1))) :
    ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec
      (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧
      ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  have := finite_quot K E
  let am := algebraMap ℚ_[l] P.R.BdR

  let A : ↥(GK K) → (Fin d → P.R.BdR) →+ (Fin d → P.R.BdR) := fun g =>
    AddMonoidHom.mk' (fun v => ((M g).map am).mulVec (fun i => P.actQdR g (v i)))
      (fun v w => by simp only [Pi.add_apply, map_add]; exact Matrix.mulVec_add _ _ _)
  have hAapp : ∀ g v, A g v = ((M g).map am).mulVec (fun i => P.actQdR g (v i)) := fun _ _ => rfl
  let σ : ↥(GK K) → Om l →* Om l := fun g => MonoidHomClass.toMonoidHom (g : GQ l)
  let ι : ↥E.1 →* Om l := MonoidHomClass.toMonoidHom E.1.val
  have hσ : ∀ g h c, σ (g * h) c = σ g (σ h c) := fun g h c => by
    simp only [σ, MonoidHom.coe_coe, Subgroup.coe_mul, AlgEquiv.mul_apply]
  have hσ1 : ∀ c, σ 1 c = c := fun c => by
    simp only [σ, MonoidHom.coe_coe, OneMemClass.coe_one, AlgEquiv.one_apply]
  have hH : ∀ g, g ∈ (GK E).subgroupOf (GK K) ↔ ∀ c, σ g (ι c) = ι c := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    unfold GK
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h c => h c c.2, fun h x hx => h ⟨x, hx⟩⟩
  have hcomm : ∀ (f : P.R.BdR ≃ₐ[ℚ_[l]] P.R.BdR) (N : Matrix (Fin d) (Fin d) ℚ_[l])
      (w : Fin d → P.R.BdR), (fun i => f ((N.map am).mulVec w i)) = (N.map am).mulVec (fun i => f (w i)) := by
    intro f N w
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, am, AlgEquiv.commutes]
  have hA : ∀ g h v, A (g * h) v = A g (A h v) := by
    intro g h v
    rw [hAapp, hAapp, hAapp, hcomm, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← hM g g.2 h h.2, Subgroup.coe_mul]
    congr 1
    funext i
    rw [map_mul, AlgEquiv.mul_apply]
  have hAs : ∀ g (c : Om l) v, A g (c • v) = σ g c • A g v := by
    intro g c v
    rw [hAapp, hAapp]
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, Algebra.smul_def,
      map_mul, P.actQdR_Om, Finset.mul_sum, σ, MonoidHom.coe_coe]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  let N₀ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K a)
  let N₁ : Submodule (Om l) (Fin d → P.R.BdR) := Submodule.pi Set.univ (fun _ => filOm P K (a + 1))
  have hmem : ∀ (b : ℤ) (v : Fin d → P.R.BdR),
      v ∈ Submodule.pi Set.univ (fun _ => filOm P K b) ↔ ∀ i, v i ∈ (P.PD K).Fil b := by
    intro b v
    simp only [Submodule.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have hN : ∀ g, ∀ v ∈ N₀, A g v ∈ N₀ := by
    intro g v hv
    rw [hmem] at hv ⊢
    intro i
    rw [hAapp]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have hj : P.actQdR g (v j) ∈ (P.PD K).Fil a := by
      rw [← P.PD_actdR K g]
      exact (P.PD K).Fil_G g a _ (hv j)
    rw [Matrix.map_apply, ← Algebra.smul_def]
    exact Submodule.smul_of_tower_mem _ _ hj
  obtain ⟨z, hzA, hz0, hz1⟩ := exists_invariant_of_subgroup ((GK E).subgroupOf (GK K)) ι σ hσ hσ1 hH
    A hA hAs N₀ N₁ hN y (fun h hh => hy h ((Subgroup.mem_subgroupOf).mp hh)) ((hmem a y).mpr h0)
    (fun h => h1 ((hmem (a + 1) y).mp h))
  exact ⟨z, fun g hg => hzA ⟨g, hg⟩, (hmem a z).mp hz0, fun h => hz1 ((hmem (a + 1) z).mpr h)⟩

end GlobalTheory.InvDescent
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K E : FinExt l), K.1 ≤ E.1 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]), (∀ g ∈ GK K, ∀ h ∈ GK K, M (g * h) = M g * M h) → ∀ (a : ℤ) (y : Fin d → P.R.BdR), (∀ g ∈ GK E, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y) → (∀ i, y i ∈ (P.PD K).Fil a) → ¬ (∀ i, y i ∈ (P.PD K).Fil (a + 1)) → ∃ z : Fin d → P.R.BdR, (∀ g ∈ GK K, ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (z i)) = z) ∧ (∀ i, z i ∈ (P.PD K).Fil a) ∧ ¬ (∀ i, z i ∈ (P.PD K).Fil (a + 1)) := by
  atlas_forward_decl GlobalTheory.InvDescent.jump_descends
end

section
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc.LatBasis

theorem exists_basis_of_full {R F N V ι : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup N] [Module R N] [AddCommGroup V] [Module F V]
    (f : N →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (x : N), f (c • x) = algebraMap R F c • f x)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ x : N, algebraMap R F c • v = f x)
    (b : Module.Basis ι R N) :
    ∃ bV : Module.Basis ι F V, (∀ j, bV j = f (b j)) ∧
      ∀ x i, bV.repr (f x) i = algebraMap R F (b.repr x i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  have hsm : ∀ (c : R) (v : V), c • v = algebraMap R F c • v := fun _ _ => rfl
  haveI : IsScalarTower R F V := ⟨fun c a v => by rw [hsm, Algebra.smul_def, mul_smul]⟩
  let f' : N →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) f' :=
    { map_units := fun s => by
        rw [Module.End.isUnit_iff]
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        have : ⇑(algebraMap R (Module.End R V) s) = fun v => algebraMap R F s • v := by
          ext v; rfl
        rw [this]
        exact (MulAction.toPerm (Units.mk0 _ h0) : Equiv.Perm V).bijective
      surj := fun v => by
        obtain ⟨c, hc, x, hx⟩ := hfull v
        exact ⟨(x, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hx⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b.ofIsLocalizedModule F (nonZeroDivisors R) f',
    fun j => b.ofIsLocalizedModule_apply F _ f' j,
    fun x i => b.ofIsLocalizedModule_repr_apply F _ f' x i⟩

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {R Qp LL O : Type} [CommRing R] [IsDomain R]
  [Field Qp] [Algebra R Qp] [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL] (T : LocLat G Qp LL O) (φ : R →+* O)
  (hφ : ∀ c, algebraMap O LL (φ c) = algebraMap Qp LL (algebraMap R Qp c))
  (hint : ∀ a : LL, ∃ c : R, c ≠ 0 ∧ ∃ o : O, algebraMap O LL o = algebraMap R Qp c • a)

include hφ in
omit [IsDomain R] in

theorem smul_eq (c : R) (v : T.V) : φ c • v = algebraMap R Qp c • v := by
  rw [← algebraMap_smul LL (φ c) v, ← algebraMap_smul LL (algebraMap R Qp c) v, hφ]

include hφ hint in

theorem exists_smul_mem (v : T.V) : ∃ c : R, c ≠ 0 ∧ algebraMap R Qp c • v ∈ T.L.T := by
  have kl : ∀ (c : R) (x : T.V), x ∈ T.L.T → algebraMap R Qp c • x ∈ T.L.T := by
    intro c x hx
    rw [← smul_eq T φ hφ]
    exact T.L.T.smul_mem _ hx
  have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, kl _ _ hx⟩
  | zero => exact ⟨1, one_ne_zero, kl _ _ T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨m, hm0, hm⟩ := hy
    refine ⟨n * m, mul_ne_zero hn0 hm0, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [mul_comm, map_mul, mul_smul]; exact kl m _ hn
    · rw [map_mul, mul_smul]; exact kl n _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn0, hn⟩ := hx
    obtain ⟨y, hy, o, ho⟩ := hint a
    refine ⟨y * n, mul_ne_zero hy hn0, ?_⟩
    have h3 := T.L.T.smul_mem o hn
    rw [← algebraMap_smul LL o, ho, smul_assoc, smul_comm a] at h3
    rw [map_mul, mul_smul]
    exact h3

include hφ hint in

theorem exists_basis_compHom [IsFractionRing R Qp] {ι : Type} :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
    ∀ b : Module.Basis ι R ↥T.L.T, ∃ bV : Module.Basis ι Qp T.V, ∀ g i j,
      algebraMap R Qp (b.repr (actT T.L g (b j)) i) = bV.repr (T.ρ g (bV j)) i := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T φ
  intro b
  obtain ⟨bV, h1, h2⟩ := exists_basis_of_full (F := Qp) (V := T.V) T.L.T.subtype.toAddMonoidHom
    Subtype.val_injective (fun c x => smul_eq T φ hφ c (x : T.V))
    (fun v => by
      obtain ⟨c, hc, h⟩ := exists_smul_mem T φ hφ hint v
      exact ⟨c, hc, ⟨_, h⟩, rfl⟩) b
  refine ⟨bV, fun g i j => ?_⟩
  rw [h1]
  exact (h2 (actT T.L g (b j)) i).symm

end Generic

theorem algebraMap_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (c : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) c) =
      algebraMap ℚ_[l] ↥LL.1 (algebraMap ℤ_[l] ℚ_[l] c) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem exists_multiple_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (a : ↥LL.1) :
    ∃ c : ℤ_[l], c ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℤ_[l] ℚ_[l] c • a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h2 : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  exact ⟨y, hy, ⟨y • a, hi⟩, (algebraMap_smul ℚ_[l] y a).symm⟩

theorem exists_basis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  intro l _ K LL T d M A hM
  obtain ⟨b, hb, -⟩ := hM
  have H := exists_basis_compHom (ι := Fin d) T (algebraMap ℤ_[l] ↥(OL LL)) (algebraMap_OL LL)
    (exists_multiple_OL LL)
  obtain ⟨bV, h⟩ := H b
  refine ⟨bV, fun g i j => ?_⟩
  exact (hb g i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (h g i j))

end GlobalTheory.Cyc.LatBasis
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ bV : Module.Basis (Fin d) ℚ_[l] T.V, ∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (bV.repr (T.ρ g (bV j)) i) := by
  atlas_forward_decl GlobalTheory.Cyc.LatBasis.exists_basis_of_isMat
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  first | exact @GlobalTheory.exists_coord_tensor_dR | exact GlobalTheory.exists_coord_tensor_dR | (intros; apply GlobalTheory.exists_coord_tensor_dR <;> assumption)
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_invariants_coordinates_finrank_eq : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  first | exact @GlobalTheory.deRham_invariants_coord_finrank | exact GlobalTheory.deRham_invariants_coord_finrank | (intros; apply GlobalTheory.deRham_invariants_coord_finrank <;> assumption)
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.HTBasisEx

variable {l : ℕ} [Fact l.Prime]

theorem basis_of_invariants (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hE : E.1 = Ks K s) {d : ℕ}
    (M : GQ l → Matrix (Fin d) (Fin d) ℚ_[l]) (D : Submodule ↥E.1 (Fin d → P.R.BdR))
    (hD : ∀ y ∈ D, ∀ g ∈ GK E,
      ((M g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y)
    (hfin : Module.Finite ↥E.1 ↥D) (hd : Module.finrank ↥E.1 ↥D = d) :
    ∃ (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ), LinearIndependent (PadicComplex l) e ∧
      (∀ k, ∃ y ∈ D, (∀ i, y i ∈ (P.PD E).Fil (u k)) ∧ ¬ ∀ i, y i ∈ (P.PD E).Fil (u k + 1)) ∧
      ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
        (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (e k) = e k := by
  classical
  obtain ⟨sy, hsy⟩ := GlobalTheory.T.exists_deRhamFil_graded_symbol_to_tate_twist l P AI Θ E
  have hsum : ∀ (a : ℤ) (t : Finset (Fin d)) (f : Fin d → P.R.BdR),
      (∀ j ∈ t, f j ∈ (P.PD E).Fil a) → sy a (∑ j ∈ t, f j) = ∑ j ∈ t, sy a (f j) := by
    intro a t f
    induction t using Finset.induction_on with
    | empty =>
      intro _
      simp only [Finset.sum_empty]
      exact ((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)
    | insert j t hj ih =>
      intro hf
      have ht : ∀ j ∈ t, f j ∈ (P.PD E).Fil a := fun j h => hf j (Finset.mem_insert_of_mem h)
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        (hsy a).1 _ (hf j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ ht), ih ht]
  obtain ⟨x, u, hx, hind⟩ := GlobalTheory.T.exists_family_adapted_to_separated_filtration ↥E.1 (Fin d → P.R.BdR) D
    (fun a => Submodule.pi Set.univ fun _ => (P.PD E).Fil a) d hfin hd
    (fun a y hy i hi => (P.PD E).Fil_anti a (hy i hi))
    (by
      intro y
      choose n hn using fun i => (P.PD E).Fil_exh (y i)
      have hanti : Antitone (P.PD E).Fil := antitone_int_of_succ_le (P.PD E).Fil_anti
      obtain ⟨b, hb⟩ := (Set.finite_range n).bddBelow
      exact ⟨b, fun i _ => hanti (hb ⟨i, rfl⟩) (hn i)⟩)
    (fun y hy => funext fun i => (P.PD E).Fil_sep _ fun a => hy a i (Set.mem_univ i))
  have hxF : ∀ k i, x k i ∈ (P.PD E).Fil (u k) := fun k i => (hx k).2 i (Set.mem_univ i)
  have hact : ∀ σ ∈ GK E, ∀ k, twAct AI.actC P.χQ (u k)
      (fun g => (M g).map (algebraMap ℚ_[l] (PadicComplex l))) σ (fun i => sy (u k) (x k i)) =
        fun i => sy (u k) (x k i) := by
    intro σ hσ k
    funext i
    have hg : ∀ j, P.actQdR σ (x k j) ∈ (P.PD E).Fil (u k) := fun j => by
      rw [← P.PD_actdR E ⟨σ, hσ⟩]
      exact (P.PD E).Fil_G _ _ _ (hxF k j)
    have h1 := congrFun (hD _ (hx k).1 σ hσ) i
    conv_rhs => rw [← h1]
    simp only [twAct, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum _ _ _ (fun j _ => by
      rw [← Algebra.smul_def]
      exact ((P.PD E).Fil (u k)).smul_of_tower_mem _ (hg j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, (hsy _).2.1 _ _ (hg j),
      (hsy _).2.2.2 σ _ (hxF k j), IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l)]
    have hc : ∀ c : Om l, (c : PadicComplex l) = algebraMap (Om l) (PadicComplex l) c :=
      fun _ => rfl
    rw [hc]
    exact mul_left_comm _ _ _
  refine ⟨fun k i => sy (u k) (x k i), u, ?_, fun k => ⟨x k, (hx k).1, hxF k, fun h => ?_⟩, hact⟩
  · refine GlobalTheory.T.serreTate_linearIndependent_of_weightwise l AI.actC P.χQ (GK E) E.1 ?_ d d _ _ u hact ?_
    · intro i y hy
      have := GlobalTheory.T.tate_invariants_cyclotomic_twist l AI.actC P.χQ ⟨AI.actC_ext, AI.actC_norm⟩ P.χQ_cyc K s hs i y
        (by intro g hg; apply hy; unfold GK; rw [hE]; exact hg)
      rwa [hE]
    · intro a c hc h0
      refine hind a c hc fun i _ => ?_
      have hm : ∀ k, c k • x k i ∈ (P.PD E).Fil a := by
        intro k
        by_cases hk : u k = a
        · exact Submodule.smul_mem _ _ (hk ▸ hxF k i)
        · rw [hc k hk, zero_smul]; exact Submodule.zero_mem _
      rw [Finset.sum_apply]
      refine ((hsy a).2.2.1 _ (Submodule.sum_mem _ fun k _ => hm k)).1 ?_
      rw [hsum a _ _ fun k _ => hm k]
      have h1 := congrFun h0 i
      rw [Finset.sum_apply, Pi.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : u k = a
      · subst hk
        exact (by rw [Pi.smul_apply, Algebra.smul_def]; exact (hsy _).2.1 _ _ (hxF k i))
      · simp only [Pi.smul_apply, hc k hk, zero_smul, ZeroMemClass.coe_zero, smul_eq_mul]
        rw [((hsy a).2.2.1 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)]
        simp
  · have := hind (u k) (Pi.single k 1) (fun j hj => Pi.single_eq_of_ne (fun e => hj (by rw [e])) _)
      (by
        intro i _
        simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        exact h i) k
    simp at this

set_option maxHeartbeats 1600000 in

theorem htBasis_of_isCrys (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K : FinExt l)
    (s : ℕ) (hs : Lev l s) (E : FinExt l) (hEs : E.1 = Ks K s) (hle : K.1 ≤ E.1) (LL : FinExt l)
    (h7K : fontCore (P.PD K)) (h7E : fontCore (P.PD E))
    (T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hcrys : IsCrys (P.PD E) (T'.ρ.comp (Subgroup.inclusion (GK_le hle))))
    {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T' M A)
    (m : ℕ) (hm : s ≤ m) :
    {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
      DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a}.Finite ∧
    HTBasis AI.actC P.χQ (Gj K m) M
      {a : ℤ | DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≠
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) a} := by
  have hLL : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨bV, hbV⟩ := GlobalTheory.T.exists_padic_basis_galoisLattice_same_matrices l K LL T' d M A hM
  let ρ' : Representation ↥LL.1 ↥(GK E) T'.V := T'.ρ.comp (Subgroup.inclusion (GK_le hle))
  let AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := T'.V, ρ := T'.ρ, cont := T'.cont }
  let AE : GRep ↥(GK E) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T'.V, ρ := ρ'
      cont := fun x => (T'.cont x).comp (continuous_inclusion (GK_le hle)) }
  have hK := h7K _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AK
  have hE := h7E _ _ (GlobalTheory.T.goodCoefficientRing_padicIntegers_finExt l LL) AE
  have hanti : ∀ a, FilV (P.PD K) (LL := ↥LL.1) (V := T'.V) (a + 1) ≤ FilV (P.PD K) a := by
    obtain ⟨Φ, h1, -⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro a z hz
    exact (h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)
  refine ⟨GlobalTheory.T.finite_setOf_inf_filtration_ne_succ _ _ (DdR (P.PD K) T'.ρ) (fun a => FilV (P.PD K) a) hK.2.1.1 hanti, ?_⟩
  classical
  let M0 : GQ l → Matrix (Fin d) (Fin d) ℚ_[l] := fun g =>
    if hg : g ∈ GK K then Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i else 0
  have hM0 : ∀ g (hg : g ∈ GK K), M0 g = Matrix.of fun i j => bV.repr (T'.ρ ⟨g, hg⟩ (bV j)) i :=
    fun g hg => dif_pos hg
  have hmul : ∀ g ∈ GK K, ∀ g' ∈ GK K, M0 (g * g') = M0 g * M0 g' := by
    intro g hg g' hg'
    rw [hM0 g hg, hM0 g' hg', hM0 _ (mul_mem hg hg')]
    have key : ∀ γ : ↥(GK K), (Matrix.of fun i j => bV.repr (T'.ρ γ (bV j)) i) =
        LinearMap.toMatrix bV bV ((T'.ρ γ).restrictScalars ℚ_[l]) := fun γ => by
      ext i j
      rw [LinearMap.toMatrix_apply]; rfl
    have hcomp : (T'.ρ ⟨g * g', mul_mem hg hg'⟩).restrictScalars ℚ_[l] =
        (T'.ρ ⟨g, hg⟩).restrictScalars ℚ_[l] ∘ₗ (T'.ρ ⟨g', hg'⟩).restrictScalars ℚ_[l] := by
      refine LinearMap.ext fun v => ?_
      exact LinearMap.congr_fun (map_mul T'.ρ ⟨g, hg⟩ ⟨g', hg'⟩) v
    rw [key, key, key, hcomp]
    exact LinearMap.toMatrix_comp bV bV bV _ _
  obtain ⟨ΦE, -, hΦE⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD E) ρ' bV
  obtain ⟨DE, hDE, hfin, hdim⟩ := GlobalTheory.T.deRham_invariants_coordinates_finrank_eq (P.PD E) ρ' bV hLL hE.2.1.1 (hE.2.2 hcrys) ΦE hΦE
  have hinv : ∀ y ∈ DE, ∀ g ∈ GK E,
      ((M0 g).map (algebraMap ℚ_[l] P.R.BdR)).mulVec (fun i => P.actQdR g (y i)) = y := by
    intro y hy g hg
    have := (hDE y).1 hy ⟨g, hg⟩
    simp only [P.PD_actdR] at this
    rw [hM0 g (GK_le hle hg)]
    exact this
  obtain ⟨e, u, hli, hu, hact⟩ := basis_of_invariants P AI Θ K s hs E hEs M0 DE
    hinv hfin hdim
  have hFil : ∀ a x, x ∈ (P.PD E).Fil a ↔ x ∈ (P.PD K).Fil a := fun a x =>
    Set.ext_iff.1 (P.PD_Fil E K a) x
  refine ⟨e, u, hli, fun k => ?_, fun σ hσ k => ?_⟩
  · obtain ⟨y, hy, hy1, hy2⟩ := hu k
    simp only [hFil] at hy1 hy2
    obtain ⟨z, hz, hz1, hz2⟩ := GlobalTheory.T.deRhamFil_invariant_jump_descends_finExt l P K E hle d M0 hmul (u k) y (hinv y hy) hy1 hy2
    obtain ⟨Φ, h1, h2⟩ := GlobalTheory.T.exists_deRham_tensor_coordinates_of_basis (P.PD K) T'.ρ bV
    intro heq
    have hmem : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := by
      refine ⟨?_, (h1 _ _).2 (by simpa using hz1)⟩
      simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      apply Φ.injective
      rw [h2, Φ.apply_symm_apply]
      have := hz g g.2
      rw [hM0 g g.2] at this
      simp only [P.PD_actdR]
      exact this
    have hmem' : Φ.symm z ∈ DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) := by
      have heq' : DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k + 1) =
        DdR (P.PD K) T'.ρ ⊓ FilV (P.PD K) (u k) := heq
      rw [heq']; exact hmem
    exact hz2 (by simpa using (h1 _ _).1 hmem'.2)
  · have hσE : σ ∈ GK E := by
      refine IntermediateField.fixingSubgroup_le (?_ : E.1 ≤ Ks K m) hσ
      rw [hEs]
      refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
      change x ^ (l ^ (s + n)) = 1
      rw [pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]
    have hσK : σ ∈ GK K := GK_le hle hσE
    have hMσ : M σ = (M0 σ).map (algebraMap ℚ_[l] (PadicComplex l)) := by
      rw [hM0 σ hσK]
      ext i j
      exact hbV ⟨σ, hσK⟩ i j
    have := hact σ hσE k
    unfold twAct at this ⊢
    rw [hMσ]
    exact this

theorem exists_htBasis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  intro D HW F h7 l _ K s LL h S E' T hcr d M A hM m hm
  obtain ⟨Θ⟩ := GlobalTheory.T.nonempty_thetaOnBdRPlus_periodData D l
  obtain ⟨E, hEs⟩ : ∃ E : FinExt l, E.1 = Ks K s :=
    ⟨⟨Ks K s, GlobalTheory.MemLoc.finiteDimensional_Ks_of_finExt K s⟩, rfl⟩
  have hle : K.1 ≤ E.1 := hEs ▸ h.2.2.1
  exact htBasis_of_isCrys (D.loc l) (D.locA l) Θ K s ⟨h.1, h.2.1⟩ E hEs hle LL (h7 l K) (h7 l E) T
    (GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants l (D.loc l) K s LL _ ((HW l).W K s LL h) ((HW l).W_s K s LL h) E hEs hle T hcr)
    M A hM m hm

end GlobalTheory.HTBasisEx
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  atlas_forward_decl GlobalTheory.HTBasisEx.exists_htBasis
end

section
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem htBasis_of_isDec : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  intro l _ act χ _ _ K m d M U Dm g J hD hH
  obtain ⟨hdet, -, -, -, hrel⟩ := hD
  obtain ⟨e, u, hli, hu, hfix⟩ := hH
  have hDe : ∀ v : Fin d → PadicComplex l, Dm.mulVec (Dm⁻¹.mulVec v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hinj : ∀ v w : Fin d → PadicComplex l, Dm.mulVec v = Dm.mulVec w → v = w := by
    intro v w h
    have h2 := congrArg (fun x => Dm⁻¹.mulVec x) h
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec] using h2
  refine ⟨fun k => Dm⁻¹.mulVec (e k), u, ?_, hu, ?_⟩
  · refine LinearIndependent.of_comp Dm.mulVecLin ?_
    have : (Dm.mulVecLin ∘ fun k => Dm⁻¹.mulVec (e k)) = e := by
      funext k
      exact hDe (e k)
    rw [this]
    exact hli
  · intro σ hσ k
    apply hinj
    have hmap : (Dm.map (act σ)).mulVec (fun a => act σ (Dm⁻¹.mulVec (e k) a)) =
        fun a => act σ (e k a) := by
      funext a
      conv_rhs => rw [← hDe (e k)]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
    have h1 := hfix σ hσ k
    unfold twAct at h1 ⊢
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hrel σ hσ, ← Matrix.mulVec_mulVec, hmap, h1, hDe]

end GlobalTheory.Cyc
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m d : ℕ) (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (J : Set ℤ), IsDec act χ K m M Dm U g → HTBasis act χ (Gj K m) M J → HTBasis act χ (Gj K m) U J := by
  atlas_forward_decl GlobalTheory.Cyc.htBasis_of_isDec
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decompletion_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (Dm : Matrix (Fin d) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l), IsDec (D.locA l).actC (D.loc l).χQ K (mN l s (M0 + h0)) M Dm U g ∧ ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K (mN l s (M0 + h0))) := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_decompletion | exact GlobalTheory.Cyc.Decomp.exists_decompletion | (intros; apply GlobalTheory.Cyc.Decomp.exists_decompletion <;> assumption)
end

section
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.Graded

variable {l : ℕ} [Fact l.Prime]

theorem mem_OC_iff (y : PadicComplex l) : y ∈ PadicComplexInt l ↔ ‖y‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff]
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff (L := PadicComplex l) (Γ₀ := NNReal)).symm

theorem norm_OC (y : OC l) : ‖(y : PadicComplex l)‖ ≤ 1 := (mem_OC_iff _).1 y.2

theorem norm_alg (x : ℚ_[l]) : ‖algebraMap ℚ_[l] (PadicComplex l) x‖ = ‖x‖ := by
  exact norm_algebraMap' _ x

theorem norm_lpow (m : ℕ) : ‖(l : PadicComplex l) ^ m‖ = (l : ℝ) ^ (-(m : ℤ)) := by
  have h := norm_alg ((l : ℚ_[l]) ^ m)
  rw [map_pow, map_natCast] at h
  rw [h, Padic.norm_p_pow]

theorem eq_zero_of_norm_le (y : PadicComplex l) (h : ∀ m : ℕ, ‖y‖ ≤ 2 * (l : ℝ) ^ (-(m : ℤ))) :
    y = 0 := by
  by_contra hy
  have hpos : 0 < ‖y‖ / 2 := by positivity
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have := h m
  rw [zpow_neg, zpow_natCast, ← inv_pow] at this
  linarith

theorem theta_alg (θ : Ainf l →+* OC l) (z : ℤ_[l]) :
    ((θ (algebraMap ℤ_[l] (Ainf l) z) : OC l) : PadicComplex l) = zC z := by
  rw [← sub_eq_zero]
  apply eq_zero_of_norm_le
  intro m
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m z)
  have hz : z = (z.appr m : ℤ_[l]) + w * (l : ℤ_[l]) ^ m := by rw [hw]; ring
  have h1 : ((θ (algebraMap ℤ_[l] (Ainf l) z) : OC l) : PadicComplex l) - zC z =
      ((θ (algebraMap ℤ_[l] (Ainf l) w) : OC l) : PadicComplex l) * (l : PadicComplex l) ^ m -
        zC w * (l : PadicComplex l) ^ m := by
    generalize z.appr m = n at hz
    subst hz
    simp [zC]
  have h2 : ‖zC w‖ ≤ 1 := by rw [zC, norm_alg]; exact w.2
  have h3 := norm_OC (θ (algebraMap ℤ_[l] (Ainf l) w))
  have h4 : 0 ≤ (l : ℝ) ^ (-(m : ℤ)) := by positivity
  rw [h1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_lpow]
  nlinarith

theorem inclW_inj : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

variable {P : LocPrime l} (AI : LocAinf l P)

theorem xi_cancel {a b : Ainf l} (h : AI.ξ * a = AI.ξ * b) : a = b := by
  apply inclW_inj
  have := congrArg (inclW l) h
  rw [map_mul, map_mul] at this
  exact AI.isUnit_inclW_ξ.mul_left_cancel this

theorem εroot_pow (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ k ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem ζQ_pow (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem theta_lambda (θ : Ainf l →+* OC l) (hθ : IsTheta AI θ) (g : GQ l)
    (hg : g (P.ζQ 1) = P.ζQ 1) (lam : Ainf l) (hlam : AI.actW g AI.ξ = lam * AI.ξ) :
    ((θ lam : OC l) : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (P.χQ g : ℚ_[l]) := by
  obtain ⟨-, -, hact, hker, hζ⟩ := hθ
  have hπ : θ AI.π₁ = AI.ζ 1 - 1 := by
    rw [LocAinf.π₁, map_sub, map_one, ← hζ 1]; rfl
  have hne : ((AI.ζ 1 - 1 : OC l) : PadicComplex l) ≠ 0 := by
    intro h
    exact AI.ζ_one (sub_eq_zero.1 (Subtype.ext h))
  have hgπ : θ (AI.actW g AI.π₁) = AI.ζ 1 - 1 := by
    apply Subtype.ext
    have := hact g AI.π₁
    rw [hπ] at this
    rw [this]
    push_cast
    rw [map_sub, map_one, AI.ζ_eq, AI.actC_ext, hg]
  rw [← sub_eq_zero]
  apply mul_left_cancel₀ hne
  rw [mul_zero]
  apply eq_zero_of_norm_le
  intro m
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m (P.ζQ m) (ζQ_pow m)
  set z : Ainf l := WittVector.teichmuller l (AI.εroot m) with hz
  have hzl : z ^ (l ^ m) = 1 + AI.μ := by
    rw [hz, ← map_pow, εroot_pow, LocAinf.μ]; ring
  have h0 : θ (AI.actW g z - z ^ a) = 0 := by
    apply Subtype.ext
    rw [map_sub, map_pow]
    push_cast
    rw [hact, hζ m, AI.ζ_eq, AI.actC_ext, hga, sub_eq_zero]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  obtain ⟨b, hb⟩ := (hker _).1 h0
  have hb' : AI.actW g z = z ^ a + AI.ξ * b := by rw [← hb]; ring
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion (z ^ a) (AI.ξ * b) (l ^ m)
  obtain ⟨k', hk'⟩ := Polynomial.powAddExpansion (1 : Ainf l) AI.μ a
  have h1 : 1 + AI.actW g AI.μ = (z ^ a + AI.ξ * b) ^ (l ^ m) := by
    rw [← hb', ← map_pow, hzl, map_add, map_one]
  rw [hk, ← pow_mul, mul_comm a, pow_mul, hzl, hk', AI.μ_eq, map_mul, hlam] at h1
  have h2 : AI.actW g AI.π₁ * lam = (a : Ainf l) * AI.π₁ +
      (l : Ainf l) ^ m * ((z ^ a) ^ (l ^ m - 1) * b) + AI.ξ * (k' * AI.π₁ ^ 2 + k * b ^ 2) := by
    apply xi_cancel AI
    rw [Nat.cast_pow, one_pow, one_pow] at h1
    linear_combination h1
  have hξ : θ AI.ξ = 0 := (hker _).2 dvd_rfl
  have h3 := congrArg (fun t => ((θ t : OC l) : PadicComplex l)) h2
  simp only [map_add, map_mul, hξ, hgπ, hπ, map_pow, map_natCast, zero_mul, add_zero] at h3
  set u : OC l := (θ z ^ a) ^ (l ^ m - 1) * θ b with hu
  have h4 : ((AI.ζ 1 - 1 : OC l) : PadicComplex l) * (((θ lam : OC l) : PadicComplex l) -
      algebraMap ℚ_[l] (PadicComplex l) (P.χQ g : ℚ_[l])) = (l : PadicComplex l) ^ m * (u : PadicComplex l) -
      ((AI.ζ 1 - 1 : OC l) : PadicComplex l) *
        algebraMap ℚ_[l] (PadicComplex l) ((P.χQ g : ℚ_[l]) - a) := by
    rw [map_sub, map_natCast]
    generalize (AI.ζ 1 - 1 : OC l) = t at h3 ⊢
    push_cast at h3
    linear_combination h3
  rw [h4]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_lpow, norm_alg]
  have h5 := norm_OC u
  have h6 := norm_OC (AI.ζ 1 - 1)
  have h7 : 0 ≤ (l : ℝ) ^ (-(m : ℤ)) := by positivity
  have h8 := norm_nonneg ((P.χQ g : ℚ_[l]) - a)
  nlinarith

def toM (i : ℤ) : Ainf l →+ Mxi (AinfSub l) (xiU AI) i where
  toFun a := ⟨((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a, inclW l a, ⟨a, rfl⟩, rfl⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp [mul_add])

theorem toM_val (i : ℤ) (a : Ainf l) :
    (toM AI i a : WCb l) = ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a := rfl

theorem toM_bij (i : ℤ) : Function.Bijective (toM AI i) := by
  constructor
  · intro a b h
    have := congrArg Subtype.val h
    rw [toM_val, toM_val] at this
    exact inclW_inj ((Units.mul_right_inj _).1 this)
  · rintro ⟨x, y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

theorem toM_mem (i : ℤ) (a : Ainf l) :
    toM AI i a ∈ (Mxi (AinfSub l) (xiU AI) (i + 1)).comap (Mxi (AinfSub l) (xiU AI) i).subtype ↔
      AI.ξ ∣ a := by
  have key : ∀ b : Ainf l, ((xiU AI ^ (i + 1) : (WCb l)ˣ) : WCb l) * inclW l b =
      ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l (AI.ξ * b) := by
    intro b
    rw [zpow_add_one, Units.val_mul, map_mul, mul_assoc]; rfl
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, h⟩
    refine ⟨b, ?_⟩
    have h' : ((xiU AI ^ (i + 1) : (WCb l)ˣ) : WCb l) * inclW l b =
      ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a := h
    rw [key] at h'
    exact (inclW_inj ((Units.mul_right_inj _).1 h')).symm
  · rintro ⟨b, rfl⟩
    exact ⟨inclW l b, ⟨b, rfl⟩, key b⟩

theorem toM_smul (i : ℤ) (z : ℤ_[l]) (a : Ainf l) :
    z • toM AI i a = toM AI i (algebraMap ℤ_[l] (Ainf l) z * a) := by
  apply Subtype.ext
  rw [Submodule.coe_smul, toM_val, toM_val, map_mul, Algebra.smul_def]
  have : inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z
  rw [this]; ring

theorem toM_act (i : ℤ) (g : GQ l) : ∃ lam : (Ainf l)ˣ, AI.actW g AI.ξ = lam * AI.ξ ∧
    ∀ a : Ainf l, actM (xiOK AI) i g (toM AI i a) =
      toM AI i (((lam ^ i : (Ainf l)ˣ) : Ainf l) * AI.actW g a) := by
  obtain ⟨u, ⟨b, hb⟩, ⟨b', hb'⟩, hu⟩ := (xiOK AI).2.2 g
  have hb1 : inclW l b = u := hb
  have hb2 : inclW l b' = ((u⁻¹ : (WCb l)ˣ) : WCb l) := hb'
  have hbb : b * b' = 1 := by
    apply inclW_inj
    rw [map_mul, hb1, hb2, map_one, Units.mul_inv]
  let lam : (Ainf l)ˣ := ⟨b, b', hbb, by rw [mul_comm, hbb]⟩
  have hmap : Units.map (inclW l).toMonoidHom lam = u := Units.ext hb1
  refine ⟨lam, ?_, fun a => ?_⟩
  · apply inclW_inj
    have h1 := inclW_act AI g AI.ξ
    have h2 : AI.actWCbHom g (inclW l AI.ξ) = u * inclW l AI.ξ := hu
    rw [map_mul]
    change inclW l (AI.actWHom g AI.ξ) = inclW l b * _
    rw [← h1, h2, hb1]
  · apply Subtype.ext
    change AI.actWCbHom g (((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a) = _
    rw [toM_val, map_mul, act_zpow (act := AI.actWCbHom) g i u hu, inclW_act, map_mul, mul_zpow, Units.val_mul]
    have h3 : inclW l ((lam ^ i : (Ainf l)ˣ) : Ainf l) = ((u ^ i : (WCb l)ˣ) : WCb l) := by
      rw [← hmap, ← map_zpow]; rfl
    rw [h3]
    change _ = _ * (_ * inclW l (AI.actWHom g a))
    ring

theorem graded_of_theta (θ : Ainf l →+* OC l) (hθ : IsTheta AI θ) (i : ℤ) :
    ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧
      Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧
      ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x,
        Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  let θ' : Ainf l →+* PadicComplex l := (PadicComplexInt l).subtype.comp θ
  have hθ' : ∀ a, θ' a = ((θ a : OC l) : PadicComplex l) := fun _ => rfl
  have hker : ∀ a, θ' a = 0 ↔ AI.ξ ∣ a := by
    intro a
    rw [← hθ.2.2.2.1 a, hθ']
    exact ZeroMemClass.coe_eq_zero
  let e := AddEquiv.ofBijective (toM AI i) (toM_bij AI i)
  let f : Mxi (AinfSub l) (xiU AI) i →+ PadicComplex l :=
    θ'.toAddMonoidHom.comp e.symm.toAddMonoidHom
  have hf : ∀ a, f (toM AI i a) = θ' a := fun a => congrArg θ' (e.symm_apply_apply a)
  let Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l :=
    QuotientAddGroup.lift
      ((Mxi (AinfSub l) (xiU AI) (i + 1)).comap (Mxi (AinfSub l) (xiU AI) i).subtype).toAddSubgroup f
      (by
        intro x hx
        obtain ⟨a, rfl⟩ := (toM_bij AI i).2 x
        rw [AddMonoidHom.mem_ker, hf, hker]
        exact (toM_mem AI i a).1 hx)
  have hΦ : ∀ a, Φ (Submodule.Quotient.mk (toM AI i a)) = θ' a := fun a => hf a
  have hsurj : ∀ x : Qab (AinfSub l) (xiU AI) i (i + 1), ∃ a, x = Submodule.Quotient.mk (toM AI i a) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, rfl⟩ := (toM_bij AI i).2 y
    exact ⟨a, rfl⟩
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    rw [hΦ, hker] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((toM_mem AI i a).2 hx)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj x
      rw [Set.mem_setOf_eq, hΦ]
      exact norm_OC _
    · intro hy
      obtain ⟨a, ha⟩ := hθ.2.1 ⟨y, (mem_OC_iff y).2 hy⟩
      exact ⟨_, by rw [hΦ a, hθ', ha]⟩
  · intro z x
    obtain ⟨a, rfl⟩ := hsurj x
    rw [← Submodule.Quotient.mk_smul, toM_smul, hΦ, hΦ, map_mul, hθ', theta_alg]
  · intro g hg x
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨lam, h1, h2⟩ := toM_act AI i g
    have h3 := theta_lambda AI θ hθ g hg lam h1
    have h4 : actQab (xiOK AI) i (i + 1) g (Submodule.Quotient.mk (toM AI i a)) =
        Submodule.Quotient.mk (actM (xiOK AI) i g (toM AI i a)) := rfl
    rw [h4, h2, hΦ, hΦ, map_mul, hθ' (AI.actW g a), hθ.2.2.1, hθ' a]
    congr 1
    have h5 : Units.map θ'.toMonoidHom lam =
        Units.map (algebraMap ℚ_[l] (PadicComplex l)).toMonoidHom (P.χQ g) := Units.ext h3
    have h6 := congrArg (fun u : (PadicComplex l)ˣ => ((u ^ i : (PadicComplex l)ˣ) : PadicComplex l)) h5
    beta_reduce at h6
    rw [← map_zpow, ← map_zpow] at h6
    exact h6

theorem graded_iso : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ),
    ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧
      Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧
      ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x,
        Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  intro l _ P AI i
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_fontaineTheta_on_Ainf l P AI
  exact graded_of_theta AI θ hθ i

end GlobalTheory.Cyc.Graded
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xiGradedPiece_iso_twistedOC : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ), ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧ Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧ ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x, Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  atlas_forward_decl GlobalTheory.Cyc.Graded.graded_iso
end

section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter TensorProduct Matrix

namespace GlobalTheory.Cyc.GradedTorsion

variable {l : ℕ} [Fact l.Prime]

theorem algebraMap_eq (q : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) q = ((algebraMap ℚ_[l] (Om l) q : Om l) : PadicComplex l) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) q

theorem act_zC {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (g : GQ l) (z : ℤ_[l]) : act g (zC z) = zC z := by
  rw [zC, algebraMap_eq, ha.1, AlgEquiv.commutes]

theorem norm_l_lt : ‖(l : PadicComplex l)‖ < 1 := by
  have h : (l : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, algebraMap_eq, PadicComplex.norm_extends, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

theorem zC_add (x y : ℤ_[l]) : zC (x + y) = zC x + zC y := by simp [zC]

theorem zC_mul (x y : ℤ_[l]) : zC (x * y) = zC x * zC y := by simp [zC]

theorem zC_sum {ι : Type} (s : Finset ι) (f : ι → ℤ_[l]) : zC (∑ j ∈ s, f j) = ∑ j ∈ s, zC (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zC]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, zC_add, ih]

theorem zC_pow_l (k : ℕ) : zC ((l : ℤ_[l]) ^ k) = (l : PadicComplex l) ^ k := by simp [zC]

theorem mulVec_mem_ball {d : ℕ} {A : Matrix (Fin d) (Fin d) (PadicComplex l)}
    (hA : ∀ a b, ‖A a b‖ ≤ 1) {y : Fin d → PadicComplex l} (hy : y ∈ ball l d) :
    A *ᵥ y ∈ ball l d := by
  intro a
  simp only [Matrix.mulVec, dotProduct]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun b _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA a b) (norm_nonneg _) (hy b)

theorem twAct_smul_nat (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (n : ℕ)
    (y : Fin d → PadicComplex l) :
    twAct act χ i U σ ((n : PadicComplex l) • y) = (n : PadicComplex l) • twAct act χ i U σ y := by
  have : (fun a => act σ (((n : PadicComplex l) • y) a)) =
      (n : PadicComplex l) • fun a => act σ (y a) := by
    funext a; simp
  simp only [twAct]
  rw [this, Matrix.mulVec_smul, smul_comm]

theorem twAct_mulVec (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (i : ℤ) {d : ℕ} (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (D : Matrix (Fin d) (Fin d) (PadicComplex l)) (σ : GQ l) (h : D * U σ = M σ * D.map (act σ))
    (y : Fin d → PadicComplex l) :
    twAct act χ i M σ (D *ᵥ y) = D *ᵥ twAct act χ i U σ y := by
  have : (fun a => act σ ((D *ᵥ y) a)) = D.map (act σ) *ᵥ fun a => act σ (y a) := by
    funext a; simp [Matrix.mulVec, dotProduct]
  simp only [twAct]
  rw [this, Matrix.mulVec_mulVec, ← h, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

theorem sandwich {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
    {K : FinExt l} {m d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    {D : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l} (hD : IsDec act χ K m M D U g)
    (i : ℤ) (n : ℕ)
    (hU : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ),
      CocOn (Gj K m) (twAct act χ i U) (ball l d) c →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn (Gj K m) (twAct act χ i U) (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ))
    (c : GQ l → Fin d → PadicComplex l) (k : ℕ)
    (hc : CocOn (Gj K m) (twAct act χ i M) (ball l d) c)
    (hk : CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ)) :
    CobOn (Gj K m) (twAct act χ i M) (ball l d) (fun σ => (l : PadicComplex l) ^ (n + 1) • c σ) := by
  obtain ⟨hdet, hint, hinv, -, hcomm⟩ := hD
  set E : Matrix (Fin d) (Fin d) (PadicComplex l) := (l : PadicComplex l) • D⁻¹ with hE
  have hEint : ∀ a b, ‖E a b‖ ≤ 1 := fun a b => by simpa [hE] using hinv a b
  have hDE : ∀ y, D *ᵥ (E *ᵥ y) = (l : PadicComplex l) • y := fun y => by
    rw [Matrix.mulVec_mulVec, hE, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.smul_mulVec, Matrix.one_mulVec]
  have hinj : Function.Injective D.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det D).2 hdet)
  have hEt : ∀ σ ∈ Gj K m, ∀ y, twAct act χ i U σ (E *ᵥ y) = E *ᵥ twAct act χ i M σ y := by
    intro σ hσ y
    apply hinj
    show D *ᵥ _ = D *ᵥ _
    rw [← twAct_mulVec act χ i M U D σ (hcomm σ hσ), hDE, hDE, twAct_smul_nat]
  obtain ⟨x, hx, hxe⟩ := hU (fun σ => E *ᵥ c σ) k
    ⟨(continuous_const.matrix_mulVec continuous_id).comp_continuousOn hc.1,
      fun σ hσ => mulVec_mem_ball hEint (hc.2.1 σ hσ), fun σ hσ τ hτ => by
        simp only [hc.2.2 σ hσ τ hτ, Matrix.mulVec_add, hEt σ hσ]⟩
    (by
      obtain ⟨x, hx, hxe⟩ := hk
      refine ⟨E *ᵥ x, mulVec_mem_ball hEint hx, fun σ hσ => ?_⟩
      have := hxe σ hσ
      simp only at this ⊢
      rw [hEt σ hσ, ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul])
  refine ⟨D *ᵥ x, mulVec_mem_ball hint hx, fun σ hσ => ?_⟩
  have := hxe σ hσ
  simp only at this ⊢
  rw [twAct_mulVec act χ i M U D σ (hcomm σ hσ), ← Matrix.mulVec_sub, ← this, Matrix.mulVec_smul,
    hDE, smul_smul, pow_succ]

theorem transfer {G : Subgroup (GQ l)} {X : Type} [AddCommGroup X] [Module ℤ_[l] X]
    (ρ : Representation ℤ_[l] ↥G X) {d : ℕ}
    (A : GQ l → (Fin d → PadicComplex l) → (Fin d → PadicComplex l))
    (Ψ : X →+ (Fin d → PadicComplex l)) (hinj : Function.Injective Ψ)
    (hr : Set.range Ψ = ball l d)
    (hl : ∀ (k : ℕ) x, Ψ ((l : ℤ_[l]) ^ k • x) = (l : PadicComplex l) ^ k • Ψ x)
    (hA : ∀ (g : ↥G) x, Ψ (ρ g x) = A g (Ψ x)) (n : ℕ)
    (H : ∀ (c : GQ l → Fin d → PadicComplex l) (k : ℕ), CocOn G A (ball l d) c →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ k • c σ) →
      CobOn G A (ball l d) (fun σ => (l : PadicComplex l) ^ n • c σ)) :
    @TorsKilledBy ℤ_[l] ↥G X _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology X) ρ
      (l : ℤ_[l]) ((l : ℤ_[l]) ^ n) := by
  classical
  rintro f ⟨hfc, hfm⟩ ⟨k, x, hx⟩
  rw [continuous_adicModule_iff] at hfc
  have hb : ∀ y, Ψ y ∈ ball l d := fun y => hr ▸ ⟨y, rfl⟩
  let c : GQ l → Fin d → PadicComplex l := fun σ => if h : σ ∈ G then Ψ (f ⟨σ, h⟩) else 0
  have hc : ∀ σ (h : σ ∈ G), c σ = Ψ (f ⟨σ, h⟩) := fun σ h => dif_pos h
  have hcont : Continuous fun g : ↥G => Ψ (f g) := by
    rw [continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt (l := l))
    filter_upwards [hfc g N] with h hh
    obtain ⟨y, e⟩ := hh
    rw [dist_eq_norm, ← map_sub, e, hl, norm_smul, norm_pow]
    refine lt_of_le_of_lt ?_ hN
    exact mul_le_of_le_one_right (by positivity) ((pi_norm_le_iff_of_nonneg zero_le_one).2 (hb y))
  obtain ⟨y, hy, hye⟩ := H c k
    ⟨by
      rw [continuousOn_iff_continuous_domRestrict]
      convert hcont using 1
      funext g
      exact hc g g.2,
    fun σ hσ => by rw [hc σ hσ]; exact hb _,
    fun σ hσ τ hτ => by
      rw [hc σ hσ, hc τ hτ, hc _ (G.mul_mem hσ hτ)]
      have := hfm ⟨σ, hσ⟩ ⟨τ, hτ⟩
      rw [← hA ⟨σ, hσ⟩, ← map_add, ← this]
      rfl⟩
    ⟨Ψ x, hb x, fun σ hσ => by
      have := hx ⟨σ, hσ⟩
      simp only [Pi.smul_apply] at this
      simp only
      rw [hc σ hσ, ← hl, this, map_sub, hA]⟩
  rw [← hr] at hy
  obtain ⟨z, rfl⟩ := hy
  refine ⟨z, fun g => hinj ?_⟩
  have := hye g g.2
  simp only at this
  rw [Pi.smul_apply, hl, map_sub, hA, ← this, hc g g.2]

theorem exists_coord {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (hinj : Function.Injective Φ) (hr : Set.range Φ = {y | ‖y‖ ≤ 1})
    (hz : ∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) :
    ∃ Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l), Function.Injective Ψ ∧
      Set.range Ψ = ball l d ∧ (∀ (z : ℤ_[l]) x, Ψ (z • x) = zC z • Ψ x) ∧
      ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q := by
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := Q) b
  refine ⟨⟨⟨fun x a => Φ (e x a), ?_⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · funext a; simp
  · intro x y; funext a; simp
  · intro x y hxy
    apply e.injective
    ext a
    exact hinj (congrFun hxy a)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩ a
      exact (hr ▸ ⟨_, rfl⟩ : Φ (e x a) ∈ {y : PadicComplex l | ‖y‖ ≤ 1})
    · intro hy
      have : ∀ a, ∃ q, Φ q = y a := fun a =>
        (hr.symm ▸ hy a : y a ∈ Set.range Φ)
      choose q hq using this
      refine ⟨e.symm (Finsupp.equivFunOnFinite.symm q), ?_⟩
      funext a
      simp [hq]
  · intro z x
    funext a
    simp [hz]
  · intro t q a
    simp [e, hz]

theorem coord_equivariant {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    (χ : GQ l →* ℚ_[l]ˣ) (i : ℤ) {T Q : Type} [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup Q]
    [Module ℤ_[l] Q] {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] T) (Φ : Q →+ PadicComplex l)
    (Ψ : T ⊗[ℤ_[l]] Q →+ (Fin d → PadicComplex l))
    (hΨ : ∀ t q a, Ψ (t ⊗ₜ q) a = zC (b.repr t a) * Φ q)
    (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (r : T →ₗ[ℤ_[l]] T)
    (s : Q →ₗ[ℤ_[l]] Q) (hM : ∀ a j, M g a j = zC (b.repr (r (b j)) a))
    (hs : ∀ x, Φ (s x) = chiC χ i g * act g (Φ x)) (x : T ⊗[ℤ_[l]] Q) :
    Ψ (TensorProduct.map r s x) = twAct act χ i M g (Ψ x) := by
  induction x using TensorProduct.induction_on with
  | zero => funext a; simp [twAct, Matrix.mulVec, dotProduct]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    funext a
    simp [twAct, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  | tmul t q =>
    funext a
    have h1 : b.repr (r t) a = ∑ j, b.repr (r (b j)) a * b.repr t j := by
      conv_lhs => rw [← b.sum_repr t, map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    simp only [TensorProduct.map_tmul, hΨ, twAct, Pi.smul_apply, smul_eq_mul, Matrix.mulVec,
      dotProduct, map_mul, act_zC ha, hM, hs, h1, zC_sum, zC_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

theorem rI_eq (l m : ℕ) (J : Finset ℤ) (i : ℤ) :
    rI l m (J : Set ℤ) i = ∑ u ∈ J.erase i, (m + padicValInt l (u - i)) := by
  rw [rI, ← finsum_mem_finset_eq_sum]
  refine finsum_congr fun u => ?_
  by_cases h1 : u ∈ J <;> by_cases h2 : u = i <;> simp [h1, h2, vZ]

theorem of_basis (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l)
    {T : Type} [AddCommGroup T] [Module ℤ_[l] T] (m : ℕ) (hlev : Lev l m)
    (ρ : ↥(Gj K m) →* (T →ₗ[ℤ_[l]] T)) (i : ℤ)
    (J : Set ℤ) (hfin : J.Finite) {d : ℕ} {M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)}
    (b : Module.Basis (Fin d) ℤ_[l] T)
    (hb : ∀ (σ : ↥(Gj K m)) a j, M σ a j = zC (b.repr (ρ σ (b j)) a))
    {Dm : Matrix (Fin d) (Fin d) (PadicComplex l)} {g : GQ l}
    (hD : IsDec AI.actC P.χQ K m M Dm U g) (hHT : HTBasis AI.actC P.χQ (Gj K m) M J) :
    @TorsKilledBy ℤ_[l] _ _ _ _ _ _ _ ((Ideal.span {(l : ℤ_[l])}).adicModuleTopology _)
      (repQ AI (Gj K m) ρ i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l m J i))) := by
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hHT' := GlobalTheory.T.hodgeTateBasis_of_isDecompletionAtLevel l _ _ ha hχ K _ d M U Dm g _ hD hHT
  have hJ : J = (hfin.toFinset : Set ℤ) := hfin.coe_toFinset.symm
  have hc6 := GlobalTheory.T.cocycle_twist_coboundary_on_ball l _ _ ha hχ K _ d hlev U g hD.2.2.2.1 hfin.toFinset (hJ ▸ hHT') i
  rw [← rI_eq, ← hJ] at hc6
  have hs := sandwich hD i _ hc6
  obtain ⟨Φ, hinj, hr, hz, hact⟩ := GlobalTheory.T.xiGradedPiece_iso_twistedOC l P AI i
  obtain ⟨Ψ, hΨi, hΨr, hΨz, hΨ⟩ := exists_coord b Φ hinj hr hz
  have hn : 2 + max 1 (rI l m J i) = 1 + max 1 (rI l m J i) + 1 := by omega
  rw [hn]
  refine transfer _ (twAct AI.actC P.χQ i M) Ψ hΨi hΨr
    (fun k x => by rw [hΨz, zC_pow_l]) (fun σ x => ?_) _ hs
  have hζ : (σ : GQ l) (P.ζQ 1) = P.ζQ 1 := by
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ ?_
    refine (le_sup_right : _ ≤ Ks K _) (IntermediateField.subset_adjoin _ _ ?_)
    show P.ζQ 1 ^ (l ^ m) = 1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlev.1
    have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
    rw [pow_add, pow_one, pow_mul, h1, one_pow]
  exact coord_equivariant ha _ i b Φ Ψ hΨ M σ (ρ σ)
    (actQab (xiOK AI) i (i + 1) σ) (hb σ) (hact σ hζ) x

theorem torsion_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (i : ℤ) (hle : Gj K (mN l s (M0 + h0)) ≤ GK K), HypW S E T M0 h0 → letI := zlMod LL T; letI : TopologicalSpace (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) i (i + 1))) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; TorsKilledBy (repQ (D.locA l) (Gj K (mN l s (M0 + h0))) ((actTZ LL T).comp (Subgroup.inclusion hle)) i (i + 1)) (l : ℤ_[l]) ((l : ℤ_[l]) ^ (2 + max 1 (rI l (mN l s (M0 + h0)) (Jset S T) i))) := by
  intro D HW F h7 l _ K s LL h S E T M0 h0 i hle hW
  have hsm : s ≤ mN l s (M0 + h0) := by unfold mN; omega
  have hlev : Lev l (mN l s (M0 + h0)) :=
    ⟨le_trans h.1 hsm, fun h2 => le_trans (h.2.1 h2) hsm⟩
  have h1 := (GlobalTheory.T.exists_continuous_galoisLatticeMatrix_integral l K LL T).1
  refine h1.elim fun d h1 => h1.elim fun M h1 => h1.elim fun A hM => ?_
  have h2 := GlobalTheory.T.exists_decompletion_frame_of_lattice D HW F l K s LL h T M0 h0 hW d M A hM
  refine h2.elim fun Dm h2 => h2.elim fun U h2 => h2.elim fun g hD => ?_
  have h3 := GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks D HW F h7 l K s LL h T hW.1 d M A hM _ hsm
  refine Exists.elim hM fun b hb => ?_
  exact @of_basis l _ (D.loc l) (D.locA l) K _ _ (zlMod LL T) _ hlev
    ((actTZ LL T).comp (Subgroup.inclusion hle)) i _ h3.1 d M U b
    (fun σ => hb.1 (Subgroup.inclusion hle σ)) Dm g hD.1 h3.2

end GlobalTheory.Cyc.GradedTorsion
end
end
