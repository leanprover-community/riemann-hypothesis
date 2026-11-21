import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewform2A
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.CharPolSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.OrdPlain
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJacqOfU
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfDualR
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharLocalArtinEqCyclotomicTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.DeRhamWeightsOfLocalArtinCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdFlagU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocCharDR
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.AutNewformAOfEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSelfTwGal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAUpDownOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist' :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (χ : HChar F) (ξ : G F Ω →* (Qbar l)ˣ) (t : ℤ), IsOpen (ξ.ker : Set (G F Ω)) → IsCharOf ι χ (cycBar F Ω l ^ t * ξ) → ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ s : Weil h, ((χ.loc w (a s) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (t * deg s) * ι (ξ (s : G F Ω) : Qbar l) := by
  intro N F Ω _ _ _ _ _ l _ ι χ ξ t hξ ⟨hc, art, n, hart, _, hL⟩ w hw A h a ha s
  haveI : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen hξ
  have hN : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 := UpperTheory.V.Loc.laHecke h art hart ι χ n _ hL ⟨a, ha⟩
  have h2 := UpperTheory.V.Loc.laArith N.aut.art h hw ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype)
    (hc.comp continuous_subtype_val) t ξ.ker.index (Nat.pos_of_ne_zero hN) fun g _ => by
      have e : ((cycBar F Ω l ^ t * ξ).comp (Dec (F := F) A).subtype) g * cycBar F Ω l g ^ (-t) = ξ g := by
        show cycBar F Ω l g ^ t * ξ g * cycBar F Ω l g ^ (-t) = ξ g
        rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
      rw [e, ← map_pow]
      exact ξ.ker.pow_index_mem _
  have h3 := UpperTheory.V.Loc.laUnique h ⟨a, ha⟩ _ _ _ h1 h2
  haveI : Fintype {j : w.adicCompletion F →+* Qbar l // Continuous j} := @Fintype.ofFinite _ (finite_contEmb w)
  have h4 : locPow ι n w (a s : w.adicCompletion F) = Hi.algPow w (fun _ => 1) (a s : w.adicCompletion F) ^ t := by
    unfold locPow Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [neg_injective (congrFun h3 j), zpow_one]
  have h0 : Hi.algPow w (fun _ : F →+* Qbar l => 1) (a s : w.adicCompletion F) ^ t ≠ 0 := by
    refine zpow_ne_zero _ ?_
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype]
    exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 (a s).ne_zero)
  have h5 := hL.loc (a s) s (ha.glob art hart s)
  have h6 := UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s
  have h7 : (((cycBar F Ω l ^ t * ξ) (s : G F Ω) : (Qbar l)ˣ) : Qbar l) =
      (cycBar F Ω l (s : G F Ω) : Qbar l) ^ t * (ξ (s : G F Ω) : Qbar l) := by
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_mul]
    rfl
  rw [h7, h6, h4, mul_zpow, mul_right_comm, mul_left_inj' h0, eq_comm, RingEquiv.symm_apply_eq] at h5
  rw [h5, map_mul, map_zpow₀, map_zpow₀, map_natCast, ← zpow_mul, mul_comm t]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Sd.OrdinaryAbove
section Loc
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
end Loc
private theorem norm_fin {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
    (ξ : G F Ω →* (Qbar l)ˣ) (hξ : IsOpen (ξ.ker : Set (G F Ω))) (g : G F Ω) : ‖(ξ g : Qbar l)‖ = 1 := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have : Finite (G F Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ hξ
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ (g ^ ξ.ker.index) = 1 := Subgroup.pow_index_mem ξ.ker g
  have h2 : ‖(ξ g : Qbar l)‖ ^ ξ.ker.index = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← map_pow, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) h0).1 h2
private theorem dualTw_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp), fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
private theorem cont_cyc (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  _root_.UpperTheory.Reformulated.B.CyclotomicCharacterContinuous.cont_cyc F Ω l
theorem central_weil_ordinary_above (hP : _root_.UpperTheory.V.Af.HypothesesH') {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ξ : G F Ω →* (Qbar l)ˣ} {s c m a π r}
    (H : OrdForm ι ξ s c m a π r) {w : HeightOneSpectrum (𝓞 F)} (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {ar : Weil h →* (w.adicCompletion F)ˣ} (har : IsLocalArtin h ar)
    {σ : SmIrr (GL (Fin 2) (w.adicCompletion F))} (hσ : LocIsotypic π.finPart w σ) (t : Weil h) (z : ℂ)
    (hz : ∀ v, σ.ρ (Matrix.GeneralLinearGroup.scalar (Fin 2) (ar t)) v = z • v) :
    ‖ι.symm z‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ ((s + 1) * deg t) := by
  have e : Matrix.GeneralLinearGroup.det.comp r * cycBar F Ω l ^ (((2 : ℕ) : ℤ) - 1) = cycBar F Ω l ^ (s + 1) * ξ := by
    rw [H.det, _root_.zpow_add, mul_right_comm]
    norm_num
  have hc : Continuous (cycBar F Ω l ^ (s + 1) * ξ : G F Ω →* (Qbar l)ˣ) := by
    rw [← e]
    exact (Matrix.GeneralLinearGroup.continuous_det.comp H.cont).mul ((cont_cyc F Ω l).zpow _)
  obtain ⟨χ, hχ⟩ := (_root_.UpperTheory.V.Af.algOfCyc_s hP F Ω l ι).1 _ hc fun v hv => by
    have hA := isPlaceOver_placeOf Ω v
    refine ⟨_, hA, s + 1, 1, one_pos, fun g hg => ?_⟩
    have h1 : ξ g = 1 := (H.ram v _ hA).2 (Or.inr hv) hg
    rw [pow_one, MonoidHom.mul_apply, h1, mul_one, MonoidHom.zpow_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero]
  have hd := (_root_.UpperTheory.V.Af.self_dual_real_of_printed_hida hP F Ω l ι 2 one_le_two r π H.att _ χ (dualTw_det r) (e ▸ hχ)).1
  have h1 := UpperTheory.central_char_sq_eq_of_isSelfDualBy F π χ hd w σ hσ _ z hz
  rw [_root_.UpperTheory.heckeChar_localArtin_eq_cyclotomic_twist' hP.litN F Ω l ι χ ξ (s + 1) H.ξ_open hχ w hw A h ar har t] at h1
  have h2 := congrArg (fun x => ‖ι.symm x‖) h1
  simp only [map_pow, map_mul, map_zpow₀, map_natCast, RingEquiv.symm_apply_apply, norm_pow, norm_mul, norm_zpow,
    norm_fin ξ H.ξ_open, mul_one] at h2
  exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg (norm_nonneg _) _) two_ne_zero).1 h2
end UpperTheory.V.Sd.OrdinaryAbove
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section Phi
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem exists_trace {k U D : Type} [Field k] [Field U] [AddCommGroup D] [Module k D]
    (m : U →+* End k D) (φ : End k D) (n : ℕ) (hn : 0 < n) (t : ℕ → U)
    (ht : ∀ i j : Fin n, t i = t j → i = j) (htn : t n = t 0)
    (hφ : ∀ i j : ℕ, φ ^ i * m (t 0 ^ j) = m (t i ^ j) * φ ^ i) (x : D) (hx : x ≠ 0) (hp : (φ ^ n) x = x) :
    ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 ∧
      φ ((∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x) = (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x := by
  have h1 : ∃ j : ℕ, (∑ i ∈ Finset.range n, φ ^ i * m (t 0 ^ j)) x ≠ 0 := by
    by_contra hc
    push Not at hc
    letI : Module U D := Module.compHom D m
    refine hx ((Module.forall_dual_apply_eq_zero_iff U x).mp fun f => ?_)
    have h2 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (f := fun i : Fin n => t i)
      (v := fun i : Fin n => f ((φ ^ (i : ℕ)) x)) ht (fun j => by
        have h3 := congrArg f (hc j)
        rw [map_zero, LinearMap.sum_apply, map_sum, Finset.sum_range] at h3
        rw [← h3]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hφ, mul_comm, ← smul_eq_mul, ← map_smul]
        rfl)
    simpa using congrFun h2 ⟨0, hn⟩
  obtain ⟨j, hj⟩ := h1
  refine ⟨j, hj, ?_⟩
  have h4 : (φ ^ n * m (t 0 ^ j)) x = (φ ^ 0 * m (t 0 ^ j)) x := by
    rw [hφ, htn, End.mul_apply, hp, pow_zero, one_mul]
  have h5 := Finset.sum_range_succ (fun i => (φ ^ i * m (t 0 ^ j)) x) n
  rw [Finset.sum_range_succ', h4, add_left_inj] at h5
  rw [LinearMap.sum_apply, map_sum, ← h5]
  conv_rhs => rw [h5, ← h5]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ', mul_assoc, End.mul_apply φ]
private theorem exists_orbit (l : ℕ) [hl : Fact l.Prime] (n : ℕ) (hn : 2 ≤ n) :
    ∃ c : ↥(MaximalUnramifiedExtension l), (frobUr l ^ n) c = c ∧
      ∀ i j : Fin n, (frobUr l ^ (i : ℕ)) c = (frobUr l ^ (j : ℕ)) c → i = j := by
  have h2 := hl.out.two_le
  have hlt : ∀ i, i < n → l ^ i < l ^ n - 1 := by
    intro i hi
    obtain ⟨r, rfl⟩ : ∃ r, n = r + 1 := ⟨n - 1, by omega⟩
    have h3 : l ^ i ≤ l ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : 1 < l ^ r := Nat.one_lt_pow (by omega) (by omega)
    have h5 : l ^ r * 2 ≤ l ^ r * l := Nat.mul_le_mul_left _ h2
    rw [pow_succ]; omega
  have h0 : 0 < l ^ n - 1 := lt_of_le_of_lt (Nat.zero_le _) (hlt 0 (by omega))
  have hd : ¬ l ∣ l ^ n - 1 := fun h => hl.out.one_lt.ne' (Nat.dvd_one.mp
    ((Nat.dvd_sub_iff_right (by omega) (dvd_pow_self l (by omega))).mp h))
  haveI : NeZero (l ^ n - 1) := ⟨h0.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ n - 1)
  have hmem : z ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨_, h0, hd, hz.pow_eq_one⟩
  have h1 : (⟨z, hmem⟩ : ↥(MaximalUnramifiedExtension l)) ^ (l ^ n - 1) = 1 := Subtype.ext hz.pow_eq_one
  refine ⟨⟨z, hmem⟩, ?_, fun i j hij => ?_⟩
  · rw [frobUr_pow_root _ _ _ h0 hd h1, show l ^ n = (l ^ n - 1) + 1 by omega, pow_succ, h1, one_mul]
  · rw [frobUr_pow_root _ _ _ h0 hd h1, frobUr_pow_root _ _ _ h0 hd h1] at hij
    have h6 : z ^ l ^ (i : ℕ) = z ^ l ^ (j : ℕ) := congrArg Subtype.val hij
    exact Fin.ext (Nat.pow_right_injective h2 (hz.pow_inj (hlt _ i.2) (hlt _ j.2) h6))
private theorem zpow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (y : D)
    (hy : (u : End k D) y = y) (n : ℤ) : ((u ^ n : (End k D)ˣ) : End k D) y = y :=
  (GlobalTheory.PstLaws.vecStab (Units.coeHom (End k D)) y).zpow_mem hy n
private theorem pow_fix {k D : Type} [Field k] [AddCommGroup D] [Module k D] (u : (End k D)ˣ) (a : End k D) (y : D)
    (n : ℕ) (hc : Commute a ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) (ha : a y = y)
    (hy : (a * ((u ^ (n : ℤ) : (End k D)ˣ) : End k D)) y = y) : ((u : End k D) ^ n) y = y := by
  rwa [hc.eq, End.mul_apply, ha, zpow_natCast, Units.val_pow_eq_pow_val] at hy
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O]
  [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
  (P : LocPrime l) {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
private theorem exists_stab {K : FinExt l} (ρ : Representation LL ↥(GK K) V) (y : ↥(Dpst P ρ)) :
    ∃ K' : FinExt l, ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → g ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) y := by
  obtain ⟨K', hK'⟩ := (mem_Dpst P ρ).mp y.2
  exact ⟨K', fun g hg => Subtype.ext (hK' g hg)⟩
private theorem deg_frob_inv_pow (s : ℕ) : deg ((frob h)⁻¹ ^ s) = -(s : ℤ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h1 := deg_mul ((frob h)⁻¹ ^ (s + 1)) (frob h)
    rw [pow_succ, inv_mul_cancel_right, ih, deg_frob] at h1
    rw [pow_succ]; push_cast; omega
variable (ρ : Representation LL ↥(GK Bw.Kw) V)
private theorem fix_of_weil (z : ↥(Dpst P ρ)) (hz : ∀ σ, actD P ρ (weilToGK Bw h σ) z = z)
    (g : ↥(GK Bw.Kw)) : actD P ρ g z = z := by
  obtain ⟨K', hK'⟩ := exists_stab P ρ z
  haveI := K'.2
  let S := (GlobalTheory.PstLaws.vecStab (actD P ρ) z).comap Bw.e.toMonoidHom
  have hS : IsOpen (S : Set ↥(Dec (F := F) A)) := by
    refine Subgroup.isOpen_mono (H₁ := ((GK K').subgroupOf (GK Bw.Kw)).comap Bw.e.toMonoidHom)
      (fun τ hτ => hK' _ hτ) ?_
    exact (IntermediateField.fixingSubgroup_isOpen K'.1).preimage (continuous_subtype_val.comp Bw.e_cont)
  have hd := UpperTheory.weil_group_dense_in_galois_group F Ω w A h
  obtain ⟨τ, rfl⟩ := Bw.e.surjective g
  exact hd.induction_on (p := fun τ => τ ∈ S) τ (S.isClosed_of_isOpen hS) hz
variable [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)]
include hj in
private theorem exists_period (x : ↥(Dpst P ρ)) (hx : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ n : ℕ, 2 ≤ n ∧ (phiD P ρ ^ n) x = x := by
  have hf : resDeg l w ≠ 0 := by
    intro h0
    have hq1 := GlobalTheory.WeilDeligne.one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at hq1
    exact lt_irrefl _ hq1
  obtain ⟨K', hK'⟩ := exists_stab P ρ x
  haveI := GlobalTheory.PstLaws.finite_quotient K' _ hK'
  haveI : (GlobalTheory.PstLaws.vecStab (actD P ρ) x).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨r, hr0, -, hr⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := GlobalTheory.PstLaws.vecStab (actD P ρ) x)) (weilToGK Bw h (frob h)⁻¹)
  have hr2 : weilToGK Bw h ((frob h)⁻¹ ^ (r * 2)) ∈ GlobalTheory.PstLaws.vecStab (actD P ρ) x := by
    rw [map_pow (weilToGK Bw h), pow_mul]
    exact (GlobalTheory.PstLaws.vecStab (actD P ρ) x).pow_mem hr 2
  have h2 := hx ((frob h)⁻¹ ^ (r * 2))
  have e : -alpha l ((frob h)⁻¹ ^ (r * 2)) = ((resDeg l w * (r * 2) : ℕ) : ℤ) := by
    rw [alpha, deg_frob_inv_pow]; push_cast; ring
  rw [weilD_apply, e] at h2
  refine ⟨_, ?_, pow_fix (phiU P ρ) _ x _ (commute_actD_phiU P ρ _ _) hr2 h2⟩
  have : 0 < resDeg l w * r := Nat.mul_pos (Nat.pos_of_ne_zero hf) hr0
  rw [← mul_assoc]; omega
include hj in
private theorem phiMain (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (hW : ∀ σ, weilD Bw h P ρ σ x = x) :
    ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  obtain ⟨n, hn, hp⟩ := exists_period h Bw hj P ρ x hW
  obtain ⟨c, hc1, hc2⟩ := exists_orbit l n hn
  obtain ⟨j, hz0, hz1⟩ := exists_trace (mulD P ρ) (phiD P ρ) n (by omega) (fun i => (frobUr l ^ i) c) hc2
    (by simpa using hc1) (fun i j => by rw [phiD_pow_mulD, pow_zero, AlgHom.one_apply, map_pow]) x hx0 hp
  refine ⟨_, hz0, hz1, fix_of_weil h Bw P ρ _ fun σ => ?_⟩
  refine (congrArg (actD P ρ (weilToGK Bw h σ)) (zpow_fix (phiU P ρ) _ hz1 (-alpha l σ))).symm.trans ?_
  have hcm : Commute (weilD Bw h P ρ σ) (∑ i ∈ Finset.range n, phiD P ρ ^ i *
      mulD P ρ ((frobUr l ^ 0) c ^ j)) := by
    refine Commute.sum_right _ _ _ fun i _ => Commute.mul_right (Commute.pow_right ?_ i)
      (weilD_mulD Bw h P ρ hj _ _)
    rw [weilD_apply]
    exact (Commute.mul_right (phiD_actD P ρ _)
      (Commute.units_zpow_right (u := phiU P ρ) (Commute.refl _) _)).symm
  exact (LinearMap.congr_fun hcm.eq x).trans (congrArg _ (hW σ))
end
private theorem ordPhiU :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (_hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)], (∃ x : ↥(Dpst P ρ), x ≠ 0 ∧ ∀ σ, weilD Bw h P ρ σ x = x) → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ GlobalTheory.Pst.phiD P ρ z = z ∧ ∀ g, GlobalTheory.Pst.actD P ρ g z = z := by
  intro F Ω _ _ _ _ _ l hl A w h O _ _ _ Bw hj P L V _ _ _ _ _ ρ _ ⟨x, hx0, hW⟩
  exact phiMain h Bw hj P ρ x hx0 hW
end Phi
section Priv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section SlopeTestRemainingChoices
open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
private theorem ine_normal (σ : ↥(Weil h)) (s : ↥(Ine (F := F) A)) : ∃ t, σ * ineIncl h s = ineIncl h t * σ := by
  have : deg (σ * ineIncl h s * σ⁻¹) = 0 := by simp
  refine ⟨⟨_, deg_eq_zero_iff.1 this⟩, ?_⟩
  have e : ineIncl h ⟨_, deg_eq_zero_iff.1 this⟩ = σ * ineIncl h s * σ⁻¹ := rfl
  rw [e, inv_mul_cancel_right]
private theorem core0 {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type}
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) {n : ℕ} (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → μ j ≠ μ k ∧ μ j ≠ μ k * unrChar h (qPow w 1))
    (hP : ∀ σ, (wdPst P ι Bw h hj ρ).charPol σ = ∏ j, (X - C (μ j σ : ℂ))) :
    wdN P ι ρ = 0 ∧ ∀ j, μ j = 1 → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  haveI := hV.finite
  have hc : ∀ σ, (wdRho P ι Bw h hj ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ)) :=
    fun σ => (DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ).symm.trans (hP σ)
  have hL := UpperTheory.exists_common_eigenvector_of_charpoly_split_characters (ineIncl h) (frob h) (wdRho P ι Bw h hj ρ) μ (ine_normal h)
    (fun σ => ⟨deg σ, exists_eq_zpow_mul deg_frob σ⟩) (isSmooth_wdRho P ι Bw h hj ρ).finite_range hc
  have hq : ((qPow w 1 : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) := by simp
  have hdim : finrank ℂ (WDSpace P ι ρ) = n := by
    rw [← LinearMap.charpoly_natDegree (wdRho P ι Bw h hj ρ 1), hc, natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C _]
    simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  refine ⟨UpperTheory.eq_zero_of_twisted_commute_of_distinct_characters (wdRho P ι Bw h hj ρ) μ (unrChar h (qPow w 1)) _ hdim hL
    (fun j k e => by_contra fun hjk => (hμ j k hjk).1 e) (fun j k e => ?_) fun σ => ?_, fun j hj1 => ?_⟩
  · by_cases hjk : j = k
    · subst hjk
      have h1 := congrArg (fun x : ℂˣ => (x : ℂ)) (left_eq_mul.1 (DFunLike.congr_fun e (frob h)))
      simp only [unrChar_apply, deg_frob, zpow_one, hq, Units.val_one, Nat.cast_eq_one] at h1
      exact (one_lt_normV w).ne' h1
    · exact (hμ j k hjk).2 e
  · rw [unrChar_apply, Units.val_zpow_eq_zpow_val, hq]
    exact wdRho_wdN P ι Bw h hj ρ σ
  have h1 := hL j
  simp only [hj1, MonoidHom.one_apply, Units.val_one, one_smul] at h1
  exact ordPhiU h Bw hj P ρ (UpperTheory.exists_weil_invariant_in_Dpst_of_weilDeligne_invariant ι h Bw hj P ρ h1)
private theorem core (hB : DeRhamPotSemistable) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l))
    (hr : Continuous r) (HT : (F →+* Qbar l) → Multiset ℤ) (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → μ j ≠ μ k ∧ μ j ≠ μ k * unrChar h (qPow w 1))
    (hD : DRat ι h r HT fun s => ∏ j, (X - C (μ j s : ℂ)))
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) :
    IsPotCrysAt (UpperTheory.V.Loc.PP l) Bw r ∧ ∀ j, μ j = 1 → (∀ τ, ∀ c ∈ HT τ, 0 ≤ c) →
      ∃ v : Fin n → Qbar l, v ≠ 0 ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) (Qbar l)) *ᵥ v = v := by
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨hd, hJ, hP⟩ := hD O Bw hj
  have hp := hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
  obtain ⟨L, r', hm, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hp
  obtain ⟨hN0, hz⟩ := core0 ι h Bw hj (UpperTheory.V.Loc.PP l) (Bw.repE L r') hV μ hμ fun σ =>
    (congrArg (fun x => WD.charPol x σ) e).symm.trans (hP σ)
  refine ⟨(GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj _ ι r hp).1 ?_, fun j hj1 hHT => ?_⟩
  · rw [e]
    exact (mono0_wdPst ι Bw h hj hV).2 hN0
  obtain ⟨z, z0, z1, z2⟩ := hz j hj1
  have hd' := (hm.isdRAt_iff _).1 hd
  have hM := (GlobalTheory.PstLaws.wdN_eq_zero_iff (UpperTheory.V.Loc.PP l) (Bw.repE L r') ι).1 hN0
  have hmult : ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → Bw.multE (UpperTheory.V.Loc.PP l) L r' τ' c = 0 := by
    intro τ' c hc0
    let τ : F →+* Qbar l := ((algebraMap ↥L.1 (Om l)).comp τ'.toRingHom).comp
      ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E)
    have hτ : IsInduced Bw τ τ' := fun _ => rfl
    have := IsJumpsAt.count_eq _ hm hτ (hJ τ L τ' hτ) c
    rw [Multiset.count_eq_zero.2 fun hc' => absurd (hHT τ c hc') (not_le.2 hc0)] at this
    exact this.symm
  obtain ⟨v, v0, hv⟩ := UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights (fun τ x => hm.1 (Bw.LL_split τ x)) (Bw.repE L r')
    (finiteDimensional_DdR _ _ hd') hmult z z0 (LinearMap.congr_fun hM z) z1 z2
  refine ⟨fun i => (v i : Om l), fun h0 => v0 (funext fun i => Subtype.ext (congrFun h0 i)), fun g => ?_⟩
  have h5 : (r' g : Matrix (Fin n) (Fin n) ↥L.1) *ᵥ v = v := by
    have := hv (Bw.e g)
    rw [← Bw.e.symm_apply_apply g]
    exact this
  funext i
  have h6 := congrArg (algebraMap ↥L.1 (Om l)) (congrFun h5 i)
  rw [RingHom.map_mulVec] at h6
  rw [← hm.2]
  exact h6
omit [IsAlgClosure F Ω] in
private theorem ordChar_inv {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} {ω : (w.adicCompletion F)ˣ →* ℂˣ}
    {hh : (F →+* Qbar l) → ℤ} {ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} (H : OrdChar ι a ω hh ψ) :
    OrdChar ι a ω⁻¹ (-hh) ψ⁻¹ where
  smooth := by
    have := H.smooth
    unfold GlobalTheory.SmGL.IsSmoothChar at this ⊢
    convert this using 1
    ext x
    simp
  cont := H.cont.inv
  val := fun s g hg hs => by
    have := H.val s g hg hs
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at this ⊢
    rw [this, mul_inv, map_inv₀]
    congr 1
    unfold algPow
    rw [← finprod_inv_distrib]
    simp
end SlopeTestRemainingChoices
section Main
open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
private noncomputable def twR {H k : Type} [Group H] [Field k] {n : ℕ} (μ : H →* kˣ) (r : H →* GL (Fin n) k) : H →* GL (Fin n) k where
  toFun g := ⟨(μ g : k) • (r g : Matrix (Fin n) (Fin n) k), (μ g⁻¹ : k) • (r g⁻¹ : Matrix (Fin n) (Fin n) k),
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp,
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g g' := Units.ext (by simp [smul_smul, mul_comm])
private theorem twR_cont {H k : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} {μ : H →* kˣ} {r : H →* GL (Fin n) k}
    (hμ : Continuous μ) (hr : Continuous r) : Continuous (twR μ r) :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr),
    ((Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)).comp continuous_inv⟩
private theorem good_comp {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) {n : ℕ}
    {ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ}
    (hne : ∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) 1) :
    ∀ j k, j ≠ k → (ω j).comp a ≠ (ω k).comp a ∧ (ω j).comp a ≠ (ω k).comp a * unrChar h (qPow w 1) := by
  intro j k hjk
  refine ⟨fun e => (hne j k hjk).1 ((MonoidHom.cancel_right ha.surj).1 e), fun e => (hne j k hjk).2
    ((MonoidHom.cancel_right ha.surj).1 ?_)⟩
  rw [e, MonoidHom.mul_comp, ← ha.absPow_comp, Complex.ofReal_one]
private theorem flag (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
    {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (n : ℕ) :
    ∀ (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (hh : Fin n → (F →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) →
    ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) →
      (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) 1) →
      DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) →
      HasFlag r ψ := by
  have hB := hL.aut.berger
  induction n with
  | zero => exact fun r _ _ _ _ _ _ _ _ => ⟨1, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro r hr hh hmono ω ψ hO hne hD
    have hO' := ordChar_inv ι h (hO 0)
    have hc := twR_cont hO'.cont hr
    have h1 := UpperTheory.deRham_rational_twist_by_character hB ι h r (twR (ψ 0)⁻¹ r) (ψ 0)⁻¹ hr hc hO'.cont (fun _ => rfl) _ _ _ _ hD
      (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ hO').1
    obtain ⟨LL, Bw, hj⟩ := GlobalTheory.Pst.Test.exists_induces (l := l) (E := F) (Ω := Ω) hw h
    obtain ⟨v, v0, hv⟩ := (core ι h hB _ hc _ (fun j => (ω j * (ω 0)⁻¹).comp a)
      (good_comp h ha fun j k hjk => ⟨fun e => (hne j k hjk).1 (mul_right_cancel e),
        fun e => (hne j k hjk).2 (mul_right_cancel (e.trans (mul_right_comm _ _ _)))⟩)
      (by simpa only [MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul] using h1) Bw hj).2 0
      (by rw [mul_inv_cancel]; rfl) (fun τ c hc => by
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Pi.neg_apply] at hc
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hc
        have := (hmono τ).monotone (Fin.zero_le j)
        omega)
    have hv' : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) *ᵥ v = (ψ 0 g : Qbar l) • v := fun g => by
      have := hv g
      change ((((ψ 0 g)⁻¹ : (Qbar l)ˣ) : Qbar l) • (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l))) *ᵥ v = v at this
      rw [Matrix.smul_mulVec] at this
      rw [← congrArg (fun x => (ψ 0 g : Qbar l) • x) this, smul_smul, Units.mul_inv, one_smul]
    obtain ⟨p, r₁, r', e₁, c₁, c', b1, b2, b3, hfl⟩ := UpperTheory.exists_common_eigenline r ψ v hr v0 hv'
    have h2 := UpperTheory.deRhamRational_of_conj hB ι h r r₁ p hr e₁ _ _ hD
    refine hfl (ih r' c' (fun j => hh j.succ) (fun τ => (hmono τ).comp Fin.strictMono_succ) (fun j => ω j.succ) _
      (fun j => hO j.succ) (fun i j hij => hne _ _ fun e => hij (Fin.succ_injective _ e)) ?_)
    refine UpperTheory.deRham_rational_of_extension_by_character hB ι h r₁ r' (ψ 0) c₁ b1 b2 b3 (hh 0) _ _ _ ?_
      (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ (hO 0)).1
    convert h2 using 2
    · rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ, Multiset.cons_coe]
    · rw [Fin.prod_univ_succ]
end Main
end Priv
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Loc.ordFlagU_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 L)), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := L) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (hh : Fin n → (L →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) → ∀ (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ), (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) → (∀ i j, i ≠ j → ω i ≠ ω j ∧ ω i ≠ ω j * absPow (w.adicCompletion L) 1) → DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → W.HasFlag r ψ ∧ PotCrys A r := by
  intro hL F Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh hmono ω ψ hO hne hD
  exact ⟨flag ι h hL hw ha n r hr hh hmono ω ψ hO hne hD, fun O _ _ _ Bw hj =>
    (core ι h hL.aut.berger r hr _ (fun j => (ω j).comp a) (good_comp h ha hne) hD Bw hj).1⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem norm_q {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : ((normV w : ℕ) : Qbar l) ≠ 0 ∧ ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  refine ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd : l ∣ normV w := by
    rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec] at hw
    have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
    rw [(Nat.prime_dvd_prime_iff_eq hq Fact.out).1 hw]
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact_mod_cast Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)
private theorem abs_art {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (c : ℤ) (s : Weil h) :
    (GlobalTheory.SmGL.absPow (w.adicCompletion F) (c : ℂ) (a s) : ℂ) = ((normV w : ℕ) : ℂ) ^ (c * deg s) := by
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV, Complex.cpow_intCast,
    mul_comm, zpow_mul]
  push_cast
  rfl
private theorem cont_smooth {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] {B : Type} [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (f : X →* B) (hf : IsOpen (f.ker : Set X)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : B))).congr ?_
  filter_upwards [hf.mem_nhds f.ker.one_mem] with x hx
  exact (MonoidHom.mem_ker.1 hx).symm
theorem UpperTheory.deRham_weights_of_localArtin_characters' :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := F) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (m : Fin n → ℤ), (∀ i j, i < j → m j + 2 ≤ m i) → ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ), (∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j)) → (∀ j (s : Weil h), ‖ι.symm (ω j (a s) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m j * deg s)) → Hi.DRat ι h r (fun _ => Finset.univ.val.map fun j => -m j) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → ∃ κ : Fin n → Dec (F := F) A →* (Qbar l)ˣ, W.HasFlag r κ ∧ ∀ j (s : Weil h), (κ j (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) = ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
  intro N F Ω _ _ _ _ _ l _ hl ι n w hw A h a ha r hr m hm ω hω hn hD
  obtain ⟨q0, q1⟩ := norm_q w hw
  have q2 : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 q0
  have hcyc : Continuous (cycBar F Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)
  have key : ∀ j, ∃ κ : Dec (F := F) A →* (Qbar l)ˣ, Continuous κ ∧ ∀ s : Weil h,
      (κ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) =
        ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
    intro j
    let φ := ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ)
    have hφ : GlobalTheory.SmGL.IsSmoothChar φ :=
      (hω j).mul (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _))
    let ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ := (Units.map ι.symm.toRingHom.toMonoidHom).comp φ
    have hξ : ∀ s, (ξ (a s) : Qbar l) = ι.symm (ω j (a s) : ℂ) * ((normV w : ℕ) : Qbar l) ^ (-m j * deg s) := by
      intro s
      show ι.symm ((ω j (a s) : ℂ) * (GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ) (a s) : ℂ)) = _
      rw [abs_art ha, map_mul, map_zpow₀, map_natCast]
    have hc : Continuous ξ := by
      refine cont_smooth ξ (Subgroup.isOpen_mono (fun x hx => ?_) hφ)
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]
    obtain ⟨κ, ⟨c1, c2⟩, -⟩ := UpperTheory.V.Loc.laExists N.aut.art h a ha ξ hc fun x => by
      obtain ⟨s, rfl⟩ := ha.surj x
      rw [hξ, norm_mul, hn, norm_zpow, ← zpow_add₀ q2.ne', neg_mul, add_neg_cancel, zpow_zero]
    refine ⟨κ * ((cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m j,
      c1.mul ((continuous_zpow (m j)).comp (hcyc.comp continuous_subtype_val)), fun s => ?_⟩
    show ((κ (Subgroup.inclusion (Weil_le_Dec h) s) * cycBar F Ω l (s : G F Ω) ^ m j : (Qbar l)ˣ) : Qbar l) * _ = _
    rw [c2, Units.val_mul, hξ, Units.val_zpow_eq_zpow_val, neg_mul, zpow_neg, mul_right_comm,
      inv_mul_cancel_right₀ (zpow_ne_zero _ q0)]
  choose κ hκ hv using key
  refine ⟨κ, (_root_.UpperTheory.V.Loc.ordFlagU_alt N F Ω l hl ι n w hw A h a ha r hr (fun j _ => -m j)
    (fun _ i j hij => ?_) ω κ (fun j => ⟨hω j, hκ j, fun s g hg _ => ?_⟩) (fun i j hij => ?_) hD).1, hv⟩
  · have := hm i j hij
    show -m i < -m j
    omega
  · obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
    have h1 := hv j s
    rw [UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s, mul_zpow, ← zpow_mul, mul_comm (deg s), mul_comm (_ ^ _),
      ← mul_assoc] at h1
    refine (mul_right_cancel₀ (zpow_ne_zero _ q0) h1).trans ?_
    congr 1
    haveI := finite_contEmb (l := l) w
    letI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    simp
  · have hi := hn i (frob h)
    have hj := hn j (frob h)
    rw [deg_frob, mul_one] at hi hj
    have hij' : m i ≠ m j ∧ m i ≠ m j + 1 := by
      rcases lt_or_gt_of_ne hij with h1 | h1
      · have := hm _ _ h1; omega
      · have := hm _ _ h1; omega
    refine ⟨fun e => hij'.1 ?_, fun e => hij'.2 ?_⟩
    · rw [e, hj] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
    · have h1 := abs_art ha 1 (frob h)
      rw [deg_frob, mul_one, zpow_one, Int.cast_one] at h1
      rw [e, MonoidHom.mul_apply, Units.val_mul, h1, map_mul, map_natCast, norm_mul, hj, ← zpow_add_one₀ q2.ne'] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private UpperTheory.V.Sd.OrdinaryAbove.unr_val UpperTheory.V.Sd.OrdinaryAbove.abs_val UpperTheory.V.Sd.OrdinaryAbove.det_flag from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAbove
open private embAt_of_induced from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.LocalGlobalCompatibilityGl2
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.RR.ordAbove_of_alt (hX : ExRS) (hGd : GdOf) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdAbove := by
  intro hP F Ω _ _ _ _ _ _ l _ hl _ ι ξ s c m a π r H w hw A h
  obtain ⟨-, hm, hs, ha, ⟨lam, hU, hlam⟩, hinf⟩ := H.above w hw
  obtain ⟨χ₀, hpol⟩ := H.pol
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results hP.toClassicalTheorems F 2 π w
  have hiso := hiso σ hσ
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  obtain ⟨ar, har, ε, hLV⟩ := toV' hrc
  have hq0 : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_normV w).ne_bot
  have hqc : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (one_lt_normV w).ne_bot
  have hqn : ‖((normV w : ℕ) : Qbar l)‖ ≠ 0 := norm_ne_zero_iff.2 hq0
  have hn : ‖ι.symm lam * (normV w : Qbar l) ^ m w 0‖ = 1 := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := ι.symm lam * (normV w : Qbar l) ^ m w 0 - a w) (y := a w)
      (by rw [ha]; exact hlam.ne)
    rwa [sub_add_cancel, ha, max_eq_right hlam.le] at this
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hn
  have hn' : ‖ι.symm lam‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (-m w 0) := by
    rw [norm_mul, norm_zpow] at hn
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_left hn
  obtain ⟨μ₁, μ₂, Lf, hL0, hunr, hval, hLf⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt hP.toClassicalTheorems F w σ 1 (Units.mk0 lam hl0) one_ne_zero
    (UpperTheory.hasUEigenvalue_of_locIsotypic F w _ π.finPart σ hiso 1 lam hU)
  obtain ⟨s1, s2, hsub, hcen⟩ := UpperTheory.isSubquotient_principalSeries_of_borel_functional F w σ μ₁ μ₂ Lf hL0 hLf
  set ω : Fin 2 → (w.adicCompletion F)ˣ →* ℂˣ := ![μ₁ * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1), μ₂] with hω
  have hω0 : ∀ t : Weil h, (ω 0 (ar t) : ℂ) = lam ^ (-deg t) := fun t => by
    change ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) = _
    rw [Units.val_mul, UpperTheory.V.Sd.OrdinaryAbove.abs_val, UpperTheory.V.Sd.OrdinaryAbove.unr_val w μ₁ hunr, har.ord_eq, Units.val_zpow_eq_zpow_val, ← mul_zpow, mul_comm, hval]
    rfl
  have hsm : ∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j) := by
    refine Fin.forall_fin_two.2 ⟨?_, s2⟩
    exact Subgroup.isOpen_mono (H₁ := μ₁.ker ⊓ (GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1)).ker)
      (fun x hx => by
        change μ₁ x * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) x = 1
        rw [hx.1, hx.2, mul_one])
      (IsOpen.inter s1 (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _)))
  have hn0 : ∀ t : Weil h, ‖ι.symm (ω 0 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 0 * deg t) := fun t => by
    rw [hω0, map_zpow₀, norm_zpow, hn', ← zpow_mul, neg_mul_neg]
  have hn1 : ∀ t : Weil h, ‖ι.symm (ω 1 (ar t) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m w 1 * deg t) := fun t => by
    have h1 := _root_.UpperTheory.V.Sd.OrdinaryAbove.central_weil_ordinary_above hP H hw h har hiso t _ (hcen (ar t))
    have h2 : ((μ₁ (ar t) * μ₂ (ar t) : ℂˣ) : ℂ) = (ω 0 (ar t) : ℂ) * (ω 1 (ar t) : ℂ) * ((normV w : ℕ) : ℂ) ^ deg t := by
      change _ = ((μ₁ (ar t) * GlobalTheory.SmGL.absPow (w.adicCompletion F) (-1) (ar t) : ℂˣ) : ℂ) * (μ₂ (ar t) : ℂ) * _
      rw [Units.val_mul, Units.val_mul, UpperTheory.V.Sd.OrdinaryAbove.abs_val, har.ord_eq, zpow_neg]
      field_simp
    rw [h2, map_mul, map_mul, norm_mul, norm_mul, hn0, map_zpow₀, map_natCast, norm_zpow, ← hs,
      show (m w 0 + m w 1 + 1) * deg t = m w 0 * deg t + m w 1 * deg t + deg t by ring, zpow_add₀ hqn, zpow_add₀ hqn] at h1
    exact mul_left_cancel₀ (zpow_ne_zero _ hqn) (mul_right_cancel₀ (zpow_ne_zero _ hqn) h1)
  have hcp := RR.ps_alg hLV σ ω hsm hsub
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX F Ω l ι 2 one_le_two π χ₀ H.reg hpol
  have hG := hall r H.cont H.att
  have hpl := (Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
  have hdr : Hi.DRat ι h (r.comp (Dec (F := F) A).subtype) (fun _ => Finset.univ.val.map fun j => -m w j)
      fun s => (rc (algNorm σ)).charPol s := by
    intro O _ _ _ Bw hj
    obtain ⟨k1, k2⟩ := hG.loc w σ hσ hpl
    obtain ⟨h1, h2⟩ := k2 A h O Bw hj
    refine ⟨h1, fun τ LL' τ' hτ => ?_, fun s => ?_⟩
    · have e : HT τ = Finset.univ.val.map fun j => -m w j := by
        refine Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective ?_
        have := hG.weights τ _ (hinf τ (embAt_of_induced h Bw hj τ LL' τ' hτ))
        simp only [this, infOf, Multiset.map_map]
        exact Multiset.map_congr rfl fun i _ => by simp
      exact e ▸ h2 τ LL' τ' hτ
    · rw [((k1 A h rc hrc).2 O Bw hj (hGd F Ω A w h rc hrc 2 σ hpl)).2]
  rw [funext hcp] at hdr
  obtain ⟨κ, hκ, hv⟩ := _root_.UpperTheory.deRham_weights_of_localArtin_characters' hP.litN F Ω l hl ι 2 w hw A h ar har _ (H.cont.comp continuous_subtype_val) (m w)
    (fun i j hij => by fin_cases i <;> fin_cases j <;> first | exact hm | exact absurd hij (by decide)) ω hsm
    (Fin.forall_fin_two.2 ⟨hn0, hn1⟩) hdr
  have k0 : ∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A → κ 0 g = cycBar F Ω l g ^ m w 0 := fun g hg => by
    have h1 := hv 0 (ineIncl h ⟨g, hg⟩)
    rw [hω0, deg_ineIncl, mul_zero, zpow_zero, neg_zero, zpow_zero, map_one, mul_one, one_mul] at h1
    exact Units.ext (h1.trans (Units.val_zpow_eq_zpow_val _ _).symm)
  refine ⟨κ, hκ, Fin.forall_fin_two.2 ⟨k0, fun g hg => ?_⟩, fun g hg => ?_⟩
  · have h1 := UpperTheory.V.Sd.OrdinaryAbove.det_flag _ κ hκ g
    have h2 : Matrix.GeneralLinearGroup.det (r g) = cycBar F Ω l g ^ s * ξ g := DFunLike.congr_fun H.det (g : G F Ω)
    have h3 : ξ g = 1 := (H.ram w A h).2 (Or.inr hw) hg
    rw [h3, mul_one, ← hs, _root_.zpow_add] at h2
    rw [k0 g hg] at h1
    exact mul_left_cancel (h1.symm.trans h2)
  · let t : Weil h := ⟨g, mem_Weil_of_isFrob h hg⟩
    have hd : deg t = 1 := deg_eq_one_iff.2 hg
    have h1 := hv 0 t⁻¹
    rw [hω0, deg_inv, hd, neg_neg, zpow_one, mul_neg_one, zpow_neg] at h1
    have h2 : (κ 0 g⁻¹ : Qbar l) * ((normV w : Qbar l) ^ m w 0)⁻¹ = ι.symm lam * (cycBar F Ω l (g : G F Ω)⁻¹ : Qbar l) ^ m w 0 := h1
    have h3 : ((κ 0 g⁻¹ * cycBar F Ω l (g : G F Ω) ^ m w 0 : (Qbar l)ˣ) : Qbar l) = ι.symm lam * (normV w : Qbar l) ^ m w 0 := by
      rw [mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ hq0), map_inv (cycBar F Ω l), Units.val_inv_eq_inv_val (cycBar F Ω l _), inv_zpow] at h2
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, h2, mul_right_comm _ _ (_ ^ _), inv_mul_cancel_right₀ (zpow_ne_zero _ (Units.ne_zero _))]
    rw [h3]
    exact hlam
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private UpperTheory.V.Sd.OrdinaryAwayPlaces.rep_retr UpperTheory.V.Sd.OrdinaryAwayPlaces.map_dc UpperTheory.V.Sd.OrdinaryAwayPlaces.exists_ps UpperTheory.V.Sd.OrdinaryAwayPlaces.charPol_lpTw UpperTheory.V.Sd.OrdinaryAwayPlaces.diag_of_wd UpperTheory.V.Sd.OrdinaryAwayPlaces.iwahori_level_zero_eq from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.OrdAway
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Hi
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Win.RR.ordAway_of_alt (hX : ExRS) (hGd : GdOf) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.OrdAway := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H A hA
  have P := PH.toClassicalTheorems
  obtain ⟨p1, p2, p3, p4⟩ := UpperTheory.V.Base.places F Ω l A
  have triv : (∀ g ∈ Ine (F := F) A, r g = 1) → Ine (F := F) A ≤ ξ.ker → IsDiagOn r (Ine (F := F) A) ![1, ξ] :=
    fun h1 h2 => ⟨1, fun g hg => by
      have h3 : ξ g = 1 := h2 hg
      rw [h1 g hg]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h3]⟩
  by_cases hT : A = ⊤
  · rw [(p2 hT).1] at triv ⊢
    exact triv (fun g hg => by rw [Subgroup.mem_bot.1 hg, map_one]) bot_le
  obtain ⟨w, h⟩ := p1 hT
  have hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal := fun e => hA ((p3 w h).2 e)
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F 2 π w
  by_cases hc : c w = 0
  · obtain ⟨v, hv, hf⟩ := H.sph w hc
    obtain ⟨T, hT, hTv⟩ := UpperTheory.V.Sd.OrdinaryAwayPlaces.rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
    obtain ⟨B, hB⟩ := (_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).1 ⟨T v, hTv, fun u hu => by rw [← hT, hf u (UpperTheory.V.Sd.OrdinaryAwayPlaces.iwahori_level_zero_eq w ▸ hu)]⟩
    have hB' : π.HasSat w B := ((_root_.UpperTheory.V.Af.satake_local_of_printed_results P F 2 w σ).2 _ π.finPart (hiso σ hσ) B).2 hB
    exact triv (hG.frob w hl B hB' A h).1
      ((H.ram w A h).2 (Or.inl hc))
  obtain ⟨lam, ⟨v, hv, hf, hU⟩, hlam⟩ := H.away w hc hl
  have hl0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  obtain ⟨T, hT, hTv⟩ := UpperTheory.V.Sd.OrdinaryAwayPlaces.rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, -, hlaw⟩ := _root_.UpperTheory.V.Sd.jacqOfU_alt P F w σ (c w) (Units.mk0 lam hl0) hc
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← UpperTheory.V.Sd.OrdinaryAwayPlaces.map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hU, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := UpperTheory.V.Sd.OrdinaryAwayPlaces.exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := recTExists F Ω A w h
  have hpl := (Birth.ordPlain F Ω l ι ξ s c m a π r H w σ hσ).elim id fun ⟨B, hB⟩ => hG.plain w B hB σ hσ
  have hx := (((hG.loc w σ hσ hpl).1 A h rc hrc).1 hl).isWDOf (hGd F Ω A w h rc hrc 2 σ hpl)
  refine UpperTheory.V.Sd.OrdinaryAwayPlaces.diag_of_wd hl ι r ξ hx (fun g => ?_) (fun g hg => ?_)
    fun e => ((H.ram w A h).1 e).elim hc hl
  · obtain ⟨b, hb, ε, hL⟩ := toV' hrc
    obtain ⟨e1, e2⟩ := RR.ps_cls hL σ ψ hψ hs
    rw [e1, UpperTheory.V.Sd.OrdinaryAwayPlaces.charPol_lpTw]
    have h1 := e2 (ineIncl h g)
    have h2 : valuation (w.adicCompletion F) (b (ineIncl h g) : w.adicCompletion F) = 1 :=
      ord_eq_zero_iff.1 (by rw [hb.ord_eq, deg_ineIncl, neg_zero])
    have : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    rw [Fin.prod_univ_two, hψ0 _ h2, hμ _ ((isEquiv (valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1 h2)] at h1
    exact ⟨_, h1⟩
  · have h1 := DFunLike.congr_fun H.det g
    have h2 : cycZ F Ω l g = 1 := p4 hA hg
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.zpow_apply, cycBar, h2, map_one, one_zpow,
      one_mul] at h1
    exact congrArg Units.val h1
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT UpperTheory.V.Z.Bc
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]
private theorem upCycI (hP : _root_.UpperTheory.V.Af.Hypotheses') (hL : CyclicBaseChangeLiftRankTwo) (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E]
    [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    [IsGalois F E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hp : (Module.finrank F E).Prime) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (π : CuspSub F 2) (hr : Continuous r) (hreg : (CG.mk π).IsRegAlg) (hatt : AttC ι r π) (hirr : IsIrr (r.comp (galEmb F E Ω))) :
    ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  rcases hL F E hp π hreg with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results hP F Ω l ι 2 r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ 2 r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr, ?_⟩, hinf⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normV_under (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 2 r _ hF
      rw [← algSat_pow, ← normV_under] at h3
      exact h3
private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp
private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }
private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n) (hreg : (CG.mk π).IsRegAlg) (ha : AttC ι r π)
    (hi : IsIrr (r.comp (galEmb F E Ω))) : ∃ P : CuspSub E n, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  obtain ⟨-, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩, fun τ m hm => by
      have h := (UpperTheory.V.FieldIso.hasInfChar_pullSub j π _ m).2 hm
      rwa [show (τ.comp (algebraMap F E)).comp (j : E →+* F) = τ from RingHom.ext fun x => congrArg τ (j.symm_apply_apply x)] at h⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3
theorem UpperTheory.V.Z.Bc.upSolI_of_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → CyclicBaseChangeLiftRankTwo → UpSolI := by
  intro P hL F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing F with
  | _ d ih =>
  intro r π hc hreg ha hi
  by_cases h1 : Module.finrank F E = 1
  · exact up_one F E Ω h1 l ι 2 r π hreg ha hi
  haveI : Nontrivial (E ≃ₐ[F] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := F) (M := E)
    omega
  obtain ⟨M, hM, hp⟩ := exists_prime_index (E ≃ₐ[F] E)
  let K := IntermediateField.fixedField M
  haveI : IsGalois F K := IsGalois.of_fixedField_normal_subgroup M
  haveI : IsTotallyComplex K := isTotallyComplex_of_algebra F K
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := closure_tower K E Ω
  haveI : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom F) (AlgEquiv.restrictScalars_injective F)
  have hdeg : Module.finrank F K = M.index := by
    have h2 := Module.finrank_mul_finrank F K E
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F E, ← M.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hlt : Module.finrank K E < d := by
    rw [← hd, ← Module.finrank_mul_finrank F K E, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt
  have e : r.comp (galEmb F E Ω) = (r.comp (galEmb F K Ω)).comp (galEmb K E Ω) := rfl
  rw [e] at hi ⊢
  obtain ⟨Q, q1, q2, q3⟩ := upCycI P hL F K Ω l ι (hdeg ▸ hp) r π hc hreg ha ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hi)
  obtain ⟨Q', p1, p2, p3⟩ := ih _ hlt K rfl _ Q (hc.comp (resFacts F K Ω l 2 r).1) q1 q2 hi
  refine ⟨Q', p1, p2, fun τ m hm => p3 τ m (q3 _ m ?_)⟩
  rwa [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
theorem UpperTheory.V.Z.Bc.upQuadI_of_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') (h : QuadLiftRealToComplexRankTwo) : UpQuadI := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE r π hr hreg hatt hirr
  obtain ⟨P, hBC⟩ := (h F E hE π hreg).resolve_left fun ⟨η, hη, ht⟩ =>
    UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results hP) UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion F E Ω l ι hE 2 r π hr hatt hirr η hη ht
  have h1 := UpperTheory.V.Br.bcAtt0 F E Ω l ι 2 r π P hBC
  exact ⟨P, h1.1 hreg, h1.2 hatt ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr), hBC.inf⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV UpperTheory.V.Z.Win.RR
open scoped Matrix Pointwise
open private UpperTheory.V.Af.infOf_of_weights UpperTheory.V.Af.exists_over from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
open private UpperTheory.V.Af.NewformAutomorphy.ev_not_mem from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
open private UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.flag_stable UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.dual_det UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.ss_tw UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cyc_inf UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.charpoly_smul UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cont_cycBar from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharpolySmul
open private cc_ex kills_cc kills_pow pairing2 from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
open private UpperTheory.V.Z.Win.tw_tw_inv from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AIsoTwOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.RR
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
private theorem alg0 (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) (m : ℤ) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ m) := by
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  obtain ⟨k, hk, hpow⟩ := kills_pow hM hχ
  refine (_root_.UpperTheory.V.Af.algOfCyc_s P ℚ Ω l ι).1 _ ?_ fun w _ => ?_
  · have h1 : Continuous fun s => Matrix.GeneralLinearGroup.det (W s) * cycBar ℚ Ω l s ^ m :=
      (Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cont_cycBar ℚ Ω l))
    exact h1
  · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, m, k, hk, fun s _ => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one, hθ, hpow]
private theorem alg_det (P : _root_.UpperTheory.V.Af.HypothesesH') (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1)) := alg0 P ι W hW hdet _
private theorem flag_all {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) {B : ValuationSubring Ω}
    (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∃ N : Subgroup (G ℚ Ω), IsOpen (N : Set (G ℚ Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∃ s ∈ N ⊓ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1) ∧
        ∃ κ, IsFlagOn W (Dec (F := ℚ) A) κ ∧ ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ N ⊓ Ine (F := ℚ) A →
          κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) := by
  have : IsGalois ℚ Ω := {}
  have := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : H.normalCore.Normal := H.normalCore_normal
  have hH' : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have hk : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨H.normalCore, hH', fun w hw A hA => ?_⟩
  have hAl : A.valuation (l : Ω) < 1 := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.1 w hA).2 hw
  obtain ⟨s, hs, hs'⟩ := UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.cyc_inf hAl
  have hs0 : s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) A :=
    ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩
  have hinf : ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l (s ^ H.normalCore.index) ^ k ≠ 1 := fun k hk0 h => by
    rw [map_pow, ← pow_mul] at h
    exact hs' _ (mul_ne_zero hk hk0) h
  refine ⟨⟨_, hs0, hinf⟩, ?_⟩
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of hB hw) hA
  have hfl' : IsFlagOn W (H.normalCore ⊓ Ine (F := ℚ) (g • B))
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H.normalCore ⊓ Ine (F := ℚ) (g • B)).subtype) := by
    obtain ⟨p, hp⟩ := hfl
    refine ⟨p * (W g)⁻¹, fun t => ?_⟩
    have hm : g⁻¹ * (t : G ℚ Ω) * g ∈ H ⊓ Ine (F := ℚ) B :=
      ⟨H.normalCore_le (hn.conj_mem' _ t.2.1 g), GlobalTheory.PointIrredCompare.conj_mem_Ine_of_smul t.2.2⟩
    have e1 : p * (W g)⁻¹ * W t * (p * (W g)⁻¹)⁻¹ = p * W (g⁻¹ * (t : G ℚ Ω) * g) * p⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    obtain ⟨h1, h2⟩ := hp ⟨_, hm⟩
    rw [e1]
    refine ⟨h1, fun i => (h2 i).trans ?_⟩
    congr 1
    change ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (g⁻¹ * (t : G ℚ Ω) * g) = ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) t
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  exact UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.flag_stable W (Dec (F := ℚ) (g • B)) (H.normalCore ⊓ Ine (F := ℚ) (g • B)) _ le_rfl
    (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d, by simpa using conj_mem_Ine ((Dec (F := ℚ) (g • B)).inv_mem hd) hs.2⟩)
    (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (by
      refine ⟨_, hs0, fun h1 => hinf (e + e) (by omega) ?_⟩
      rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1
      rw [pow_add]
      exact mul_eq_one_iff_eq_inv.2 h1) hfl'
private theorem zpow_ne {C : Type} [Group C] {x : C} (h : ∀ k : ℕ, k ≠ 0 → x ^ k ≠ 1) {a b : ℤ} (e : x ^ a = x ^ b) : a = b := by
  by_contra hne
  have h1 : x ^ (a - b) = 1 := by rw [zpow_sub, e, mul_inv_cancel]
  refine h (a - b).natAbs (by omega) ?_
  rcases Int.natAbs_eq (a - b) with h2 | h2
  · rw [← zpow_natCast, ← h2, h1]
  · rw [← zpow_natCast, ← inv_inj, ← zpow_neg, ← h2, h1, inv_one]
private theorem inf_char (P : _root_.UpperTheory.V.Af.HypothesesH') (hC : CompatT) (ι : Qbar l ≃+* ℂ) {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hW : Continuous W) (π : TR.CuspSub ℚ 2) (hreg : π.IsRegAlg) (hatt : AttR ι W π) (hU : WitUp ι W)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∀ v, π.HasInfChar v (infOf ![(e : ℤ), -(e : ℤ)]) := by
  intro v
  obtain ⟨hdet, L, _, _, _, _, _, hirr, ⟨η, σ₀, hσ₀, hησ, hηL⟩, ka, hka, hWit⟩ := hU
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  obtain ⟨K, hK, hKC⟩ := Z.Bc.exists_quad L Ω η σ₀ hσ₀ hησ hηL
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm a.is_comm.comm
  have ec : W.comp (galEmb ℚ L Ω) = (W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) := MonoidHom.ext fun _ => rfl
  have hirr' : IsIrr ((W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω)) := ec ▸ hirr
  obtain ⟨P₁, a1, a2, a3⟩ := _root_.UpperTheory.V.Z.Bc.upQuadI_of_alt P.toClassicalTheorems (Z.Bc.quadLiftRealToComplex_of_base_change P.bc) ℚ K Ω l ι hK W π hW hreg hatt
    ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr')
  obtain ⟨Q, b1, b2, b3⟩ := _root_.UpperTheory.V.Z.Bc.upSolI_of_alt P.toClassicalTheorems (Z.Bc.cyclicLiftRankTwo_of_cyclic_base_change P.cyc) K L Ω l ι _ P₁
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) a1 a2 hirr'
  rw [← ec] at b2
  have hWL : Continuous (W.comp (galEmb ℚ L Ω)) := hW.comp (continuous_restrictScalarsHom ℚ L Ω)
  have hpol : Sol.Pol ι W := by
    have halg := alg0 P ι W hW hdet 0
    rw [zpow_zero, mul_one] at halg
    obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
    rw [zpow_zero, one_mul] at hθ
    obtain ⟨c, hc⟩ := cc_ex Ω
    obtain ⟨J, hJ⟩ := pairing2 W c
    exact ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J, halg,
      fun c c' h h' => by rw [hθ]; exact kills_cc hM hχ h h', hc, hJ⟩
  have hQ := _root_.UpperTheory.V.Z.Win.polarized_pair_of_attached P one_le_two (UpperTheory.solvable_polarized_restriction ℚ L Ω l ι 2 W hpol) b2
  have hka' : IsAlgChar ι ka := by
    obtain ⟨h1, art, χ, a, h2, h3, h4⟩ := hka
    exact ⟨χ, h1, art, a, h2, h3, h4⟩
  have hWA : WitA ι (W.comp (galEmb ℚ L Ω)) := by
    have := (_root_.UpperTheory.V.Z.Win.aIsoTwOf_alt flagLaws ImaginaryQuadraticEtaCharacter.winTw P.toClassicalTheorems L Ω l ι 2 _ hWit).2 ka⁻¹ ((_root_.UpperTheory.V.Af.algOfCyc_s P L Ω l ι).2.1 ka ka hka' hka').2
    rwa [UpperTheory.V.Z.Win.tw_tw_inv] at this
  obtain ⟨N, hN, hall⟩ := flag_all he W hB H hH hfl
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places L Ω l B
  obtain ⟨w, h⟩ := p1 fun h0 => (p2 h0).2 hB
  have hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := (p3 w h).1 hB
  have hw0 : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]; exact hw
  have hpot : PotUnl W (w.under (𝓞 ℚ)) := fun A hA => by
    obtain ⟨⟨s, hs, hs'⟩, κ, hκ, hI⟩ := hall _ hw0 A hA
    refine ⟨κ, hκ, fun i j m hm e0 => ?_⟩
    have e1 := DFunLike.congr_fun e0 ⟨s, Ine_le_Dec A hs.2⟩
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.mul_apply, hI i _ hs, hI j _ hs] at e1
    change (cycBar ℚ Ω l s ^ _) ^ m = (cycBar ℚ Ω l s ^ _ * cycBar ℚ Ω l s) ^ m at e1
    rw [← zpow_add_one, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at e1
    have e2 := mul_right_cancel₀ (show (m : ℤ) ≠ 0 by omega) (zpow_ne hs' e1)
    fin_cases i <;> fin_cases j <;> simp at e2 <;> omega
  have hpotL : PotUnl (W.comp (galEmb ℚ L Ω)) w := (((flagLaws ℚ Ω l 2 W).2.2.2 L).2.2 w hw).1 hpot
  obtain ⟨HT, hwt, hloc⟩ := hC L Ω l ι 2 one_le_two _ Q hWL b1 hQ b2
  obtain ⟨⟨σ, hσ⟩, -⟩ := _root_.UpperTheory.V.Af.local_comp_complex_of_printed_results P.toClassicalTheorems L 2 Q w
  obtain ⟨rc, hrc⟩ := recTExists L Ω B w h
  have hpl := (guard_of plainRec b1 b2 hWA (Or.inr (Or.inr hpotL)) hrc hσ).1
  obtain ⟨j, L0, hj, hBw⟩ := GlobalTheory.PlaceBridge.exists_locBridge l L Ω w B hw h
  obtain ⟨Bw, hBj, -⟩ := hBw L0 le_rfl
  have hInd : Induces Bw := fun x => by rw [hBj]; exact hj x
  have hJ := ((hloc w σ hσ).2 hpl B h _ Bw hInd).2 (Bw.j.comp (algebraMap L Ω)) Bw.Kw (AlgHom.id _ _) fun _ => rfl
  obtain ⟨-, κ, ⟨g, hg⟩, hI⟩ := hall _ hw0 B (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.place_of hB hw0)
  let ρ : ↥(Dec (F := L) B) →* ↥(Dec (F := ℚ) B) :=
    ((galEmb ℚ L Ω).comp (Dec (F := L) B).subtype).codRestrict _ fun s => s.2
  have hH2 := jumpsOpen ![(e : ℤ), -(e : ℤ)] _ hWL B Bw hInd (fun i => (κ i).comp ρ) (N.comap (galEmb ℚ L Ω))
    (hN.preimage (continuous_restrictScalarsHom ℚ L Ω)) ⟨g, fun s => hg (ρ s)⟩ (fun i s hs => hI i (ρ s) ⟨hs.1, hs.2⟩) _ _ hJ
  obtain ⟨μ, hμ, -⟩ := hreg v
  have hμQ : Q.HasInfChar (ι.toRingHom.comp (Bw.j.comp (algebraMap L Ω))) μ :=
    b3 _ μ (a3 _ μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v]))
  have hW2 := hwt (Bw.j.comp (algebraMap L Ω))
  rw [hH2, CG.HasInfChar.infChar_eq (π := CG.mk Q) hμQ] at hW2
  rwa [UpperTheory.V.Af.infOf_of_weights _ μ hW2] at hμ
end UpperTheory.V.Z.Win.RR
theorem UpperTheory.V.Z.Win.RR.autNewformA_of_exRS_of_compatT_of_repNewAE (hX : ExRS) (hC : CompatT) :
    _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Br.RepNewAE → AutNewformA := by
  rintro P hN Ω _ _ _ l hl ι e he W hW - ⟨π, hreg, hatt⟩ hU B hB H hH hfl
  have hinf := UpperTheory.V.Z.Win.RR.inf_char P hC ι he W hW π hreg hatt hU hB H hH hfl
  obtain ⟨χ, hχ⟩ := UpperTheory.V.Z.Win.RR.alg_det P ι W hW hU.1
  have hsd := (_root_.UpperTheory.V.Af.self_dual_real_of_printed_hida P ℚ Ω l ι 2 (by omega) W π hatt _ χ (UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.dual_det W) hχ).1
  obtain ⟨-, wt, HT, -, -, hall⟩ := hX ℚ Ω l ι 2 (by omega) π χ hreg ⟨fun v v' => by rw [Subsingleton.elim v v'], hsd⟩
  have hG := hall W hW hatt
  obtain ⟨f, hf⟩ := hN (2 * e + 1) (by omega) e π fun v => by
    convert hinf v using 1
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, ← Multiset.cons_coe,
      Multiset.coe_nil, Multiset.cons_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    congr 2 <;> push_cast <;> ring
  have hfrob : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι W w (algSat 2 (normV w) B) := hG.frob
  refine ⟨f, UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.ss_tw _ _ hatt.1, ?_⟩
  filter_upwards [UpperTheory.V.Af.NewformAutomorphy.ev_not_mem l hl.out.ne_zero, hf] with w hwl hfw A hA
  obtain ⟨S, hS, hpoly⟩ := hfw
  obtain ⟨h1, h2⟩ := hfrob w hwl S hS A hA
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h3 : cycZ ℚ Ω l s = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
      simp
    apply Units.ext
    rw [tw_val, h1 s hs, MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h3, map_one, one_zpow, Units.val_one, one_smul]
  · have h3 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
    have h4 : ι.toRingHom (((cycBar ℚ Ω l ^ (-(e : ℤ))) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (e : ℤ) := by
      rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h3, map_zpow₀,
        map_inv₀, map_natCast, inv_zpow', neg_neg]
    rw [tw_val, UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere.charpoly_smul _ _ _ (Units.ne_zero _) _ (h2 σ hσ), h4, hpoly]
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Af UpperTheory.Gal.SV
namespace UpperTheory.V.Z.Win.RR
theorem ordAway_a_alt : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAway := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAway_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem ordAbove_of_printsH : _root_.UpperTheory.V.Af.HypothesesH' → Sd.OrdAbove := fun P => _root_.UpperTheory.V.Z.Win.RR.ordAbove_of_alt (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) gd P
theorem autNewformA_of_printsH_of_repNewAE : _root_.UpperTheory.V.Af.HypothesesH' → Br.RepNewAE → AutNewformA := fun P =>
  _root_.UpperTheory.V.Z.Win.RR.autNewformA_of_exRS_of_compatT_of_repNewAE (_root_.UpperTheory.Gal.SV.exRS_alt P.toClassicalTheorems) (compatTOf (_root_.UpperTheory.Gal.SV.rowOf' P.litN.aut.gal) plainRec) P
end UpperTheory.V.Z.Win.RR
end
end
