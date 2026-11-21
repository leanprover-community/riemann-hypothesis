import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensVolS
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul

section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def pv (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → Af F ⊗[F] E) : Fin n → Fv F v ⊗[F] E :=
  fun i => tensMap (E := E) (evalV F v) (x i)

def latHat (Λ : Set (Fin n → E)) : Set (Fin n → Af F ⊗[F] E) :=
  {x | ∀ v, pv v x ∈ latLoc (E := E) v Λ}

theorem pv_mulVec (v : HeightOneSpectrum (𝓞 F)) (m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))
    (x : Fin n → Af F ⊗[F] E) :
    pv v (m *ᵥ x) = (m.map (tensMap (E := E) (evalV F v))) *ᵥ pv v x := by
  funext i
  simp [pv, Matrix.mulVec, dotProduct, map_sum]

open Classical in
theorem singleV_smul (v : HeightOneSpectrum (𝓞 F)) (c : F) (y : Fv F v) :
    singleV F v (c • y) = c • singleV F v y := by
  apply RestrictedProduct.ext
  intro j
  show (singleV F v (c • y)) j = evalV F j (c • singleV F v y)
  rw [map_smul]
  show _ = c • (singleV F v y) j
  by_cases h : j = v
  · subst h
    rw [PI.VolStabSW.VolAAW.singleV_self, PI.VolStabSW.VolAAW.singleV_self]
  · rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, PI.VolStabSW.VolAAW.singleV_ne _ _ h, smul_zero]

def sV (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] Af F where
  toFun := singleV F v
  map_add' := PI.VolStabSW.SdUniqW.singleV_add v
  map_smul' := singleV_smul v

def liftV (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : Fin n → Af F ⊗[F] E :=
  fun i => LinearMap.rTensor E (sV v) (y i)

theorem tens_lift_self (v : HeightOneSpectrum (𝓞 F)) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F v) (LinearMap.rTensor E (sV v) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F v (singleV F v a)) ⊗ₜ[F] e = a ⊗ₜ e
    show (singleV F v a v) ⊗ₜ[F] e = a ⊗ₜ e
    rw [PI.VolStabSW.VolAAW.singleV_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem tens_lift_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (z : Fv F v ⊗[F] E) :
    tensMap (E := E) (evalV F w) (LinearMap.rTensor E (sV v) z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [LinearMap.rTensor_tmul]
    show (evalV F w (singleV F v a)) ⊗ₜ[F] e = 0
    show (singleV F v a w) ⊗ₜ[F] e = 0
    rw [PI.VolStabSW.VolAAW.singleV_ne _ _ h, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem pv_liftV_self (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E) : pv v (liftV v y) = y := by
  funext i
  exact tens_lift_self v (y i)

theorem pv_liftV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fin n → Fv F v ⊗[F] E) :
    pv w (liftV v y) = 0 := by
  funext i
  exact tens_lift_ne h (y i)

theorem liftV_mem (Λ : Set (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : liftV v y ∈ latHat (F := F) Λ := by
  intro w
  by_cases h : w = v
  · subst h
    rw [pv_liftV_self]
    exact hy
  · rw [pv_liftV_ne h]
    exact zero_mem _

theorem loc_of_matStab (Λ : Set (Fin n → E)) {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)}
    (hm : m ∈ matStab (latHat (F := F) Λ)) (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v Λ) : (m.map (tensMap (E := E) (evalV F v))) *ᵥ y ∈ latLoc (E := E) v Λ := by
  have h := hm _ (liftV_mem Λ v hy) v
  rwa [pv_mulVec, pv_liftV_self] at h

end Lift

end MassDataMassesW.KCptW
end
end

section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Char

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def stabGLHat (Λ : Set (Fin n → E)) : Set (GL (Fin n) (Af F ⊗[F] E)) :=
  {g | (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) ∧
    ((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ)}

theorem mem_Kloc_of (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)} (hg : g ∈ stabGLHat Λ)
    (v : HeightOneSpectrum (𝓞 F)) : compV v g ∈ Kloc (E := E) v Λ := by
  intro y
  constructor
  · intro hy
    exact loc_of_matStab Λ hg.1 v hy
  · intro hy
    have hy' : ((g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map (tensMap (E := E) (evalV F v))) *ᵥ y ∈
        latLoc (E := E) v Λ := hy
    have h := loc_of_matStab Λ hg.2 v hy'
    rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at h

theorem matStab_of_mem (Λ : Set (Fin n → E)) {g : GL (Fin n) (Af F ⊗[F] E)}
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), compV v g ∈ Kloc (E := E) v Λ) :
    (g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ matStab (latHat (F := F) Λ) := by
  intro x hx v
  rw [pv_mulVec]
  exact ((hg v) (pv v x)).1 (hx v)

theorem kf_iff (Λ : Set (Fin n → E)) (g : HA (Af F) σ J) :
    g ∈ Kf σ J Λ ↔ incAf σ J g ∈ stabGLHat Λ := by
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Kf σ J Λ := (Kf σ J Λ).inv_mem hg
    refine ⟨matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg v), ?_⟩
    rw [← map_inv]
    exact matStab_of_mem Λ fun v => (Subgroup.mem_iInf.1 hg' v)
  · intro h
    rw [Kf, Subgroup.mem_iInf]
    intro v
    exact mem_Kloc_of Λ h v

end Char

def LatHatOpen : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsOpen (latHat (F := F) (L : Set (Fin n → E)))

def LatHatCompact : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → L.FG →
    IsCompact (latHat (F := F) (L : Set (Fin n → E)))

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {n : ℕ}

theorem pv_intSmul_single (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (j : Fin n) :
    pv v ((N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E)) = ratV (F := F) (Fv F v) (N • (Pi.single j (1 : E) : Fin n → E)) := by
  classical
  funext i
  by_cases h : i = j
  · subst h
    simp [pv, ratV, Algebra.smul_def, tensMap, inclR]
  · simp [pv, ratV, h, tensMap, inclR]

theorem hcol_hat (L : Submodule (𝓞 E) (Fin n → E)) {N : ℤ}
    (hN : ∀ j : Fin n, N • (Pi.single j (1 : E) : Fin n → E) ∈ L) (j : Fin n) :
    (N : F) • (Pi.single j 1 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) (L : Set (Fin n → E)) := by
  intro v
  rw [pv_intSmul_single]
  exact Submodule.subset_span ⟨_, hN j, rfl⟩

theorem isCompact_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E)))) :
    IsCompact (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  classical
  set M := latHat (F := F) (L : Set (Fin n → E))
  have hMcl : IsClosed M := hc.isClosed
  obtain ⟨N, hN0, hNmem⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  have hN : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hSc := isCompact_matStab (K := F) hc hMcl (N : F) hN (hcol_hat L hNmem)
  have e : stabGLHat (F := F) (L : Set (Fin n → E)) =
      Units.embedProduct _ ⁻¹' (matStab M ×ˢ (MulOpposite.op '' matStab M)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, y, hy, hyg⟩
      refine ⟨h1, ?_⟩
      have hy' : y = (((g⁻¹ : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
        MulOpposite.op_injective hyg
      rwa [hy'] at hy
  rw [e]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod (hSc.image MulOpposite.continuous_op))

theorem isOpen_stabGLHat (L : Submodule (𝓞 E) (Fin n → E))
    (hc : IsCompact (latHat (F := F) (L : Set (Fin n → E))))
    (ho : IsOpen (latHat (F := F) (L : Set (Fin n → E)))) :
    IsOpen (stabGLHat (F := F) (L : Set (Fin n → E))) := by
  have hS := isOpen_matStab hc ho
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

end Glob

end MassDataMassesW.KCptW

namespace MassDataMassesW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub KCptW

theorem kCompactOpen_of (hO : LatHatOpen) (hC : LatHatCompact) : KCompactOpen := by
  intro D X
  have : FiniteDimensional X.B.I.F X.B.I.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have hMo := hO (F := X.B.I.F) X.B.I.L X.B.I.L_span X.B.I.L_fg
  have hMc := hC (F := X.B.I.F) X.B.I.L X.B.I.L_span X.B.I.L_fg
  have eK : (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) =
      incAf X.B.I.cm.sig X.B.I.J ⁻¹' stabGLHat (F := X.B.I.F) (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    ext g
    exact kf_iff X.B.I.cm.sig X.B.I.J _ g
  have hinc : Continuous (incAf X.B.I.cm.sig X.B.I.J) := continuous_subtype_val
  rw [eK]
  refine ⟨?_, (isOpen_stabGLHat X.B.I.L hMc hMo).preimage hinc⟩
  exact (PI.AdicCompletionValuation.isClosed_HR (Af X.B.I.F) X.B.I.cm.sig X.B.I.J).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_stabGLHat X.B.I.L X.B.I.L_span hMc)

end MassDataMassesW
end
end

section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Sand

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem tensMap_smul' {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (c : R) (z : R ⊗[F] E) : tensMap (E := E) φ (c • z) = φ c • tensMap (E := E) φ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [tensMap, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem continuous_tensEval (v : HeightOneSpectrum (𝓞 F)) : Continuous (tensMap (E := E) (evalV F v)) := by
  let f : Af F ⊗[F] E →ₛₗ[(evalV F v : Af F →+* Fv F v)] Fv F v ⊗[F] E :=
    { toFun := tensMap (E := E) (evalV F v), map_add' := map_add _,
      map_smul' := fun c z => tensMap_smul' (evalV F v) c z }
  exact IsModuleTopology.continuous_of_linearMapₛₗ (R := Af F) (S := Fv F v)
    (σ := (evalV F v : Af F →+* Fv F v)) (by exact RestrictedProduct.continuous_eval v) f

theorem continuous_pv (v : HeightOneSpectrum (𝓞 F)) : Continuous (pv (E := E) (n := n) v) :=
  continuous_pi fun i => (continuous_tensEval v).comp (continuous_apply i)

theorem pv_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fin n → Af F ⊗[F] E) : pv v (x + y) = pv v x + pv v y := by
  funext i; simp [pv]

theorem pv_zero (v : HeightOneSpectrum (𝓞 F)) : pv (E := E) (n := n) v 0 = 0 := by
  funext i; simp [pv]

theorem pv_neg (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → Af F ⊗[F] E) : pv v (-x) = -pv v x := by
  funext i; simp [pv]

theorem pv_zsmul (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (x : Fin n → Af F ⊗[F] E) : pv v (N • x) = N • pv v x := by
  funext i; simp [pv]

theorem ratV_zsmul (v : HeightOneSpectrum (𝓞 F)) (N : ℤ) (x : Fin n → E) :
    ratV (F := F) (Fv F v) (N • x) = N • ratV (F := F) (Fv F v) x := by
  funext i; simp [ratV]

theorem zsmul_mem_latLoc_of (L0 L : Set (Fin n → E)) (N : ℤ) (h : ∀ μ ∈ L0, N • μ ∈ L)
    (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc (E := E) v L0) :
    N • y ∈ latLoc (E := E) v L := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨μ, hμ, rfl⟩ := hz
    rw [← ratV_zsmul]
    exact Submodule.subset_span ⟨_, h μ hμ, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem zsmul_mem_latHat (L0 L : Set (Fin n → E)) (N : ℤ) (h : ∀ μ ∈ L0, N • μ ∈ L)
    {x : Fin n → Af F ⊗[F] E} (hx : x ∈ latHat (F := F) L0) : N • x ∈ latHat (F := F) L := by
  intro v
  rw [pv_zsmul]
  exact zsmul_mem_latLoc_of L0 L N h v (hx v)

def stdSub : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap (𝓞 E) E)

theorem single_mem_std (j : Fin n) : (Pi.single j (1 : E) : Fin n → E) ∈ (stdSub : Submodule (𝓞 E) (Fin n → E)) := by
  classical
  rw [stdSub, Submodule.mem_pi]
  intro i _
  rw [Pi.single_apply]
  split_ifs
  · exact LinearMap.mem_range.2 ⟨1, by simp⟩
  · exact zero_mem _

theorem span_std : Submodule.span E ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = ⊤ := by
  classical
  refine eq_top_iff.2 fun x _ => ?_
  rw [← Finset.univ_sum_single x]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : (Pi.single i (x i) : Fin n → E) = x i • (Pi.single i (1 : E) : Fin n → E) := by
    ext k
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_std i))

theorem std_mult (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)), N • μ ∈ (L : Set (Fin n → E)) := by
  classical
  obtain ⟨N, hN0, hN⟩ := exists_common_mult L hL (fun j : Fin n => (Pi.single j (1 : E) : Fin n → E))
  refine ⟨N, hN0, fun μ hμ => ?_⟩
  have hμ' : ∀ j, ∃ a : 𝓞 E, Algebra.linearMap (𝓞 E) E a = μ j := fun j =>
    LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) j (Set.mem_univ _))
  choose a ha using hμ'
  have e : N • μ = ∑ j, a j • (N • (Pi.single j (1 : E) : Fin n → E)) := by
    ext k
    simp only [Pi.smul_apply, Finset.sum_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← ha k, Algebra.linearMap_apply]
    simp only [Algebra.smul_def, mul_one, eq_intCast, zsmul_eq_mul]
    ring
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hN j)

theorem lat_mult (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ (L : Set (Fin n → E)), N • μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  obtain ⟨S, hS⟩ := hfg
  obtain ⟨N, hN0, hN⟩ := exists_common_mult (stdSub : Submodule (𝓞 E) (Fin n → E)) span_std
    (fun s : S => (s : Fin n → E))
  refine ⟨N, hN0, fun μ hμ => ?_⟩
  have hμ' : μ ∈ Submodule.span (𝓞 E) (S : Set (Fin n → E)) := by rw [hS]; exact hμ
  clear hμ
  induction hμ' using Submodule.span_induction with
  | mem z hz => exact hN ⟨z, hz⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

end Sand

def StdHatOpen : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    IsOpen (latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))

def StdHatCompact : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ},
    IsCompact (latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))

theorem zsmul_eq_cast_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} (N : ℤ)
    (x : Fin n → Af F ⊗[F] E) : N • x = (N : F) • x :=
  (Int.cast_smul_eq_zsmul F N x).symm

theorem latHatOpen_of (h0 : StdHatOpen) : LatHatOpen := by
  intro F E _ _ _ _ _ n L hL _
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := std_mult L hL
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  let G : AddSubgroup (Fin n → Af F ⊗[F] E) :=
    { carrier := latHat (F := F) (L : Set (Fin n → E))
      add_mem' := fun {x y} hx hy v => by rw [pv_add]; exact add_mem (hx v) (hy v)
      zero_mem' := fun v => by rw [pv_zero]; exact zero_mem _
      neg_mem' := fun {x} hx v => by rw [pv_neg]; exact neg_mem (hx v) }
  let W : Set (Fin n → Af F ⊗[F] E) :=
    {x | (N : F)⁻¹ • x ∈ latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))}
  have hWo : IsOpen W := (h0 (F := F) (E := E) (n := n)).preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Af F ⊗[F] E) ∈ W := by
    have h00 : (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) = 0 := smul_zero _
    show (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) _
    rw [h00]
    intro v
    rw [pv_zero]
    exact zero_mem _
  have hWG : W ⊆ (G : Set (Fin n → Af F ⊗[F] E)) := by
    intro x hx
    have h := zsmul_mem_latHat _ _ N hN hx
    rwa [zsmul_eq_cast_smul, smul_smul, mul_inv_cancel₀ hNF, one_smul] at h
  exact G.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWG)

theorem latHatCompact_of (h0 : StdHatCompact) : LatHatCompact := by
  intro F E _ _ _ _ _ n L hL hfg
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := lat_mult L hfg
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  have hcl : IsClosed (latHat (F := F) (L : Set (Fin n → E))) := by
    have e : latHat (F := F) (L : Set (Fin n → E)) =
        ⋂ v, pv v ⁻¹' (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [latHat]
    rw [e]
    exact isClosed_iInter fun v => (((latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup.isClosed_of_isOpen
      (isOpen_latLoc v L hL))).preimage (continuous_pv v)
  refine ((h0 (F := F) (E := E) (n := n)).image (continuous_const_smul ((N : F)⁻¹))).of_isClosed_subset hcl ?_
  intro x hx
  refine ⟨N • x, zsmul_mem_latHat _ _ N hN hx, ?_⟩
  show (N : F)⁻¹ • (N • x) = x
  rw [zsmul_eq_cast_smul, smul_smul, inv_mul_cancel₀ hNF, one_smul]

end MassDataMassesW.KCptW

namespace MassDataMassesW

open KCptW

theorem kCompactOpen_of_std (hO : StdHatOpen) (hC : StdHatCompact) : KCompactOpen :=
  kCompactOpen_of (latHatOpen_of @hO) (latHatCompact_of @hC)

end MassDataMassesW
end
end

section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Ohat

variable (F : Type) [Field F] [NumberField F]

def Ohat : Set (Af F) := {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

theorem isOpen_Ohat : IsOpen (Ohat F) := by
  have h := RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact h

theorem isCompact_Ohat : IsCompact (Ohat F) := by
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    fun v => isCompact_iff_compactSpace.mp (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap (𝓕 := Filter.cofinite)
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end Ohat

end MassDataMassesW.KCptW
end
end

section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Crd

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

def crd (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) : Fin (Module.finrank F E) → R :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun z

theorem crd_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (z : R ⊗[F] E) (k : Fin (Module.finrank F E)) : crd R' (tensMap (E := E) φ z) k = φ (crd R z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, tensMap, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add] at *
    simp only [crd, map_add, Pi.add_apply] at *
    rw [hx, hy]

def Bint (n : ℕ) : Set (Fin n → E) :=
  {x | ∀ i k, IsIntegral ℤ ((Module.finBasis F E).repr (x i) k)}

theorem algebraMap_mem_Ov (v : HeightOneSpectrum (𝓞 F)) {c : F} (hc : IsIntegral ℤ c) :
    algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, rfl⟩ : ∃ x : 𝓞 F, (x : F) = c := ⟨⟨c, hc⟩, rfl⟩
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v x

theorem crd_mem_of_latLoc {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v (Bint (F := F) n)) (i : Fin n) (k : Fin (Module.finrank F E)) :
    crd (Fv F v) (y i) k ∈ v.adicCompletionIntegers F := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have h := algebraMap_mem_Ov v (hx i k)
    simpa [crd, ratV, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.one_def] using h
  | zero => simp [crd]
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, crd, map_add] at ha hb ⊢
    exact add_mem ha hb
  | smul c a _ ha =>
    simp only [crd] at ha ⊢
    have e : (c • a) i = (c : Fv F v) • a i := rfl
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem c.2 ha

end Crd

end MassDataMassesW.KCptW
end
end

section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {n : ℕ}

def crdAll : (Fin n → Af F ⊗[F] E) ≃ₗ[Af F] (Fin n → Fin (Module.finrank F E) → Af F) :=
  LinearEquiv.piCongrRight fun _ => (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).equivFun

theorem continuous_crdAll : Continuous (crdAll (F := F) (E := E) (n := n)) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have h := IsModuleTopology.continuous_of_linearMap (R := Af F)
    (crdAll (F := F) (E := E) (n := n)).toLinearMap
  exact h

theorem continuous_crdAll_symm : Continuous (crdAll (F := F) (E := E) (n := n)).symm := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have h := IsModuleTopology.continuous_of_linearMap (R := Af F)
    (crdAll (F := F) (E := E) (n := n)).symm.toLinearMap
  exact h

theorem ratV_single (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (e : E) :
    ratV (F := F) (Fv F v) (Pi.single i e) = Pi.single i ((1 : Fv F v) ⊗ₜ[F] e) := by
  funext j
  unfold ratV
  rcases eq_or_ne j i with rfl | h
  · simp [inclR]
  · simp [h, inclR]

theorem single_mem_Bint (i : Fin n) (k : Fin (Module.finrank F E)) :
    (Pi.single i (Module.finBasis F E k) : Fin n → E) ∈ Bint (F := F) n := by
  unfold Bint
  rw [Set.mem_setOf_eq]
  intro i' k'
  rcases eq_or_ne i' i with rfl | h
  · rw [Pi.single_eq_same, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Pi.single_eq_of_ne h, map_zero, Finsupp.zero_apply]
    exact isIntegral_zero

theorem mem_latHat_Bint_iff (x : Fin n → Af F ⊗[F] E) :
    x ∈ latHat (F := F) (Bint (F := F) (E := E) n) ↔ ∀ i k, crd (Af F) (x i) k ∈ Ohat F := by
  constructor
  · intro hx i k v
    have h := crd_mem_of_latLoc v (hx v) i k
    simp only [pv, crd_tens] at h
    exact h
  · intro hx v
    set Btv := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
    have hc : ∀ i k, crd (Fv F v) (pv v x i) k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [pv, crd_tens]
      exact hx i k v
    rw [← Finset.univ_sum_single (pv v x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e1 : pv v x i = ∑ k, crd (Fv F v) (pv v x i) k • Btv k := (Btv.sum_equivFun (pv v x i)).symm
    have e2 : (Pi.single i (pv v x i) : Fin n → Fv F v ⊗[F] E) =
        ∑ k, crd (Fv F v) (pv v x i) k • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) := by
      conv_lhs => rw [e1]
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [e2]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hm : (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) ∈ latLoc (E := E) v (Bint (F := F) n) := by
      refine Submodule.subset_span ⟨Pi.single i (Module.finBasis F E k), single_mem_Bint i k, ?_⟩
      rw [ratV_single, Algebra.TensorProduct.basis_apply]
    have e3 : crd (Fv F v) (pv v x i) k • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) =
        (⟨_, hc i k⟩ : v.adicCompletionIntegers F) • (Pi.single i (Btv k) : Fin n → Fv F v ⊗[F] E) := rfl
    rw [e3]
    exact Submodule.smul_mem _ _ hm

theorem latHat_Bint_eq : latHat (F := F) (Bint (F := F) (E := E) n) =
    (crdAll (F := F) (E := E) (n := n)) ⁻¹' (Set.univ.pi fun _ => Set.univ.pi fun _ => Ohat F) := by
  ext x
  rw [mem_latHat_Bint_iff]
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  rfl

theorem isOpen_latHat_Bint : IsOpen (latHat (F := F) (Bint (F := F) (E := E) n)) := by
  rw [latHat_Bint_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ohat F).preimage continuous_crdAll

theorem isCompact_latHat_Bint : IsCompact (latHat (F := F) (Bint (F := F) (E := E) n)) := by
  rw [latHat_Bint_eq, ← LinearEquiv.image_symm_eq_preimage]
  exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Ohat F).image continuous_crdAll_symm

theorem mem_std_iff (μ : Fin n → E) :
    μ ∈ (stdSub : Submodule (𝓞 E) (Fin n → E)) ↔ ∀ i, IsIntegral ℤ (μ i) := by
  unfold stdSub
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies, LinearMap.mem_range, Algebra.linearMap_apply]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨μ i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem exists_bint_to_std : ∃ N : ℤ, N ≠ 0 ∧ ∀ μ ∈ Bint (F := F) (E := E) n,
    N • μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set b := Module.finBasis F E
  obtain ⟨N, hN0, hN⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image b)
  refine ⟨N, hN0, fun μ hμ => (mem_std_iff _).2 fun i => ?_⟩
  have hb : ∀ k, IsIntegral ℤ (N • b k) := fun k => hN _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have e : (N • μ) i = ∑ k, algebraMap F E (b.repr (μ i) k) * (N • b k) := by
    rw [Pi.smul_apply]
    conv_lhs => rw [← b.sum_repr (μ i)]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, Algebra.smul_def]
  rw [e]
  exact IsIntegral.sum _ fun k _ => ((hμ i k).algebraMap).mul (hb k)

theorem exists_std_to_bint : ∃ M : ℤ, M ≠ 0 ∧ ∀ μ ∈ ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)),
    M • μ ∈ Bint (F := F) (E := E) n := by
  classical
  set b := Module.finBasis F E
  set β := RingOfIntegers.basis E
  obtain ⟨M, hM0, hM⟩ := exists_integral_multiples ℤ ℚ (L := F)
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin (Module.finrank F E) =>
      b.repr (algebraMap (𝓞 E) E (β p.1)) p.2)
  refine ⟨M, hM0, fun μ hμ i k => ?_⟩
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) i (Set.mem_univ _))
  rw [Algebra.linearMap_apply] at ha
  have e : b.repr ((M • μ) i) k =
      ∑ j, (β.repr a j) • (M • b.repr (algebraMap (𝓞 E) E (β j)) k) := by
    rw [Pi.smul_apply, ← ha]
    conv_lhs => rw [← β.sum_repr a]
    simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  rw [e]
  refine IsIntegral.sum _ fun j _ => ?_
  have h := hM _ (Finset.mem_image_of_mem _ (Finset.mem_univ (j, k)))
  have h2 : (β.repr a j) • (M • b.repr (algebraMap (𝓞 E) E (β j)) k) =
      ((β.repr a j : ℤ) : F) * (M • b.repr (algebraMap (𝓞 E) E (β j)) k) := by
    rw [zsmul_eq_mul]
  rw [h2]
  have hc : IsIntegral ℤ ((β.repr a j : ℤ) : F) := by
    rw [← eq_intCast (algebraMap ℤ F)]; exact isIntegral_algebraMap
  exact hc.mul h

end Hat

theorem stdHatOpen_holds : StdHatOpen := by
  intro F E _ _ _ _ _ n
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := exists_bint_to_std (F := F) (E := E) (n := n)
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  let G : AddSubgroup (Fin n → Af F ⊗[F] E) :=
    { carrier := latHat (F := F) ((stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))
      add_mem' := fun {x y} hx hy v => by rw [pv_add]; exact add_mem (hx v) (hy v)
      zero_mem' := fun v => by rw [pv_zero]; exact zero_mem _
      neg_mem' := fun {x} hx v => by rw [pv_neg]; exact neg_mem (hx v) }
  let W : Set (Fin n → Af F ⊗[F] E) := {x | (N : F)⁻¹ • x ∈ latHat (F := F) (Bint (F := F) (E := E) n)}
  have hWo : IsOpen W := (isOpen_latHat_Bint (F := F) (E := E) (n := n)).preimage (continuous_const_smul _)
  have hW0 : (0 : Fin n → Af F ⊗[F] E) ∈ W := by
    show (N : F)⁻¹ • (0 : Fin n → Af F ⊗[F] E) ∈ latHat (F := F) _
    rw [smul_zero]
    intro v
    rw [pv_zero]
    exact zero_mem _
  have hWG : W ⊆ (G : Set (Fin n → Af F ⊗[F] E)) := by
    intro x hx
    have h := zsmul_mem_latHat _ _ N hN hx
    rwa [zsmul_eq_cast_smul, smul_smul, mul_inv_cancel₀ hNF, one_smul] at h
  exact G.isOpen_of_mem_nhds (Filter.mem_of_superset (hWo.mem_nhds hW0) hWG)

theorem stdHatCompact_holds : StdHatCompact := by
  intro F E _ _ _ _ _ n
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  obtain ⟨N, hN0, hN⟩ := exists_std_to_bint (F := F) (E := E) (n := n)
  have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.mpr hN0
  set L : Submodule (𝓞 E) (Fin n → E) := stdSub
  have hcl : IsClosed (latHat (F := F) (L : Set (Fin n → E))) := by
    have e : latHat (F := F) (L : Set (Fin n → E)) =
        ⋂ v, pv v ⁻¹' (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
      ext x
      simp [latHat]
    rw [e]
    exact isClosed_iInter fun v => (((latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup.isClosed_of_isOpen
      (isOpen_latLoc v L span_std))).preimage (continuous_pv v)
  refine ((isCompact_latHat_Bint (F := F) (E := E) (n := n)).image
    (continuous_const_smul ((N : F)⁻¹))).of_isClosed_subset hcl ?_
  intro x hx
  refine ⟨N • x, zsmul_mem_latHat _ _ N hN hx, ?_⟩
  show (N : F)⁻¹ • (N • x) = x
  rw [zsmul_eq_cast_smul, smul_smul, inv_mul_cancel₀ hNF, one_smul]

end MassDataMassesW.KCptW

namespace MassDataMassesW

theorem kCompactOpen_holds : KCompactOpen :=
  kCompactOpen_of_std @KCptW.stdHatOpen_holds @KCptW.stdHatCompact_holds

end MassDataMassesW
end
end
