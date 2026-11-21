import Formalism.LocalToGlobal.CMDeterminantIdeals.CmNumbersLink

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def IndexFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (M : Submodule (𝓞 K) (Fin m → K)) (b : Fin m → Fin m → K),
    M.FG → Submodule.span K (M : Set (Fin m → K)) = ⊤ → LinearIndependent K b → (∀ i, b i ∈ M) →
    ((FractionalIdeal.absNorm (MLat.mk (Submodule.span (𝓞 K) (Set.range b)) (fun _ => 0) : MLat K m).detIdeal : ℚ) : ℝ) =
      ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) *
        ((FractionalIdeal.absNorm (MLat.mk M (fun _ => 0) : MLat K m).detIdeal : ℚ) : ℝ)


namespace Dx

variable {K : Type} [Field K] [NumberField K]

def dS {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) K :=
  Submodule.span (𝓞 K) {d | ∃ x : Fin n → Fin n → K, (∀ i, x i ∈ M) ∧ d = (Matrix.of x).det}

def lastL (K : Type) [Field K] [NumberField K] (n : ℕ) : (Fin (n+1) → K) →ₗ[𝓞 K] K :=
  LinearMap.proj (Fin.last n)

def snocL (K : Type) [Field K] [NumberField K] (n : ℕ) : (Fin n → K) →ₗ[𝓞 K] (Fin (n+1) → K) where
  toFun w := Fin.snoc (α := fun _ => K) w 0
  map_add' u v := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c u := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] theorem snocL_castSucc {n : ℕ} (w : Fin n → K) (j : Fin n) : snocL K n w (Fin.castSucc j) = w j := by
  simp [snocL]

@[simp] theorem snocL_last {n : ℕ} (w : Fin n → K) : snocL K n w (Fin.last n) = 0 := by
  simp [snocL]

@[simp] theorem lastL_apply {n : ℕ} (v : Fin (n+1) → K) : lastL K n v = v (Fin.last n) := rfl



theorem idx {G H : Type*} [AddCommGroup G] [AddCommGroup H] (A' A : AddSubgroup G) (hA : A' ≤ A) (f : G →+ H) :
    A'.relIndex A = (A' ⊓ f.ker).relIndex (A ⊓ f.ker) * (A'.map f).relIndex (A.map f) := by
  set Z := f.ker
  have hmod : (A' ⊔ Z) ⊓ A = A' ⊔ (A ⊓ Z) := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hx⟩
      exact ⟨y, hy, z, ⟨by simpa using A.sub_mem hx (hA hy), hz⟩, rfl⟩
    · rintro ⟨y, hy, z, ⟨hzA, hz⟩, rfl⟩
      exact ⟨⟨y, hy, z, hz, rfl⟩, A.add_mem (hA hy) hzA⟩
  have h1 : A'.relIndex (A' ⊔ (A ⊓ Z)) = (A' ⊓ Z).relIndex (A ⊓ Z) := by
    rw [sup_comm, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A' (A ⊓ Z),
      ← AddSubgroup.inf_relIndex_right (A' ⊓ Z) (A ⊓ Z)]
    congr 1
    ext x; simp only [AddSubgroup.mem_inf]
    constructor
    · rintro ⟨h, h2, h3⟩; exact ⟨⟨h, h3⟩, h2, h3⟩
    · rintro ⟨⟨h, h3⟩, h2, _⟩; exact ⟨h, h2, h3⟩
  have h2 : (A' ⊔ (A ⊓ Z)).relIndex A = (A'.map f).relIndex (A.map f) := by
    rw [AddSubgroup.relIndex_map_map]
    have e : A ⊔ f.ker = A ⊔ (A' ⊔ f.ker) := by
      apply le_antisymm
      · exact sup_le le_sup_left (le_trans le_sup_right le_sup_right)
      · exact sup_le le_sup_left (sup_le (le_trans hA le_sup_left) le_sup_right)
    rw [e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A' ⊔ f.ker) A]
    show _ = ((A' ⊔ Z) ⊓ A).relIndex A
    rw [hmod]
  rw [← AddSubgroup.relIndex_mul_relIndex A' (A' ⊔ (A ⊓ Z)) A le_sup_left (sup_le hA inf_le_left), h1, h2]

theorem absNorm_eq_relIndex_mul (J J' : FractionalIdeal (𝓞 K)⁰ K) (hJ' : J' ≠ 0) (hle : J' ≤ J) :
    FractionalIdeal.absNorm J' = ((J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (J : Submodule (𝓞 K) K).toAddSubgroup : ℚ) * FractionalIdeal.absNorm J := by
  have hJ : J ≠ 0 := by rintro rfl; exact hJ' (FractionalIdeal.le_zero_iff.1 hle)
  have hX : J' * J⁻¹ ≤ 1 := by
    calc J' * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hle le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : J' = J * (X : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hX', mul_comm J', ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  obtain ⟨c, P, hc, hP⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  let φ : 𝓞 K →+ K := (AddMonoidHom.mulLeft ((algebraMap (𝓞 K) K c)⁻¹)).comp (algebraMap (𝓞 K) K).toAddMonoidHom
  have hc' : (algebraMap (𝓞 K) K c)⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc)
  have hφ : Function.Injective φ := by
    intro r s h
    have h' : (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K s := h
    exact IsFractionRing.injective (𝓞 K) K (mul_left_cancel₀ hc' h')
  have hmap : ∀ Q : Ideal (𝓞 K), ((FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      (Q : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup =
      Q.toAddSubgroup.map φ := by
    intro Q
    ext x
    simp only [Submodule.mem_toAddSubgroup, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
      Submodule.mem_span_singleton_mul, AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩, rfl⟩
  have hJ'P : J' = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      ((P * X : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hdec, hP, FractionalIdeal.coeIdeal_mul, mul_assoc]
  have hrel : (J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      (P * X).toAddSubgroup.relIndex P.toAddSubgroup := by
    rw [hJ'P, hmap, hP, hmap, AddSubgroup.relIndex_map_map_of_injective _ _ hφ]
  have hPX : P * X ≤ P := by simpa [mul_comm] using (Ideal.mul_le_right : X * P ≤ P)
  have htow := AddSubgroup.relIndex_mul_relIndex (P * X).toAddSubgroup P.toAddSubgroup ⊤ hPX le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htow
  have hn : ∀ Q : Ideal (𝓞 K), Ideal.absNorm Q = Q.toAddSubgroup.index := fun Q => by
    rw [Ideal.absNorm_apply]; rfl
  have hmul : Ideal.absNorm (P * X) = Ideal.absNorm P * Ideal.absNorm X := map_mul _ _ _
  rw [hn, hn, hn] at hmul
  have hP0 : P.toAddSubgroup.index ≠ 0 := by
    rw [← hn]
    intro h
    apply hJ
    rw [hP, Ideal.absNorm_eq_zero_iff.1 h, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hidx : (P * X).toAddSubgroup.relIndex P.toAddSubgroup = Ideal.absNorm X := by
    rw [hn X]
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP0)
    rw [htow, hmul, mul_comm]
  rw [hrel, hidx, hdec, map_mul, FractionalIdeal.coeIdeal_absNorm, mul_comm]

def Sand {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Prop :=
  (∃ a : 𝓞 K, a ≠ 0 ∧ ∀ i, (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K) ∈ M) ∧
    ∃ b ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (b • x i)

def fiD {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : FractionalIdeal (𝓞 K)⁰ K :=
  (MLat.mk M (fun _ => 0) : MLat K n).detIdeal





theorem frac_map {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    IsFractional (𝓞 K)⁰ (M.map (lastL K n)) := by
  obtain ⟨b, hb, hint⟩ := hM.2
  refine ⟨b, hb, fun y hy => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hy
  exact hint v hv _

def imI {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨M.map (lastL K n), frac_map M hM⟩

theorem imI_ne_zero {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : imI M hM ≠ 0 := by
  obtain ⟨a, ha, hs⟩ := hM.1
  intro h0
  have hmem : algebraMap (𝓞 K) K a ∈ (imI M hM : Submodule (𝓞 K) K) :=
    ⟨_, hs (Fin.last n), by simp⟩
  rw [h0] at hmem
  exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha ((FractionalIdeal.mem_zero_iff _).1 hmem)

theorem exists_unit_one_add_generator {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    ∃ z : Fin (n+1) → K, z (Fin.last n) = 1 ∧ ∀ q ∈ M.map (lastL K n), q • z ∈ M := by
  set I := imI M hM
  have hI : I * I⁻¹ = 1 := mul_inv_cancel₀ (imI_ne_zero M hM)
  let T : Submodule (𝓞 K) K :=
    { carrier := {t | ∃ z : Fin (n+1) → K, z (Fin.last n) = t ∧ ∀ q ∈ M.map (lastL K n), q • z ∈ M}
      add_mem' := by
        rintro s t ⟨z, hz, hzM⟩ ⟨w, hw, hwM⟩
        exact ⟨z + w, by simp [hz, hw], fun q hq => by rw [smul_add]; exact M.add_mem (hzM q hq) (hwM q hq)⟩
      zero_mem' := ⟨0, by simp, fun q _ => by simp⟩
      smul_mem' := by
        rintro c t ⟨z, hz, hzM⟩
        refine ⟨c • z, by simp [hz], fun q hq => ?_⟩
        rw [smul_comm]; exact M.smul_mem c (hzM q hq) }
  have hle : ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ T := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro p hp c hc
    obtain ⟨y, hy, rfl⟩ := hp
    refine ⟨c • y, by simp [mul_comm], fun q hq => ?_⟩
    have hqc : q * c ∈ I * I⁻¹ := FractionalIdeal.mul_mem_mul hq hc
    rw [hI] at hqc
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hqc
    rw [smul_smul, ← hr, algebraMap_smul]
    exact M.smul_mem r hy
  have h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [hI]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
  obtain ⟨z, hz, hzM⟩ := hle h1
  exact ⟨z, hz, hzM⟩




end Dx

end Formalism.L2.LamCM
