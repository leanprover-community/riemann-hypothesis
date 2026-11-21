import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantFunctionalEqHaarMultiple
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatProdSpanTensors
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialIntegralMemSchwartzBruhat

section
noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

section Tens

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space A] [T2Space B]

theorem tens_mem (a : SB A) (b : SB B) :
    (fun q : A × B => (a : A → ℂ) q.1 * (b : B → ℂ) q.2) ∈ SB (A × B) := by
  have ha := mem_SB_iff.1 a.2
  have hb := mem_SB_iff.1 b.2
  refine mem_SB_iff.2 ⟨?_, ?_⟩
  · exact (ha.1.comp_continuous continuous_fst).mul (hb.1.comp_continuous continuous_snd)
  · refine HasCompactSupport.intro (IsCompact.prod ha.2 hb.2) ?_
    intro q hq
    rw [Set.mem_prod, not_and_or] at hq
    rcases hq with h | h
    · simp [image_eq_zero_of_notMem_tsupport h]
    · simp [image_eq_zero_of_notMem_tsupport h]

def tens (a : SB A) (b : SB B) : SB (A × B) :=
  ⟨_, tens_mem a b⟩

@[simp]
theorem tens_apply (a : SB A) (b : SB B) (q : A × B) :
    ((tens a b : SB (A × B)) : A × B → ℂ) q = (a : A → ℂ) q.1 * (b : B → ℂ) q.2 :=
  rfl

def tensL (b : SB B) : SB A →ₗ[ℂ] SB (A × B) where
  toFun a := tens a b
  map_add' a a' := Subtype.ext (funext fun q => by
    show ((a : A → ℂ) q.1 + (a' : A → ℂ) q.1) * (b : B → ℂ) q.2 = _
    rw [add_mul]; rfl)
  map_smul' c a := Subtype.ext (funext fun q => by
    show (c * (a : A → ℂ) q.1) * (b : B → ℂ) q.2 = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    rw [mul_assoc])

@[simp]
theorem tensL_apply (a : SB A) (b : SB B) : tensL b a = tens a b :=
  rfl

def tensR (a : SB A) : SB B →ₗ[ℂ] SB (A × B) where
  toFun b := tens a b
  map_add' b b' := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * ((b : B → ℂ) q.2 + (b' : B → ℂ) q.2) = _
    rw [mul_add]; rfl)
  map_smul' c b := Subtype.ext (funext fun q => by
    show (a : A → ℂ) q.1 * (c * (b : B → ℂ) q.2) = c * ((a : A → ℂ) q.1 * (b : B → ℂ) q.2)
    ring)

@[simp]
theorem tensR_apply (a : SB A) (b : SB B) : tensR a b = tens a b :=
  rfl

end Tens

theorem span_transfer {A : Type*} [TopologicalSpace A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (T : SB A →ₗ[ℂ] M) {S : Set (A → ℂ)} (hS : S ⊆ SB A) (N : Submodule ℂ M)
    (hT : ∀ F (hF : F ∈ S), T ⟨F, hS hF⟩ ∈ N) (f : SB A)
    (hf : (f : A → ℂ) ∈ Submodule.span ℂ S) : T f ∈ N := by
  have key : Submodule.span ℂ S ≤ (N.comap T).map (SB A).subtype := by
    rw [Submodule.span_le]
    intro F hF
    exact Submodule.mem_map.2 ⟨⟨F, hS hF⟩, hT F hF, rfl⟩
  obtain ⟨f', hf', e⟩ := Submodule.mem_map.1 (key hf)
  have e' : f' = f := Subtype.ext e
  subst e'
  exact hf'

section Prod

variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B]

theorem tens_induction {M : Type*} [AddCommGroup M] [Module ℂ M] (T : SB (A × B) →ₗ[ℂ] M)
    (N : Submodule ℂ M) (f : SB (A × B))
    (h : ∀ (a : SB A) (b : SB B), (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 →
      (f : A × B → ℂ) q ≠ 0) → T (tens a b) ∈ N) : T f ∈ N := by
  refine span_transfer T ?_ N ?_ f (GlobalTheory.T.schwartzBruhat_prod_span_tensors A B f)
  · rintro F ⟨a, b, -, rfl⟩
    exact tens_mem a b
  · rintro F ⟨a, b, hab, rfl⟩
    exact h a b hab

end Prod

section Fint

variable {A B : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A] [TopologicalSpace B] [T2Space B] [LocallyCompactSpace B]
  [TotallyDisconnectedSpace B] [MeasurableSpace B] [BorelSpace B]
  (μ : Measure B) [IsFiniteMeasureOnCompacts μ]

theorem fib_integrable (F : SB (A × B)) (a : A) {w : B → ℂ} (hw : Continuous w) :
    Integrable (fun b => (F : A × B → ℂ) (a, b) * w b) μ := by
  have hF := mem_SB_iff.1 F.2
  refine Continuous.integrable_of_hasCompactSupport
    ((hF.1.continuous.comp (Continuous.prodMk_right a)).mul hw) ?_
  refine HasCompactSupport.mul_right (f' := w) ?_
  refine HasCompactSupport.intro (IsCompact.image hF.2 continuous_snd) ?_
  intro b hb
  by_contra h
  exact hb ⟨(a, b), subset_tsupport _ h, rfl⟩

def intB (w : B → ℂ) (hw : Continuous w) : SB (A × B) →ₗ[ℂ] SB A where
  toFun F := ⟨fun a => ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ, GlobalTheory.T.partial_integral_mem_schwartzBruhat A B μ w hw F⟩
  map_add' F F' := Subtype.ext (funext fun a => by
    show ∫ b, ((F : A × B → ℂ) (a, b) + (F' : A × B → ℂ) (a, b)) * w b ∂μ =
      (∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ) + ∫ b, (F' : A × B → ℂ) (a, b) * w b ∂μ
    simp only [add_mul]
    exact integral_add (fib_integrable μ F a hw) (fib_integrable μ F' a hw))
  map_smul' c F := Subtype.ext (funext fun a => by
    show ∫ b, (c * (F : A × B → ℂ) (a, b)) * w b ∂μ = c * ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ
    simp only [mul_assoc]
    exact integral_const_mul c _)

@[simp]
theorem intB_apply (w : B → ℂ) (hw : Continuous w) (F : SB (A × B)) (a : A) :
    ((intB μ w hw F : SB A) : A → ℂ) a = ∫ b, (F : A × B → ℂ) (a, b) * w b ∂μ :=
  rfl

theorem intB_tens (w : B → ℂ) (hw : Continuous w) (a : SB A) (b : SB B) :
    intB μ w hw (tens a b) = (∫ y, (b : B → ℂ) y * w y ∂μ) • a := by
  apply Subtype.ext
  funext x
  show ∫ y, ((a : A → ℂ) x * (b : B → ℂ) y) * w y ∂μ = (∫ y, (b : B → ℂ) y * w y ∂μ) * (a : A → ℂ) x
  simp only [mul_assoc]
  rw [integral_const_mul, mul_comm]

end Fint

section Factor

variable {A : Type} [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A]
  [TotallyDisconnectedSpace A]
  {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [T2Space K]
  [LocallyCompactSpace K] [TotallyDisconnectedSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]

def rtr (k : K) : SB (A × K) →ₗ[ℂ] SB (A × K) :=
  pullHomeo ((Homeomorph.refl A).prodCongr (Homeomorph.mulRight k))

@[simp]
theorem rtr_apply (k : K) (F : SB (A × K)) (q : A × K) :
    ((rtr k F : SB (A × K)) : A × K → ℂ) q = (F : A × K → ℂ) (q.1, q.2 * k) :=
  rfl

theorem factor_intB (uK : IsUnimod K) (b0 : SB K) (hb0 : ∫ y, (b0 : K → ℂ) y ∂μ = 1)
    (M : SB (A × K) →ₗ[ℂ] ℂ) (hM : ∀ (k : K) (F : SB (A × K)), M (rtr k F) = M F)
    (F : SB (A × K)) :
    M F = M (tens (intB μ (fun _ => (1 : ℂ)) continuous_const F) b0) := by
  have hc : ∀ a : SB A, ∃ c : ℂ, ∀ b : SB K, M (tens a b) = c * ∫ y, (b : K → ℂ) y ∂μ := by
    intro a
    refine GlobalTheory.T.invariant_functional_eq_haar_multiple K uK μ (M ∘ₗ tensR a) ?_
    intro k b
    have e : tens a (pullHomeo (Homeomorph.mulRight k) b) = rtr k (tens a b) := rfl
    show M (tens a (pullHomeo (Homeomorph.mulRight k) b)) = M (tens a b)
    rw [e, hM]
  choose c hc using hc
  let T : SB (A × K) →ₗ[ℂ] ℂ :=
    M - M ∘ₗ tensL b0 ∘ₗ intB μ (fun _ => (1 : ℂ)) continuous_const
  have key : T F ∈ (⊥ : Submodule ℂ ℂ) := by
    refine tens_induction T ⊥ F (fun a b _ => ?_)
    rw [Submodule.mem_bot]
    show M (tens a b) - M (tensL b0 (intB μ (fun _ => (1 : ℂ)) continuous_const (tens a b))) = 0
    rw [intB_tens, LinearMap.map_smul, tensL_apply, LinearMap.map_smul, hc, hc, hb0]
    simp only [mul_one, smul_eq_mul]
    ring
  rw [Submodule.mem_bot] at key
  exact sub_eq_zero.1 key

end Factor

end PositivityTheory.PfBern.Frob
end
end

section
noncomputable section

open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil

namespace PositivityTheory.PfBern.Frob

structure Sec {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) where

  s : G ⧸ H → G
  cont : Continuous s
  sec : ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c

section Triv

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  {X : Type} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H}

theorem Sec.inv_smul (σ : Sec H) (c : G ⧸ H) : (σ.s c)⁻¹ • c = ((1 : G) : G ⧸ H) := by
  have hc := σ.sec c
  calc (σ.s c)⁻¹ • c = (σ.s c)⁻¹ • ((σ.s c : G) : G ⧸ H) := by rw [hc]
    _ = ((1 : G) : G ⧸ H) := by rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]

theorem Sec.inv_mul_mem (σ : Sec H) (g : G) : (σ.s (g : G ⧸ H))⁻¹ * g ∈ H := by
  have hg := σ.sec (g : G ⧸ H)
  rwa [QuotientGroup.eq] at hg

variable (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)

def zpart (x : X) : Fib p :=
  ⟨(σ.s (p x))⁻¹ • x, by rw [hp]; exact σ.inv_smul (p x)⟩

@[simp]
theorem zpart_val (x : X) : (zpart hp σ x).1 = (σ.s (p x))⁻¹ • x := rfl

include hp in
theorem p_smul_fib (g : G) (z : Fib p) : p (g • z.1) = (g : G ⧸ H) := by
  have hz : p z.1 = ((1 : G) : G ⧸ H) := z.2
  rw [hp, hz, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

variable (hpc : Continuous p)

def triv : X × H ≃ₜ G × Fib p where
  toFun q := (σ.s (p q.1) * q.2, fibSmul hp q.2⁻¹ (zpart hp σ q.1))
  invFun r := (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩)
  left_inv q := by
    obtain ⟨x, h⟩ := q
    have e1 : ((σ.s (p x) * h : G) : G ⧸ H) = p x := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2, σ.sec]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show (σ.s (p x) * h) • (((h⁻¹ : H) : G) • ((σ.s (p x))⁻¹ • x)) = x
      rw [smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
    · show (σ.s ((σ.s (p x) * h : G) : G ⧸ H))⁻¹ * (σ.s (p x) * h) = h
      rw [e1, inv_mul_cancel_left]
  right_inv r := by
    obtain ⟨g, z⟩ := r
    have e2 := p_smul_fib hp g z
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show σ.s (p (g • z.1)) * ((σ.s (g : G ⧸ H))⁻¹ * g) = g
      rw [e2, mul_inv_cancel_left]
    · show (((⟨(σ.s (g : G ⧸ H))⁻¹ * g, σ.inv_mul_mem g⟩ : H)⁻¹ : H) : G) •
          ((σ.s (p (g • z.1)))⁻¹ • (g • z.1)) = z.1
      rw [e2, smul_smul, smul_smul, Subgroup.coe_inv]
      simp [mul_assoc]
  continuous_toFun := by
    refine Continuous.prodMk
      ((σ.cont.comp (hpc.comp continuous_fst)).mul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk ((continuous_subtype_val.comp continuous_snd.inv).smul
      (((σ.cont.comp (hpc.comp continuous_fst)).inv).smul continuous_fst)) _
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) ?_
    exact Continuous.subtype_mk
      (((σ.cont.comp (QuotientGroup.continuous_mk.comp continuous_fst)).inv).mul continuous_fst) _

@[simp]
theorem triv_apply (q : X × H) :
    triv hp σ hpc q = (σ.s (p q.1) * q.2, fibSmul hp q.2⁻¹ (zpart hp σ q.1)) := rfl

@[simp]
theorem triv_symm_apply (r : G × Fib p) :
    (triv hp σ hpc).symm r = (r.1 • r.2.1, ⟨(σ.s (r.1 : G ⧸ H))⁻¹ * r.1, σ.inv_mul_mem r.1⟩) := rfl

end Triv

section Fap

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure]

def avg [LocallyCompactSpace (Fib p)] : SB (G × Fib p) →ₗ[ℂ] SB X :=
  intB μH (fun _ => (1 : ℂ)) continuous_const ∘ₗ pullHomeo (triv hp σ hpc)

def fap [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) : SB X :=
  avg hp σ hpc μH (tens α φ)

theorem fap_apply [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (x : X) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) x = ∫ h, (α : G → ℂ) (σ.s (p x) * (h : G)) *
      (φ : Fib p → ℂ) (fibSmul hp h⁻¹ (zpart hp σ x)) ∂μH := by
  simp [fap, avg]

theorem fap_smul [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (g : G) (z : Fib p) :
    ((fap hp σ hpc μH α φ : SB X) : X → ℂ) (g • z.1) =
      ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH := by
  rw [fap_apply, p_smul_fib hp g z]
  set s0 := σ.s (g : G ⧸ H)
  set k : H := ⟨s0⁻¹ * g, σ.inv_mul_mem g⟩
  conv_lhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have e1 : s0 * ((k * h : H) : G) = g * h := by
    simp [k, mul_assoc]
  have e2 : fibSmul hp (k * h)⁻¹ (zpart hp σ (g • z.1)) = fibSmul hp h⁻¹ z := by
    apply Subtype.ext
    simp [k, s0, smul_smul, mul_assoc, p_smul_fib hp g z]
  simp only [e1, e2]

theorem eq_fap [LocallyCompactSpace (Fib p)] (α : SB G) (φ : SB (Fib p)) (f : SB X)
    (hf : ∀ (g : G) (z : Fib p), (f : X → ℂ) (g • z.1) =
      ∫ h, (α : G → ℂ) (g * (h : G)) * (φ : Fib p → ℂ) (fibSmul hp h⁻¹ z) ∂μH) :
    f = fap hp σ hpc μH α φ := by
  apply Subtype.ext
  funext x
  have hx : x = σ.s (p x) • (zpart hp σ x).1 := by simp
  rw [hx, hf, fap_smul]

end Fap

end PositivityTheory.PfBern.Frob
end
end
