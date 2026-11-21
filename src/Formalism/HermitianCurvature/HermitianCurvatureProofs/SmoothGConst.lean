import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport

section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Fam

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
  [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}

theorem parFam_add {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) (hg : PBI.ParFam k ρ U₀ g) :
    PBI.ParFam k ρ U₀ (fun q => f q + g q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', F', hU', hqU', hF', hgF⟩ := hg q₀ hq hG
  exact ⟨U ∩ U', fun q => F q + F' q, hU.inter hU', ⟨hqU, hqU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun q hq hG => by show f q + g q = F q + F' q; rw [hfF q hq.1 hG, hgF q hq.2 hG]⟩

theorem parFam_smul (a : ℂ) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U, fun q => a • F q, hU, hqU, hF.const_smul a, fun q hq hG => by show a • f q = a • F q; rw [hfF q hq hG]⟩

theorem parFam_zero : PBI.ParFam k ρ U₀ (fun _ => (0 : E)) := fun q₀ _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem parFam_sum {ι : Type} (s : Finset ι) {f : ι → Par × Mt k ρ → E}
    (hf : ∀ i ∈ s, PBI.ParFam k ρ U₀ (f i)) : PBI.ParFam k ρ U₀ (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (parFam_zero (E := E) (U₀ := U₀))
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := parFam_add h1 h2
    simpa [Finset.sum_insert ha] using this

theorem parFam_contAt {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) {Z : Par} {y : Mt k ρ} (hq : (Z, y) ∈ U₀)
    (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun Z' => f (Z', y)) Z := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf (Z, y) hq hy
  have hci : Continuous fun Z' : Par => ((Z', y) : Par × Mt k ρ) := continuous_id.prodMk continuous_const
  have hm : {Z' | (Z', y) ∈ U} ∈ 𝓝 Z := hci.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU)
  have hcF : ContinuousAt (fun Z' => F (Z', y)) Z :=
    ContinuousAt.comp (g := F) (f := fun Z' : Par => ((Z', y) : Par × Mt k ρ)) (x := Z)
      (hF.continuousOn.continuousAt (hU.mem_nhds hqU)) hci.continuousAt
  refine hcF.congr ?_
  filter_upwards [hm] with Z' hZ'
  exact (hfF (Z', y) hZ' hy).symm

theorem parFam_integrable [MeasurableSpace Par] [BorelSpace Par] {f : Par × Mt k ρ → E}
    (hf : PBI.ParFam k ρ U₀ f) {ν : Measure Par} [IsFiniteMeasure ν] {Kp : Set Par} (hK : IsCompact Kp)
    (hν : ν Kpᶜ = 0) {y : Mt k ρ} (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) (hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀) :
    Integrable (fun Z => f (Z, y)) ν := by
  have hc : ContinuousOn (fun Z => f (Z, y)) Kp := fun Z hZ =>
    (parFam_contAt hf (hKU Z hZ) hy).continuousWithinAt
  have hI : IntegrableOn (fun Z => f (Z, y)) Kp ν := hc.integrableOn_compact hK
  have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
    rw [ae_iff]
    simpa [Set.compl_def] using hν
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hI

end Fam

section Cls

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

def Rep {Par : Type} (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Z c y, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z y

def GGpos (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) : Set (Mt k ρ) := {y | 0 < Q.GGl k ρ z z' (Matrix.of y)}

variable (z z' π π') in

def Good (A : Module.End ℂ (Q.RadSp k ρ z z' π π')) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ → U₀ ⊆ Set.univ ×ˢ GGpos k ρ z z' →
  ∀ (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)), Rep Ψ Ψf →
    PBI.ParFam k ρ U₀ (fun q => Ψf q.1 q.2) →
  ∃ Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp), Rep (fun Z => A (Ψ Z)) Φf ∧ PBI.ParFam k ρ U₀ (fun q => Φf q.1 q.2) ∧
    (∀ K : Set (Par × Mt k ρ), (∀ q, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ K → Ψf q.1 q.2 = 0) →
      ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ closure K → Φf q.1 q.2 = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (Ψi : Q.RadSp k ρ z z' π π') (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Ψf Z y' ∂ν) →
      ∀ c, (A Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z y ∂ν

theorem good_id : Good z z' π π' (LinearMap.id : Module.End ℂ (Q.RadSp k ρ z z' π π')) := by
  intro Par _ _ _ _ _ U₀ _ _ Ψ Ψf hR hF
  refine ⟨Ψf, fun Z c y hy => hR Z c y hy, hF, fun K hK q _ hG hq => hK q hG (fun h => hq (subset_closure h)),
    fun ν _ Kp _ _ Ψi y V _ hyV hyG _ hi c => hi c y hyV hyG⟩

theorem good_comp {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A * B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hA Par U₀ hU₀ hUpos (fun Z => B (Ψ Z)) Φ₁ hR₁ hF₁
  refine ⟨Φ₂, fun Z c y hy => hR₂ Z c y hy, hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · have hK' : ∀ q', Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → q' ∉ closure K ∪ U₀ᶜ → Φ₁ q'.1 q'.2 = 0 := by
      intro q' hG' hq'
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hq'
      exact hS₁ K hK q' hq'.2 hG' hq'.1
    refine hS₂ _ hK' q hq hG ?_
    rw [closure_union, hU₀.isClosed_compl.closure_eq, closure_closure]
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not]
    exact ⟨hqK, hq⟩
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hi' : ∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (B Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Φ₁ Z y' ∂ν :=
      fun c y' hy' hG' => hW₁ ν Kp hKp hν Ψi y' V hV hy' hG' hKV hi c
    exact hW₂ ν Kp hKp hν (B Ψi) y V hV hyV hyG hKV hi' c

theorem good_add {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A + B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => Φ₁ Z y + Φ₂ Z y, fun Z c y hy => ?_, parFam_add hF₁ hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hR₁ Z c y hy, hR₂ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, hS₂ K hK q hq hG hqK, add_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, hW₂ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c,
      ← integral_add (parFam_integrable hF₁ hKp hν hyG hKU) (parFam_integrable hF₂ hKp hν hyG hKU)]

theorem good_smul (a : ℂ) {A : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) :
    Good z z' π π' (a • A) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => a • Φ₁ Z y, fun Z c y hy => ?_, parFam_smul a hF₁, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hR₁ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, integral_smul]

variable (z z' π π') in

def PGood (x : Q.Pr (Q.RadSp k ρ z z' π π')) : Prop := Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop

variable (z z' π π') in

def goodAlg : StarSubalgebra ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) where
  carrier := {x | PGood z z' π π' x}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_comp hx1 hy1, good_comp hy2 hx2⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_add hx1 hy1, good_add hx2 hy2⟩
  algebraMap_mem' := by
    intro a
    have e1 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1 = a • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) a = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ a
    have e2 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop = (starRingEnd ℂ a) • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) (starRingEnd ℂ a) = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ _
    refine ⟨?_, ?_⟩
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1
      rw [e1]; exact good_smul a good_id
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop
      rw [e2]; exact good_smul _ good_id
  star_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, hx1⟩


theorem good_mkP {X Xs : Module.End ℂ (Q.RadSp k ρ z z' π π')} (h1 : Good z z' π π' X) (h2 : Good z z' π π' Xs) :
    Q.mkP X Xs ∈ goodAlg z z' π π' := ⟨h1, h2⟩

end Cls

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end

section
open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Ops

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (k ρ) in

def ParOK (T : (Q.Mx k ρ → E) → Q.Mx k ρ → E) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ →
  ∀ f : Par → Q.Mx k ρ → E, PBI.ParFam k ρ U₀ (fun q => f q.1 (Matrix.of q.2)) →
    PBI.ParFam k ρ U₀ (fun q => T (f q.1) (Matrix.of q.2)) ∧
    (∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → ∀ W : Set (Par × Mt k ρ), IsOpen W → q ∈ W →
      (∀ q' ∈ W, Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q'.1 (Matrix.of q'.2) = 0) →
      T (f q.1) (Matrix.of q.2) = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (fi : Q.Mx k ρ → E) (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ y' ∈ V, Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) → fi (Matrix.of y') = ∫ Z, f Z (Matrix.of y') ∂ν) →
      T fi (Matrix.of y) = ∫ Z, T (f Z) (Matrix.of y) ∂ν

variable (k ρ) in

def SmoothG (a : Q.Mx k ρ → ℂ) : Prop :=
  ∀ y₀ : Mt k ρ, Matrix.of y₀ ∈ Q.Glev k ρ (Fin.last ρ) → ∃ (U : Set (Mt k ρ)) (F : Mt k ρ → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ y ∈ U, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → a (Matrix.of y) = F y

theorem smoothG_const (s : ℂ) : SmoothG k ρ (fun _ => s) := fun _ _ =>
  ⟨Set.univ, fun _ => s, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem smoothG_mul {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g * b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y * F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).mul (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) * b (Matrix.of y) = F y * F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem smoothG_sub {a b : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) (hb : SmoothG k ρ b) :
    SmoothG k ρ (fun g => a g - b g) := by
  intro y₀ hy
  obtain ⟨U, F, hU, hyU, hF, haF⟩ := ha y₀ hy
  obtain ⟨U', F', hU', hyU', hF', hbF⟩ := hb y₀ hy
  exact ⟨U ∩ U', fun y => F y - F' y, hU.inter hU', ⟨hyU, hyU'⟩,
    (hF.mono Set.inter_subset_left).sub (hF'.mono Set.inter_subset_right),
    fun y hy hG => by show a (Matrix.of y) - b (Matrix.of y) = F y - F' y; rw [haF y hy.1 hG, hbF y hy.2 hG]⟩

theorem parFam_congr {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f)
    (h : ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → f q = g q) (hU₀ : IsOpen U₀) :
    PBI.ParFam k ρ U₀ g := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U ∩ U₀, F, hU.inter hU₀, ⟨hqU, hq⟩, hF.mono Set.inter_subset_left,
    fun q hq' hG' => (h q hq'.2 hG').symm.trans (hfF q hq'.1 hG')⟩

theorem parFam_smulG {Par : Type} [NormedAddCommGroup Par] [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}
    {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a (Matrix.of q.2) • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', A, hU', hqU', hA, haA⟩ := ha q₀.2 hG
  refine ⟨U ∩ Prod.snd ⁻¹' U', fun q => A q.2 • F q, hU.inter (hU'.preimage continuous_snd), ⟨hqU, hqU'⟩, ?_,
    fun q hq' hG' => ?_⟩
  · exact (hA.comp contDiff_snd.contDiffOn (fun q hq => hq.2)).smul (hF.mono Set.inter_subset_left)
  · show a (Matrix.of q.2) • f q = A q.2 • F q
    rw [haA q.2 hq'.2 hG', hfF q hq'.1 hG']

theorem parOK_id : ParOK k ρ (E := E) (fun f => f) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨hf, fun q _ hG W _ hqW hW => hW q hqW hG, fun ν _ Kp _ _ fi y V _ hyV hyG _ hi => hi y hyV hyG⟩

theorem parOK_zero : ParOK k ρ (E := E) (fun _ _ => 0) := by
  intro Par _ _ _ _ _ U₀ _ f hf
  refine ⟨parFam_zero, fun _ _ _ _ _ _ _ => rfl, fun ν _ Kp _ _ fi y V _ _ _ _ _ => by simp⟩

theorem parOK_congr {T T' : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) (h : ∀ f g, T f g = T' f g) :
    ParOK k ρ T' := by
  have e : T = T' := funext fun f => funext fun g => h f g
  rw [← e]; exact hT

theorem parOK_add {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f g => T₁ f g + T₂ f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  refine ⟨parFam_add a₁ a₂, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show T₁ (f q.1) (Matrix.of q.2) + T₂ (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, b₂ q hq hG W hW hqW hz, add_zero]
  · have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    show T₁ fi (Matrix.of y) + T₂ fi (Matrix.of y) = ∫ Z, (T₁ (f Z) (Matrix.of y) + T₂ (f Z) (Matrix.of y)) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, c₂ ν Kp hKp hν fi y V hV hyV hyG hKV hi,
      integral_add (parFam_integrable a₁ hKp hν hyG hKU) (parFam_integrable a₂ hKp hν hyG hKU)]

theorem parOK_smulG {a : Q.Mx k ρ → ℂ} (ha : SmoothG k ρ a) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (hT : ParOK k ρ T) : ParOK k ρ (fun f g => a g • T f g) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := hT Par U₀ hU₀ f hf
  refine ⟨parFam_smulG ha a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · show a (Matrix.of q.2) • T (f q.1) (Matrix.of q.2) = 0
    rw [b₁ q hq hG W hW hqW hz, smul_zero]
  · show a (Matrix.of y) • T fi (Matrix.of y) = ∫ Z, a (Matrix.of y) • T (f Z) (Matrix.of y) ∂ν
    rw [c₁ ν Kp hKp hν fi y V hV hyV hyG hKV hi, integral_smul]

theorem parOK_csmul (s : ℂ) {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) :
    ParOK k ρ (fun f g => s • T f g) := parOK_smulG (smoothG_const s) hT

theorem parOK_neg {T : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (hT : ParOK k ρ T) : ParOK k ρ (fun f g => -T f g) :=
  parOK_congr (parOK_csmul (-1) hT) (fun f g => by simp)

theorem parOK_comp {T₁ T₂ : (Q.Mx k ρ → E) → Q.Mx k ρ → E} (h₁ : ParOK k ρ T₁) (h₂ : ParOK k ρ T₂) :
    ParOK k ρ (fun f => T₁ (T₂ f)) := by
  intro Par _ _ _ _ _ U₀ hU₀ f hf
  obtain ⟨a₂, b₂, c₂⟩ := h₂ Par U₀ hU₀ f hf
  obtain ⟨a₁, b₁, c₁⟩ := h₁ Par U₀ hU₀ (fun Z => T₂ (f Z)) a₂
  refine ⟨a₁, fun q hq hG W hW hqW hz => ?_, fun ν _ Kp hKp hν fi y V hV hyV hyG hKV hi => ?_⟩
  · refine b₁ q hq hG (W ∩ U₀) (hW.inter hU₀) ⟨hqW, hq⟩ (fun q' hq' hG' => ?_)
    exact b₂ q' hq'.2 hG' W hW hq'.1 hz
  · refine c₁ ν Kp hKp hν (T₂ fi) y V hV hyV hyG hKV (fun y' hy' hG' => ?_)
    exact c₂ ν Kp hKp hν fi y' V hV hy' hG' hKV hi

theorem parOK_sum {ι : Type} (s : Finset ι) {T : ι → (Q.Mx k ρ → E) → Q.Mx k ρ → E}
    (h : ∀ i ∈ s, ParOK k ρ (T i)) : ParOK k ρ (fun f g => ∑ i ∈ s, T i f g) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact parOK_congr parOK_zero (fun f g => by simp)
  | insert a s ha ih =>
    have := parOK_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact parOK_congr this (fun f g => by simp [Finset.sum_insert ha])

theorem parOK_foldr (L : List ((Q.Mx k ρ → E) → Q.Mx k ρ → E)) (hL : ∀ T ∈ L, ParOK k ρ T) :
    ParOK k ρ (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact parOK_id
  | cons T L ih =>
    exact parOK_comp (hL T List.mem_cons_self) (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))

end Ops

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
end
end
