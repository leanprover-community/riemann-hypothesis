import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import BuildAid.ForwardExisting

section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

def aff (α β γ : ℝ) (l : ℂ × ℂ) : ℂ := (α : ℂ) * l.1 + (β : ℂ) * l.2 + (γ : ℂ)

def affR (α β γ : ℝ) (x : ℝ × ℝ) : ℝ := α * x.1 + β * x.2 + γ

def chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (l : ℂ × ℂ) : ℂ × ℂ := (aff α₁ β₁ γ₁ l, aff α₂ β₂ γ₂ l)

def chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (affR α₁ β₁ γ₁ x, affR α₂ β₂ γ₂ x)

lemma aff_re (α β γ : ℝ) (l : ℂ × ℂ) : (aff α β γ l).re = affR α β γ (l.1.re, l.2.re) := by
  simp [aff, affR]

lemma aff_line (α β γ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    aff α β γ (p + τ • v) = aff α β γ p + τ * ((α : ℂ) * v.1 + (β : ℂ) * v.2) := by
  simp only [aff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma continuous_aff (α β γ : ℝ) : Continuous (aff α β γ) := by
  unfold aff; fun_prop

lemma continuous_affR (α β γ : ℝ) : Continuous (affR α β γ) := by
  unfold affR; fun_prop

lemma continuous_chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chg α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_aff _ _ _).prodMk (continuous_aff _ _ _)

lemma continuous_chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chgR α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_affR _ _ _).prodMk (continuous_affR _ _ _)

lemma differentiable_aff_line (α β γ : ℝ) (p v : ℂ × ℂ) :
    Differentiable ℂ fun τ : ℂ => aff α β γ (p + τ • v) := by
  simp only [aff_line]
  fun_prop

lemma mem_tube_chg {Ω : Set (ℝ × ℝ)} {α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ} {l : ℂ × ℂ} :
    l ∈ tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) ↔ chg α₁ β₁ γ₁ α₂ β₂ γ₂ l ∈ tube Ω := by
  simp only [tube, Set.mem_setOf_eq, Set.mem_preimage, chg, chgR, aff_re]

lemma chg_line (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    chg α₁ β₁ γ₁ α₂ β₂ γ₂ (p + τ • v) = chg α₁ β₁ γ₁ α₂ β₂ γ₂ p +
      τ • ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2) := by
  simp only [chg, aff_line]
  rfl

section Good

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma lineHol_chg {F : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hF : LineHol F (tube Ω))
    (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    LineHol (fun l => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l)) (tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω)) := by
  intro p v
  have h := hF (chg α₁ β₁ γ₁ α₂ β₂ γ₂ p)
    ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2)
  simp only [mem_tube_chg, chg_line]
  exact h

theorem TubeGood_chg {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    TubeGood (fun l g => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l) g) (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) := by
  refine ⟨fun g => lineHol_chg (hF.hol g) _ _ _ _ _ _, ?_, ?_⟩
  · have hc : Continuous fun y : (ℂ × ℂ) × T => (chg α₁ β₁ γ₁ α₂ β₂ γ₂ y.1, y.2) :=
      ((continuous_chg _ _ _ _ _ _).comp continuous_fst).prodMk continuous_snd
    refine hF.cont.comp hc.continuousOn ?_
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact ⟨mem_tube_chg.1 hl, Set.mem_univ _⟩
  · intro C hC hCc g
    obtain ⟨U, hU, M, hM⟩ := hF.bdd (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ '' C)
      (by rintro _ ⟨x, hx, rfl⟩; exact hC hx) (hCc.image (continuous_chgR _ _ _ _ _ _)) g
    refine ⟨U, hU, M, fun l hl g' hg' => hM _ ?_ g' hg'⟩
    have : (l.1.re, l.2.re) ∈ C := hl
    refine ⟨_, this, ?_⟩
    simp only [chg, chgR, aff_re]

lemma TubeGood_mono {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω Ω' : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (h : Ω' ⊆ Ω) : TubeGood F Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  refine ⟨fun g p v => ?_, hF.cont.mono (Set.prod_mono ht subset_rfl),
    fun C hC => hF.bdd C (hC.trans h)⟩
  exact (hF.hol g p v).mono fun τ hτ => ht hτ

structure Fac (A : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol A (tube Ω)
  cont : ContinuousOn A (tube Ω)
  bdd : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C, ‖A l‖ ≤ M

lemma exists_bounds {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hne : C.Nonempty) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : ∃ x ∈ C, ∃ y ∈ C, ∀ u ∈ C, f x ≤ f u ∧ f u ≤ f y := by
  obtain ⟨x, hx, hx'⟩ := hC.exists_isMinOn hne hf.continuousOn
  obtain ⟨y, hy, hy'⟩ := hC.exists_isMaxOn hne hf.continuousOn
  exact ⟨x, hx, y, hy, fun u hu => ⟨hx' hu, hy' hu⟩⟩

theorem Fac_left {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) (α β γ : ℝ) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, affR α β γ x < a) : Fac (fun l => f (aff α β γ l)) Ω := by
  have hre : ∀ l ∈ tube Ω, (aff α β γ l).re < a := fun l hl => by
    rw [aff_re]; exact h _ hl
  refine ⟨fun p v => ?_, ?_, fun C hC hCc => ?_⟩
  · refine hf.1.comp (differentiable_aff_line α β γ p v).differentiableOn ?_
    intro τ hτ
    exact hre _ hτ
  · exact hf.1.continuousOn.comp (continuous_aff _ _ _).continuousOn fun l hl => hre l hl
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, hy, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y) (h y (hC hy))
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

theorem Fac_strip {f : ℂ → X} (hf : StripEntire f) (α β γ : ℝ) (Ω : Set (ℝ × ℝ)) :
    Fac (fun l => f (aff α β γ l)) Ω := by
  refine ⟨fun p v => ?_, ?_, fun C _ hCc => ?_⟩
  · exact (hf.1.comp (differentiable_aff_line α β γ p v)).differentiableOn
  · exact (hf.1.continuous.comp (continuous_aff _ _ _)).continuousOn
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, -, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y)
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2


theorem Fac_smul {f : ℂ × ℂ → ℂ} {A : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hA : Fac A Ω) :
    Fac (fun l => f l • A l) Ω := by
  refine ⟨fun p v => (hf.hol p v).smul (hA.hol p v), hf.cont.smul hA.cont, fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => ?_⟩
  rw [norm_smul]
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem Fac_mul {f f' : ℂ × ℂ → ℂ} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hf' : Fac f' Ω) :
    Fac (fun l => f l * f' l) Ω :=
  Fac_smul hf hf'

theorem TubeGood_smul {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    {f : ℂ × ℂ → ℂ} (hf : Fac f Ω) (hF : TubeGood F Ω) :
    TubeGood (fun l g => f l • F l g) Ω := by
  refine ⟨fun g p v => (hf.hol p v).smul (hF.hol g p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.smul (hf.cont.comp continuousOn_fst ?_) hF.cont
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
    obtain ⟨U, hU, M₂, h₂⟩ := hF.bdd C hC hCc g
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => ?_⟩
    rw [norm_smul]
    exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl g' hg').trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Good

section Comp

variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]

theorem Fac_comp {A : ℂ × ℂ → E₂ →L[ℂ] E₃} {B : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)}
    (hA : Fac A Ω) (hB : Fac B Ω) : Fac (fun l => (A l).comp (B l)) Ω := by
  refine ⟨fun p v => (hA.hol p v).clm_comp (hB.hol p v), hA.cont.clm_comp hB.cont,
    fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hA.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hB.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem TubeGood_comp {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → E₂ →L[ℂ] E₃}
    {A : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)} (hF : TubeGood F Ω) (hA : Fac A Ω) :
    TubeGood (fun l g => (F l g).comp (A l)) Ω := by
  refine ⟨fun g p v => (hF.hol g p v).clm_comp (hA.hol p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.clm_comp hF.cont (hA.cont.comp continuousOn_fst ?_)
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨U, hU, M₁, h₁⟩ := hF.bdd C hC hCc g
    obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' =>
      (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
    exact mul_le_mul ((h₁ l hl g' hg').trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Comp

end GlobalTheory.CompanionTheory.RgEisGal
end
end

section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

def coneI (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 ∧ r < x.2 + x.1}

def coneC (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 - x.1 ∧ r < x.2 + x.1}

def coneA (r : ℝ) : Set (ℝ × ℝ) := {x | r < x.2 - x.1 ∧ r < x.2}

abbrev yv (N : ℝ) : ℂ × ℂ → ℂ := aff 1 1 (1 - N)

abbrev zv (N : ℝ) : ℂ × ℂ → ℂ := aff 1 2 (1 - N)

abbrev nz (N : ℝ) : ℂ × ℂ → ℂ := aff (-1) 0 N

abbrev mc (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 1 1 (1 - N) 0 1 1

abbrev ma (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 1 2 (1 - N) 0 1 1

abbrev mb (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg 0 1 0 (-1) (-1) (2 * N - 1)

abbrev ml (N : ℝ) : ℂ × ℂ → ℂ × ℂ := chg (-1) 0 N 0 (-1) (N - 1)

def Om1 (N r : ℝ) : Set (ℝ × ℝ) := chgR 1 1 (1 - N) 0 1 1 ⁻¹' coneC r

def Om2 (N r : ℝ) : Set (ℝ × ℝ) := chgR 1 2 (1 - N) 0 1 1 ⁻¹' coneA r

def Om3 (N r : ℝ) : Set (ℝ × ℝ) := chgR 0 1 0 (-1) (-1) (2 * N - 1) ⁻¹' coneC r

def Om4 (N r : ℝ) : Set (ℝ × ℝ) := chgR (-1) 0 N 0 (-1) (N - 1) ⁻¹' coneI r ∩ {x | x.1 < 1 / 2}

def chamberPairOneTwo (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 < -M ∧ M < x.1 + x.2}

def chamberPairTwoThree (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 + x.2 < -M ∧ M < x.1 + 2 * x.2}

def chamberPairThreeFour (M : ℝ) : Set (ℝ × ℝ) := {x | x.1 + 2 * x.2 < -M ∧ M < x.2}

def chamberPairFourLast (M : ℝ) : Set (ℝ × ℝ) := {x | x.2 < -M ∧ x.1 < -M}

lemma mem_Om1 {N r : ℝ} {x : ℝ × ℝ} : x ∈ Om1 N r ↔ r < N - x.1 ∧ r < x.1 + 2 * x.2 + 2 - N := by
  simp only [Om1, Set.mem_preimage, chgR, affR, coneC, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma mem_Om2 {N r : ℝ} {x : ℝ × ℝ} : x ∈ Om2 N r ↔ r < N - x.1 - x.2 ∧ r < x.2 + 1 := by
  simp only [Om2, Set.mem_preimage, chgR, affR, coneA, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma mem_Om3 {N r : ℝ} {x : ℝ × ℝ} :
    x ∈ Om3 N r ↔ r < 2 * N - 1 - x.1 - 2 * x.2 ∧ r < 2 * N - 1 - x.1 := by
  simp only [Om3, Set.mem_preimage, chgR, affR, coneC, Set.mem_setOf_eq]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma mem_Om4 {N r : ℝ} {x : ℝ × ℝ} :
    x ∈ Om4 N r ↔ (r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1) ∧ x.1 < 1 / 2 := by
  simp only [Om4, Set.mem_inter_iff, Set.mem_preimage, chgR, affR, coneI, Set.mem_setOf_eq]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> refine ⟨⟨?_, ?_⟩, h₃⟩ <;> linarith

lemma isOpen_hp (α β γ r : ℝ) : IsOpen {x : ℝ × ℝ | r < affR α β γ x} :=
  isOpen_lt continuous_const (continuous_affR α β γ)

lemma convex_hp (α β γ r : ℝ) : Convex ℝ {x : ℝ × ℝ | r < affR α β γ x} := by
  have hl : IsLinearMap ℝ (fun x : ℝ × ℝ => α * x.1 + β * x.2) :=
    ⟨fun a b => by simp only [Prod.fst_add, Prod.snd_add]; ring,
      fun c a => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring⟩
  have h := convex_halfSpace_gt hl (r - γ)
  have e : {x : ℝ × ℝ | r < affR α β γ x} = {w : ℝ × ℝ | r - γ < α * w.1 + β * w.2} := by
    ext x
    simp only [Set.mem_setOf_eq, affR]
    constructor <;> intro h' <;> linarith
  rw [e]
  exact h

lemma open_convex2 {Ω : Set (ℝ × ℝ)} (α₁ β₁ γ₁ α₂ β₂ γ₂ r : ℝ)
    (h : ∀ x, x ∈ Ω ↔ r < affR α₁ β₁ γ₁ x ∧ r < affR α₂ β₂ γ₂ x) : IsOpen Ω ∧ Convex ℝ Ω := by
  have e : Ω = {x | r < affR α₁ β₁ γ₁ x} ∩ {x | r < affR α₂ β₂ γ₂ x} := by
    ext x; exact h x
  rw [e]
  exact ⟨(isOpen_hp _ _ _ _).inter (isOpen_hp _ _ _ _), (convex_hp _ _ _ _).inter (convex_hp _ _ _ _)⟩

lemma oc_coneI (r : ℝ) : IsOpen (coneI r) ∧ Convex ℝ (coneI r) :=
  open_convex2 0 1 0 1 1 0 r fun x => by simp [coneI, affR, add_comm]

lemma isOpen_convex_Om1 (N r : ℝ) : IsOpen (Om1 N r) ∧ Convex ℝ (Om1 N r) :=
  open_convex2 (-1) 0 N 1 2 (2 - N) r fun x => by
    rw [mem_Om1]; simp only [affR]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma isOpen_convex_Om2 (N r : ℝ) : IsOpen (Om2 N r) ∧ Convex ℝ (Om2 N r) :=
  open_convex2 (-1) (-1) N 0 1 1 r fun x => by
    rw [mem_Om2]; simp only [affR]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma isOpen_convex_Om3 (N r : ℝ) : IsOpen (Om3 N r) ∧ Convex ℝ (Om3 N r) :=
  open_convex2 (-1) (-2) (2 * N - 1) (-1) 0 (2 * N - 1) r fun x => by
    rw [mem_Om3]; simp only [affR]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

lemma isOpen_convex_Om4 (N r : ℝ) : IsOpen (Om4 N r) ∧ Convex ℝ (Om4 N r) := by
  have h := open_convex2 (Ω := {x : ℝ × ℝ | r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1})
    0 (-1) (N - 1) (-1) (-1) (2 * N - 1) r fun x => by
      simp only [affR, Set.mem_setOf_eq]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have h' := (isOpen_hp (-1) 0 (1 / 2) 0)
  have h'' := (convex_hp (-1) 0 (1 / 2) 0)
  have e : Om4 N r = {x : ℝ × ℝ | r < N - 1 - x.2 ∧ r < 2 * N - 1 - x.2 - x.1} ∩
      {x | 0 < affR (-1) 0 (1 / 2) x} := by
    ext x
    rw [mem_Om4]
    simp only [affR, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, by linarith⟩
    · rintro ⟨h₁, h₂⟩; exact ⟨h₁, by linarith⟩
  rw [e]
  exact ⟨h.1.inter h', h.2.inter h''⟩

lemma isOpen_chamberPairOneTwo (M : ℝ) : IsOpen (chamberPairOneTwo M) :=
  (open_convex2 (-1) 0 0 1 1 0 M fun x => by
    simp only [chamberPairOneTwo, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_V12 (M : ℝ) : IsOpen (chamberPairTwoThree M) :=
  (open_convex2 (-1) (-1) 0 1 2 0 M fun x => by
    simp only [chamberPairTwoThree, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_V23 (M : ℝ) : IsOpen (chamberPairThreeFour M) :=
  (open_convex2 (-1) (-2) 0 0 1 0 M fun x => by
    simp only [chamberPairThreeFour, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_V34 (M : ℝ) : IsOpen (chamberPairFourLast M) :=
  (open_convex2 0 (-1) 0 (-1) 0 0 M fun x => by
    simp only [chamberPairFourLast, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma nonempty_V01 (M : ℝ) : (chamberPairOneTwo M).Nonempty :=
  ⟨(-M - 1, 2 * M + 2), by simp only [chamberPairOneTwo, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma nonempty_V12 (M : ℝ) : (chamberPairTwoThree M).Nonempty :=
  ⟨(-3 * M - 3, 2 * M + 2), by simp only [chamberPairTwoThree, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma nonempty_V23 (M : ℝ) : (chamberPairThreeFour M).Nonempty :=
  ⟨(-3 * M - 3, M + 1), by simp only [chamberPairThreeFour, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma nonempty_V34 (M : ℝ) : (chamberPairFourLast M).Nonempty :=
  ⟨(-M - 1, -M - 1), by simp only [chamberPairFourLast, Set.mem_setOf_eq]; constructor <;> linarith⟩

lemma exists_midpoint (N r : ℝ) (x : ℝ × ℝ) :
    ∃ a ∈ coneI r, ∃ b ∈ Om3 N r, x = midpoint ℝ a b := by
  obtain ⟨u, v⟩ := x
  set B : ℝ := |r| + 1 with hB
  set A : ℝ := |r| + |r + 1 - 2 * N + 2 * u| + |r + 1 - 2 * N + 2 * u + 4 * v - 2 * B| + 1 with hA
  have h₀ := le_abs_self r
  have h₁ := le_abs_self (r + 1 - 2 * N + 2 * u)
  have h₂ := le_abs_self (r + 1 - 2 * N + 2 * u + 4 * v - 2 * B)
  have h₃ := abs_nonneg r
  have h₄ := abs_nonneg (r + 1 - 2 * N + 2 * u)
  have h₅ := abs_nonneg (r + 1 - 2 * N + 2 * u + 4 * v - 2 * B)
  refine ⟨(A, B), ?_, (2 * u - A, 2 * v - B), ?_, ?_⟩
  · simp only [coneI, Set.mem_setOf_eq]
    constructor <;> linarith
  · rw [mem_Om3]
    simp only
    constructor <;> linarith
  · rw [midpoint_eq_smul_add]
    ext <;> simp <;> ring

lemma chain4 (hTC : TubeChain) {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    {T : Type} [TopologicalSpace T] [FirstCountableTopology T] {Ω₀ Ω₁ Ω₂ Ω₃ : Set (ℝ × ℝ)}
    {F₀ F₁ F₂ F₃ : ℂ × ℂ → T → X}
    (h₀ : IsOpen Ω₀ ∧ Convex ℝ Ω₀ ∧ TubeGood F₀ Ω₀) (h₁ : IsOpen Ω₁ ∧ Convex ℝ Ω₁ ∧ TubeGood F₁ Ω₁)
    (h₂ : IsOpen Ω₂ ∧ Convex ℝ Ω₂ ∧ TubeGood F₂ Ω₂) (h₃ : IsOpen Ω₃ ∧ Convex ℝ Ω₃ ∧ TubeGood F₃ Ω₃)
    (j₀ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₀ ∩ Ω₁ ∧ ∀ l ∈ tube V, ∀ g, F₀ l g = F₁ l g)
    (j₁ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₁ ∩ Ω₂ ∧ ∀ l ∈ tube V, ∀ g, F₁ l g = F₂ l g)
    (j₂ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Ω₂ ∩ Ω₃ ∧ ∀ l ∈ tube V, ∀ g, F₂ l g = F₃ l g)
    (mid : ∀ x : ℝ × ℝ, ∃ a ∈ Ω₀, ∃ b ∈ Ω₃, x = midpoint ℝ a b) :
    ∃ Φ : ℂ × ℂ → T → X, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube Ω₀, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₀ l g) ∧
      ∀ l ∈ tube Ω₃, ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) • F₃ l g := by
  obtain ⟨Φ, hΦ, hE⟩ := hTC X T 3 ![Ω₀, Ω₁, Ω₂, Ω₃] ![F₀, F₁, F₂, F₃]
    (by intro i; fin_cases i; exacts [h₀, h₁, h₂, h₃])
    (by intro i; fin_cases i; exacts [j₀, j₁, j₂])
    (by intro x; obtain ⟨a, ha, b, hb, e⟩ := mid x; exact ⟨0, 3, a, ha, b, hb, e⟩)
  exact ⟨Φ, hΦ, hE 0, hE 3⟩

section Fac

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma Fac_left_fst {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, x.1 < a) : Fac (fun l => f l.1) Ω := by
  have := Fac_left hf 1 0 0 (Ω := Ω) (fun x hx => by simpa [affR] using h x hx)
  simpa [aff] using this

lemma Fac_left_snd {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, x.2 < a) : Fac (fun l => f l.2) Ω := by
  have := Fac_left hf 0 1 0 (Ω := Ω) (fun x hx => by simpa [affR] using h x hx)
  simpa [aff] using this

lemma Fac_strip_snd {f : ℂ → X} (hf : StripEntire f) (Ω : Set (ℝ × ℝ)) : Fac (fun l => f l.2) Ω := by
  have := Fac_strip hf 0 1 0 Ω
  simpa [aff] using this

end Fac

lemma lineHol_exp (U : Set (ℂ × ℂ)) : LineHol (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2)) U := by
  intro p v
  apply Differentiable.differentiableOn
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  fun_prop

section Core

variable {T : Type} [TopologicalSpace T] [FirstCountableTopology T]
  {ES EA EB W : Type} [NormedAddCommGroup ES] [NormedSpace ℂ ES] [NormedAddCommGroup EA]
  [NormedSpace ℂ EA] [NormedAddCommGroup EB] [NormedSpace ℂ EB] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]

theorem core (hId : IdTube) (hTC : TubeChain) (N R : ℝ) (hR : |N| + 1 ≤ R)
    {o₀ : ℂ × ℂ → T → ES →L[ℂ] W} {oc oa : ℂ × ℂ → T → EB →L[ℂ] W} {ob ol : ℂ × ℂ → T → EA →L[ℂ] W}
    (g₀ : TubeGood o₀ (coneI (10 * R))) (gc : TubeGood oc (coneC (10 * R)))
    (ga : TubeGood oa (coneA (10 * R))) (gb : TubeGood ob (coneC (10 * R)))
    (gl : TubeGood ol (coneI (10 * R)))
    {Dc Da Db d : ℂ → ℂ} (hDc : StripEntire Dc) (hDa : StripEntire Da) (hDb : StripEntire Db)
    (hd : StripEntire d)
    {Op₀ O : ℂ → ES →L[ℂ] EB} {Opc : ℂ → EB →L[ℂ] EB} {Opa : ℂ → EB →L[ℂ] EA} {Opb : ℂ → EA →L[ℂ] EA}
    (hOp₀ : LeftGood Op₀ (-R)) (hO : LeftGood O (1 / 2)) (hOpc : LeftGood Opc (-R))
    (hOpa : LeftGood Opa (-R)) (hOpb : LeftGood Opb (-R))
    (J₀ : ∀ l ∈ tube (chamberPairOneTwo (100 * R)), ∀ g, Dc (yv N l) • o₀ l g = (oc (mc N l) g).comp (Op₀ l.1))
    (J₁ : ∀ l ∈ tube (chamberPairTwoThree (100 * R)), ∀ g,
      Da (zv N l) • oc (mc N l) g = (oa (ma N l) g).comp (Opc (yv N l)))
    (J₂ : ∀ l ∈ tube (chamberPairThreeFour (100 * R)), ∀ g,
      Db l.2 • oa (ma N l) g = (ob (mb N l) g).comp (Opa (zv N l)))
    (J₃ : ∀ l ∈ tube (chamberPairFourLast (100 * R)), ∀ g,
      (-d (nz N l)) • (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) =
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1))))) :
    ∃ Φ : ℂ × ℂ → T → ES →L[ℂ] W, TubeGood Φ Set.univ ∧
      (∀ l ∈ tube (coneI (10 * R)), ∀ g, Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g) ∧
      ∀ l ∈ tube (Om4 N (10 * R)), ∀ g, (-d (nz N l)) • Φ l g = Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
        (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))) := by
  have hN := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hN₁ := hN.1
  have hN₂ := hN.2
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]

  set F₀ : ℂ × ℂ → T → ES →L[ℂ] W := fun l g => (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g with hF₀
  set F₁ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1) with hF₁
  set F₂ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1)) with hF₂
  set F₃ : ℂ × ℂ → T → ES →L[ℂ] W :=
    fun l g => (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) with hF₃
  have t₀ : TubeGood F₀ (coneI (10 * R)) :=
    TubeGood_smul (Fac_mul (Fac_mul (Fac_strip hDc _ _ _ _) (Fac_strip hDa _ _ _ _))
      (Fac_strip_snd hDb _)) g₀
  have t₁ : TubeGood F₁ (Om1 N (10 * R)) :=
    TubeGood_smul (Fac_mul (Fac_strip hDa _ _ _ _) (Fac_strip_snd hDb _))
      (TubeGood_comp (TubeGood_chg gc _ _ _ _ _ _)
        (Fac_left_fst hOp₀ fun x hx => by have := (mem_Om1.1 hx).1; linarith))
  have t₂ : TubeGood F₂ (Om2 N (10 * R)) :=
    TubeGood_smul (Fac_strip_snd hDb _)
      (TubeGood_comp (TubeGood_chg ga _ _ _ _ _ _)
        (Fac_comp
          (Fac_left hOpc _ _ _ fun x hx => by
            have := (mem_Om2.1 hx).1
            simp only [affR]; linarith)
          (Fac_left_fst hOp₀ fun x hx => by
            have := mem_Om2.1 hx
            linarith [this.1, this.2])))
  have t₃ : TubeGood F₃ (Om3 N (10 * R)) :=
    TubeGood_comp (TubeGood_chg gb _ _ _ _ _ _)
      (Fac_comp
        (Fac_left hOpa _ _ _ fun x hx => by
          have := (mem_Om3.1 hx).1
          simp only [affR]; linarith)
        (Fac_comp
          (Fac_left hOpc _ _ _ fun x hx => by
            have := mem_Om3.1 hx
            simp only [affR]; linarith [this.1, this.2])
          (Fac_left_fst hOp₀ fun x hx => by
            have := (mem_Om3.1 hx).2
            linarith)))
  have j₀ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ coneI (10 * R) ∩ Om1 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₀ l g = F₁ l g := by
    refine ⟨chamberPairOneTwo (100 * R), isOpen_chamberPairOneTwo _, nonempty_V01 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨?_, mem_Om1.2 ⟨?_, ?_⟩⟩
      · simp only [coneI, Set.mem_setOf_eq]
        constructor <;> linarith
      all_goals linarith
    · intro l hl g
      change (Dc (yv N l) * Da (zv N l) * Db l.2) • o₀ l g =
        (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1)
      rw [← J₀ l hl g, smul_smul]
      congr 1
      ring
  have j₁ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Om1 N (10 * R) ∩ Om2 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₁ l g = F₂ l g := by
    refine ⟨chamberPairTwoThree (100 * R), isOpen_V12 _, nonempty_V12 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨mem_Om1.2 ⟨?_, ?_⟩, mem_Om2.2 ⟨?_, ?_⟩⟩ <;> linarith
    · intro l hl g
      change (Da (zv N l) * Db l.2) • (oc (mc N l) g).comp (Op₀ l.1) =
        Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1))
      rw [← ContinuousLinearMap.comp_assoc _ (Opc (yv N l)), ← J₁ l hl g,
        ContinuousLinearMap.smul_comp, smul_smul]
      congr 1
      ring
  have j₂ : ∃ V : Set (ℝ × ℝ), IsOpen V ∧ V.Nonempty ∧ V ⊆ Om2 N (10 * R) ∩ Om3 N (10 * R) ∧
      ∀ l ∈ tube V, ∀ g, F₂ l g = F₃ l g := by
    refine ⟨chamberPairThreeFour (100 * R), isOpen_V23 _, nonempty_V23 _, ?_, ?_⟩
    · rintro x ⟨h₁, h₂⟩
      refine ⟨mem_Om2.2 ⟨?_, ?_⟩, mem_Om3.2 ⟨?_, ?_⟩⟩ <;> linarith
    · intro l hl g
      change Db l.2 • (oa (ma N l) g).comp ((Opc (yv N l)).comp (Op₀ l.1)) =
        (ob (mb N l) g).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1)))
      rw [← ContinuousLinearMap.comp_assoc _ (Opa (zv N l)), ← J₂ l hl g,
        ContinuousLinearMap.smul_comp]
  obtain ⟨Φ, hΦ, e₀, e₃⟩ := chain4 hTC (F₀ := F₀) (F₁ := F₁) (F₂ := F₂) (F₃ := F₃)
    ⟨(oc_coneI _).1, (oc_coneI _).2, t₀⟩ ⟨(isOpen_convex_Om1 N _).1, (isOpen_convex_Om1 N _).2, t₁⟩
    ⟨(isOpen_convex_Om2 N _).1, (isOpen_convex_Om2 N _).2, t₂⟩ ⟨(isOpen_convex_Om3 N _).1, (isOpen_convex_Om3 N _).2, t₃⟩
    j₀ j₁ j₂ (exists_midpoint N _)
  refine ⟨Φ, hΦ, e₀, fun l hl g => ?_⟩

  have hsub : chamberPairFourLast (100 * R) ⊆ Om4 N (10 * R) ∩ Om3 N (10 * R) := by
    rintro x ⟨h₁, h₂⟩
    refine ⟨mem_Om4.2 ⟨⟨?_, ?_⟩, ?_⟩, mem_Om3.2 ⟨?_, ?_⟩⟩ <;> linarith
  have hneg : StripEntire fun z => -d z :=
    ⟨hd.1.neg, fun b c => by
      obtain ⟨M, hM⟩ := hd.2 b c
      exact ⟨M, fun z h₁ h₂ => by simpa using hM z h₁ h₂⟩⟩
  have hleft : LineHol (fun l : ℂ × ℂ => (-d (nz N l)) • Φ l g) (tube (Om4 N (10 * R))) :=
    (TubeGood_smul (Fac_strip hneg (-1) 0 N _) (TubeGood_mono hΦ (Set.subset_univ _))).hol g
  have hcomp : TubeGood (fun (l : ℂ × ℂ) g => (ol (ml N l) g).comp
      ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1))))) (Om4 N (10 * R)) :=
    TubeGood_comp (TubeGood_mono (TubeGood_chg gl _ _ _ _ _ _) fun x hx => hx.1)
      (Fac_comp
        (Fac_left_snd hOpb fun x hx => by
          have := (mem_Om4.1 hx).1.1
          linarith)
        (Fac_comp
          (Fac_left hOpa _ _ _ fun x hx => by
            have := mem_Om4.1 hx
            simp only [affR]; linarith [this.1.1, this.2])
          (Fac_comp
            (Fac_left hOpc _ _ _ fun x hx => by
              have := mem_Om4.1 hx
              simp only [affR]; linarith [this.1.1, this.2])
            (Fac_left_fst hO fun x hx => (mem_Om4.1 hx).2))))
  have hright : LineHol (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2) •
      (ol (ml N l) g).comp ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))))
      (tube (Om4 N (10 * R))) :=
    fun p v => (lineHol_exp _ p v).smul (hcomp.hol g p v)
  refine hId (ES →L[ℂ] W) (Om4 N (10 * R)) (chamberPairFourLast (100 * R)) _ _ (isOpen_convex_Om4 N _).1 (isOpen_convex_Om4 N _).2
    (isOpen_V34 _) (nonempty_V34 _) (fun x hx => (hsub hx).1) hleft hright ?_ hl
  intro l' hl'
  have e := e₃ l' (show (l'.1.re, l'.2.re) ∈ Om3 N (10 * R) from (hsub hl').2) g
  simp only [e]
  rw [smul_comm]
  exact congrArg _ (J₃ l' hl' g)

end Core

end GlobalTheory.CompanionTheory.RgEisGal
end
end

section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

section Slice

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma Fac_const (c : X) (Ω : Set (ℝ × ℝ)) : Fac (fun _ => c) Ω :=
  ⟨fun _ _ => differentiableOn_const c, continuousOn_const, fun _ _ _ => ⟨‖c‖, fun _ _ => le_rfl⟩⟩

lemma Fac_exp (Ω : Set (ℝ × ℝ)) : Fac (fun l : ℂ × ℂ => Complex.exp (l.1 ^ 2 + l.2 ^ 2)) Ω := by
  refine ⟨lineHol_exp _, by fun_prop, fun C _ hCc => ?_⟩
  have hc : Continuous fun x : ℝ × ℝ => x.1 ^ 2 + x.2 ^ 2 := by fun_prop
  obtain ⟨M, hM⟩ := (hCc.image hc).bddAbove
  refine ⟨Real.exp M, fun l hl => ?_⟩
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 (le_trans ?_ (hM ⟨_, hl, rfl⟩))
  simp only [pow_two, Complex.add_re, Complex.mul_re]
  nlinarith [mul_self_nonneg l.1.im, mul_self_nonneg l.2.im]

lemma line_zero (τ : ℂ) : (0 : ℂ × ℂ) + τ • ((0 : ℂ), (1 : ℂ)) = (0, τ) := by
  ext <;> simp

lemma slice_mem_tube {C : Set ℝ} {y : ℂ} (h : y.re ∈ C) :
    ((0 : ℂ), y) ∈ tube (({0} : Set ℝ) ×ˢ C) := by
  simpa [tube] using h

lemma leftGood_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} {a : ℝ} (hA : Fac A {x | x.2 < a})
    (h : ∀ y, f y = A (0, y)) : LeftGood f a := by
  refine ⟨?_, fun b c hc => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube {x : ℝ × ℝ | x.2 < a}} = {z | z.re < a} := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c)
      (by rintro x ⟨-, hx⟩; exact lt_of_le_of_lt hx.2 hc)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩

lemma stripEntire_of_fac {f : ℂ → X} {A : ℂ × ℂ → X} (hA : Fac A Set.univ)
    (h : ∀ y, f y = A (0, y)) : StripEntire f := by
  refine ⟨?_, fun b c => ?_⟩
  · have h₁ := hA.hol 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    have e : f = fun τ => A (0, τ) := funext h
    rw [e]
    exact differentiableOn_univ.1 h₁
  · obtain ⟨M, hM⟩ := hA.bdd (({0} : Set ℝ) ×ˢ Set.Icc b c) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc)
    exact ⟨M, fun z h₁ h₂ => by rw [h]; exact hM _ (slice_mem_tube ⟨h₁, h₂⟩)⟩

lemma slice_good {T : Type} [TopologicalSpace T] {Φ : ℂ × ℂ → T → X} (hΦ : TubeGood Φ Set.univ) :
    (∀ g, Differentiable ℂ fun y : ℂ => Φ (0, y) g) ∧
    (Continuous fun y : ℂ × T => Φ (0, y.1) y.2) ∧
    ∀ (b a : ℝ) (g : T), ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g' ∈ U,
      ‖Φ (0, z) g'‖ ≤ M := by
  refine ⟨fun g => ?_, ?_, fun b a g => ?_⟩
  · have h₁ := hΦ.hol g 0 (0, 1)
    simp only [line_zero] at h₁
    have hs : {τ : ℂ | ((0 : ℂ), τ) ∈ tube (Set.univ : Set (ℝ × ℝ))} = Set.univ := by
      ext z; simp [tube]
    rw [hs] at h₁
    exact differentiableOn_univ.1 h₁
  · have hc : Continuous fun y : ℂ × T => (((0 : ℂ), y.1), y.2) := by fun_prop
    have := hΦ.cont.comp hc.continuousOn (s := Set.univ) (fun y _ => by simp [tube])
    exact continuousOn_univ.1 this
  · obtain ⟨U, hU, M, hM⟩ := hΦ.bdd (({0} : Set ℝ) ×ˢ Set.Icc b a) (Set.subset_univ _)
      (isCompact_singleton.prod isCompact_Icc) g
    exact ⟨U, hU, M, fun z h₁ h₂ g' hg' => hM _ (slice_mem_tube ⟨h₁, h₂⟩) g' hg'⟩

end Slice

lemma exists_ne_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h₁ : ∃ z, f z ≠ 0) (h₂ : ∃ z, g z ≠ 0) : ∃ z, f z * g z ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z₀, hz₀⟩ := h₁
  obtain ⟨z₁, hz₁⟩ := h₂
  have hev : ∀ᶠ z in 𝓝 z₀, f z ≠ 0 := hf.continuous.continuousAt.eventually_ne hz₀
  have hg0 : g =ᶠ[𝓝 z₀] 0 :=
    hev.mono fun z hz => (mul_eq_zero.1 (hcon z)).resolve_left hz
  have hga : AnalyticOnNhd ℂ g Set.univ := fun z _ => hg.analyticAt z
  exact hz₁ (hga.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₀) hg0 (Set.mem_univ z₁))

lemma exists_ne_aff {f : ℂ → ℂ} (h : ∃ z, f z ≠ 0) (α β γ : ℝ) (hβ : β ≠ 0) :
    ∃ y : ℂ, f (aff α β γ (0, y)) ≠ 0 := by
  obtain ⟨z, hz⟩ := h
  have hβ' : (β : ℂ) ≠ 0 := by exact_mod_cast hβ
  refine ⟨(z - γ) / β, ?_⟩
  have e : aff α β γ (0, (z - γ) / (β : ℂ)) = z := by
    simp only [aff]
    field_simp
    ring
  rwa [e]

lemma ex_bounds (u R : ℝ) :
    ∃ m M : ℝ, m ≤ u ∧ m ≤ -2 * R ∧ (m = u ∨ m = -2 * R) ∧ u ≤ M ∧ R ≤ M ∧ (M = u ∨ M = R) :=
  ⟨min u (-2 * R), max u R, min_le_left _ _, min_le_right _ _, min_choice _ _, le_max_left _ _,
    le_max_right _ _, max_choice _ _⟩

section Conds

variable {G : Type} [Group G]

lemma conv_congr {Γ P : Subgroup G} {f f' : G → ℝ} (h : Conv Γ P f') (e : ∀ g, f g = f' g) :
    Conv Γ P f := by
  have : f = f' := funext e
  rwa [this]

variable {Γ A B : Subgroup G} {a b h : G → ℝ} {N R Rw : ℝ}

lemma cond_first (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneI (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * a g + t * h g) ∧
        Conv Γ B fun g => (h g + N * b g) - q * b g + t * h g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · exact conv_congr (hA (M + 1) t (by linarith) (by linarith [ht'.1])) fun g => rfl
  · refine conv_congr (hB (N - (m - 1)) (1 + t - N + (m - 1)) (by linarith [hN'.1]) ?_)
      fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1, hN'.2]

lemma cond_c (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ B (fun g => p * (-b g) + t * (h g + b g)) ∧
        Conv Γ B fun g => (-b g) - q * (-b g) + t * (h g + b g) := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hB (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hB (t - 1 + (m - 1)) (1 - (m - 1)) ?_ (by linarith)) fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1]

lemma cond_a (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g)
    (hB : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g) :
    ∀ x ∈ coneA (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ B (fun g => p * b g + t * h g) ∧
        Conv Γ A fun g => (N * a g - h g) - q * a g + t * h g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hB (M + 1) (t - (M + 1)) (by linarith) ?_) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · exact conv_congr (hA (N - (m - 1)) (t - 1) (by linarith [hN'.1]) (by linarith [ht'.1]))
      fun g => by ring

lemma cond_b (hN : |N| + 1 ≤ R) (hw : Rw ≤ R)
    (hA : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g) :
    ∀ x ∈ coneC (10 * R), ∃ p q ε : ℝ, 0 < ε ∧ Rw < p ∧ q < -Rw ∧ q < x.1 ∧ x.1 < p ∧ ∀ t : ℝ,
      |t - x.2| ≤ ε → Conv Γ A (fun g => p * (h g - a g) + t * a g) ∧
        Conv Γ A fun g => ((N - 1) * (h g - a g)) - q * (h g - a g) + t * a g := by
  rintro x ⟨h₁, h₂⟩
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hR1 : 1 ≤ R := by linarith [abs_nonneg N]
  obtain ⟨m, M, m₁, m₂, m₃, M₁, M₂, M₃⟩ := ex_bounds x.1 R
  refine ⟨M + 1, m - 1, 1, one_pos, by linarith, by linarith, by linarith, by linarith,
    fun t ht => ?_⟩
  have ht' := abs_le.1 ht
  constructor
  · refine conv_congr (hA (t - (M + 1)) (M + 1) ?_ (by linarith)) fun g => by ring
    rcases M₃ with e | e <;> linarith [ht'.1]
  · refine conv_congr (hA (t - N + 1 + (m - 1)) (N - 1 - (m - 1)) ?_ (by linarith [hN'.1]))
      fun g => by ring
    rcases m₃ with e | e <;> linarith [ht'.1, hN'.2]

end Conds

section Series

variable {G : Type} [Group G]

lemma tsum_cos_inf {X : Type} [AddCommMonoid X] [TopologicalSpace X] (Γ S : Subgroup G)
    (f : G → X) : ∑' r : Cos (Γ ⊓ S) Γ, f (rep r) = ∑' q : Cos S Γ, f (rep q) := by
  have e : (Γ ⊓ S).subgroupOf Γ = S.subgroupOf Γ := Subgroup.inf_subgroupOf_left S Γ
  have key : ∀ U V : Subgroup Γ, U = V →
      ∑' r : Quotient (QuotientGroup.rightRel U), f (Quotient.out r).1 =
        ∑' q : Quotient (QuotientGroup.rightRel V), f (Quotient.out q).1 := by
    rintro U _ rfl
    rfl
  exact key _ _ e

variable {L W : Type} [NormedAddCommGroup L] [NormedSpace ℂ L] [NormedAddCommGroup W]
  [NormedSpace ℂ W] [CompleteSpace W]

lemma outer_apply {Γ Δ : Subgroup G} (ξ : G → ℝ) (H : ℂ → G → L →L[ℂ] W) (l : ℂ × ℂ) (g : G)
    (hs : Summable fun r : Cos Δ Γ => ‖Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)‖)
    (w : L) : outer Γ Δ ξ H l g w =
      ∑' r : Cos Δ Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w :=
  (ContinuousLinearMap.apply ℂ W w).map_tsum hs.of_norm

end Series

section Eis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]

lemma eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G) (s : ℂ)
    (w : W) : eis Γ K P c ρ Λ g (s • w) = s • eis Γ K P c ρ Λ g w := by
  simp only [eis, map_smul]
  rw [← tsum_const_smul'' s]
  congr 1
  ext q
  rw [smul_comm]

end Eis

end GlobalTheory.CompanionTheory.RgEisGal
end
end

section
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

section Help

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W]
  [NormedSpace ℂ W]

lemma LeftGood_mono {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {f : ℂ → X} {a a' : ℝ}
    (hf : LeftGood f a) (h : a' ≤ a) : LeftGood f a' :=
  ⟨hf.1.mono fun _ hz => lt_of_lt_of_le hz h, fun b c hc => hf.2 b c (lt_of_lt_of_le hc h)⟩

lemma IsHt_restrict {Γ K P Q : Subgroup G} {η : G → ℝ} (h : IsHt Γ K Q η) (hPQ : P ≤ Q) :
    IsHt Γ K P η :=
  ⟨fun p hp g => h.left p (hPQ hp) g, h.right, fun γ hγ hp => h.rat γ hγ (hPQ hp), h.cont⟩

lemma IsHt_lin {Γ K P : Subgroup G} {η₁ η₂ η : G → ℝ} (h₁ : IsHt Γ K P η₁) (h₂ : IsHt Γ K P η₂)
    (s t : ℝ) (e : ∀ g, η g = s * η₁ g + t * η₂ g) : IsHt Γ K P η := by
  have he : η = fun g => s * η₁ g + t * η₂ g := funext e
  subst he
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hp => ?_, ?_⟩
  · simp only [h₁.left p hp g, h₂.left p hp g]; ring
  · simp only [h₁.right g k hk, h₂.right g k hk]
  · simp only [h₁.rat γ hγ hp, h₂.rat γ hγ hp]; ring
  · have c₁ := h₁.cont
    have c₂ := h₂.cont
    fun_prop

lemma eis_congr {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {Λ Λ' : G → ℂ} {s s' : ℂ}
    (g : G) (w : W) (hs : s = s') (e : ∀ x, Λ x = Λ' x) :
    s • eis Γ K P c ρ Λ g w = s' • eis Γ K P c ρ Λ' g w := by
  have he : Λ = Λ' := funext e
  rw [hs, he]

variable [CompleteSpace W]

lemma series_first {Γ K S : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → (secSp K S c ρ) →L[ℂ] W} {a₀ : ℂ}
    (hH : ∀ g (w : secSp K S c ρ), H 0 g w = a₀ • sec K S c ρ g w) (z : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (z * h (rep r * g)) • H 0 (rep r * g)‖) (w : secSp K S c ρ) :
    outer Γ (Γ ⊓ S) h H (0, z) g w = a₀ • eis Γ K S c ρ (fun x => z * h x) g w := by
  rw [outer_apply h H (0, z) g hs w]
  simp only [hH]
  rw [tsum_cos_inf Γ S fun u => Complex.exp (z * h (u * g)) • a₀ • sec K S c ρ (u * g) w]
  simp only [eis]
  rw [← tsum_const_smul'' a₀]
  congr 1
  ext q
  rw [smul_comm]

lemma series_last {Γ K S : Subgroup G} {L : Type} [NormedAddCommGroup L] [NormedSpace ℂ L]
    {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {h : G → ℝ}
    {H : ℂ → G → L →L[ℂ] W} {N : ℂ} {T : L →L[ℂ] secSp K S c ρ}
    (hT : ∀ g w, H N g w = Complex.exp (h g) • sec K S c ρ g (T w)) (u : ℂ) (g : G)
    (hs : Summable fun r : Cos (Γ ⊓ S) Γ =>
      ‖Complex.exp (u * h (rep r * g)) • H N (rep r * g)‖) (w : L) :
    outer Γ (Γ ⊓ S) h H (N, u) g w = eis Γ K S c ρ (fun x => h x + u * h x) g (T w) := by
  rw [outer_apply h H (N, u) g hs w]
  simp only [hT]
  rw [tsum_cos_inf Γ S fun v => Complex.exp (u * h (v * g)) •
    Complex.exp (h (v * g)) • sec K S c ρ (v * g) (T w)]
  simp only [eis]
  congr 1
  ext q
  rw [smul_smul, ← Complex.exp_add, add_comm]

end Help

section Re

variable (N : ℝ) (l : ℂ × ℂ)

lemma mc_re₁ : (mc N l).1.re = l.1.re + l.2.re + 1 - N := by
  simp [chg, aff]; ring
lemma mc_re₂ : (mc N l).2.re = l.2.re + 1 := by simp [chg, aff]
lemma ma_re₁ : (ma N l).1.re = l.1.re + 2 * l.2.re + 1 - N := by
  simp [chg, aff]; ring
lemma ma_re₂ : (ma N l).2.re = l.2.re + 1 := by simp [chg, aff]
lemma mb_fst : (mb N l).1 = l.2 := by simp [chg, aff]
lemma mb_re₂ : (mb N l).2.re = 2 * N - 1 - l.1.re - l.2.re := by
  simp [chg, aff]; ring
lemma ml_fst : (ml N l).1 = nz N l := rfl
lemma nz_eq : nz N l = N - l.1 := by simp [aff]; ring
lemma ml_re₁ : (ml N l).1.re = N - l.1.re := by simp [chg, aff]; ring
lemma ml_re₂ : (ml N l).2.re = N - 1 - l.2.re := by simp [chg, aff]; ring

end Re

lemma isOpen_coneC (r : ℝ) : IsOpen (coneC r) :=
  (open_convex2 (-1) 1 0 1 1 0 r fun x => by
    simp only [coneC, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma isOpen_coneA (r : ℝ) : IsOpen (coneA r) :=
  (open_convex2 (-1) 1 0 0 1 0 r fun x => by
    simp only [coneA, affR, Set.mem_setOf_eq]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith).1

lemma tube_coneI_iff {r : ℝ} {m : ℂ × ℂ} : m ∈ tube (coneI r) ↔ r < m.2.re ∧ r < m.2.re + m.1.re :=
  Iff.rfl

lemma tube_coneC_iff {r : ℝ} {m : ℂ × ℂ} :
    m ∈ tube (coneC r) ↔ r < m.2.re - m.1.re ∧ r < m.2.re + m.1.re := Iff.rfl

lemma tube_coneA_iff {r : ℝ} {m : ℂ × ℂ} : m ∈ tube (coneA r) ↔ r < m.2.re - m.1.re ∧ r < m.2.re :=
  Iff.rfl

theorem gallery : SecLaw → IdTube → TubeChain → Cross → Gallery := by
  intro _ hId hTC hCross G _ _ _ _ _ W _ _ _ K ρ hK hρ hFC Γ S A B Q₁ Q₂ c h a b N hAS hBS hAQ hBQ
    pS pA pB hS hQa hQb hconv hFirst hWc hWa hWb hLast
  haveI := hFC
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨Rv, cS, cA, cB⟩ := hconv
  obtain ⟨R₀, D₀, Op₀, H₀, W₀, ⟨a₀, ha₀, hH₀⟩, O, hO, hOp⟩ := hFirst
  obtain ⟨Rc, Dc, Opc, Hc, Wc⟩ := hWc
  obtain ⟨Ra, Da, Opa, Ha, Wa⟩ := hWa
  obtain ⟨Rb, Db, Opb, Hb, Wb⟩ := hWb
  obtain ⟨Rl, Dl, Opl, Hl, Wl, ⟨d, hd, hdN, hDl⟩, T, hT⟩ := hLast
  have p₀ := W₀.pos
  have pc := Wc.pos
  have pa := Wa.pos
  have pb := Wb.pos
  have pl := Wl.pos
  obtain ⟨R, hRdef⟩ : ∃ R, R = |Rv| + R₀ + Rc + Ra + Rb + Rl + |N| + 1 := ⟨_, rfl⟩
  have hv₁ := abs_nonneg Rv
  have hv₂ := le_abs_self Rv
  have hv₃ := abs_nonneg N
  have hN : |N| + 1 ≤ R := by linarith
  have hRv : Rv ≤ R := by linarith
  have h₀ : R₀ ≤ R := by linarith
  have hc : Rc ≤ R := by linarith
  have ha : Ra ≤ R := by linarith
  have hb : Rb ≤ R := by linarith
  have hl : Rl ≤ R := by linarith
  have hN' := abs_le.1 (show |N| ≤ R - 1 by linarith)
  have hN₁ := hN'.1
  have hN₂ := hN'.2
  have hR1 : 1 ≤ R := by linarith
  have hAa := IsHt_restrict hQa hAQ
  have hAh := IsHt_restrict hS hAS
  have hBhb := IsHt_restrict hQb hBQ
  have hBh := IsHt_restrict hS hBS
  have hBb : IsHt Γ K B b := IsHt_lin hBhb hBh 1 (-1) fun g => by ring
  have hBβ : IsHt Γ K B fun g => h g + N * b g := IsHt_lin hBh hBb 1 N fun g => by ring
  have hBn : IsHt Γ K B fun g => -b g := IsHt_lin hBb hBb (-1) 0 fun g => by ring
  have hAβ : IsHt Γ K A fun g => N * a g - h g := IsHt_lin hAa hAh N (-1) fun g => by ring
  have hAd : IsHt Γ K A fun g => h g - a g := IsHt_lin hAh hAa 1 (-1) fun g => by ring
  have hAe : IsHt Γ K A fun g => (N - 1) * (h g - a g) := IsHt_lin hAd hAd (N - 1) 0 fun g => by ring
  have cA' : ∀ z y : ℝ, R < z → R < y → Conv Γ A fun g => z * a g + y * h g :=
    fun z y h₁ h₂ => cA z y (by linarith) (by linarith)
  have cB' : ∀ r y : ℝ, R < r → R < y → Conv Γ B fun g => r * (h g + b g) + y * h g :=
    fun z y h₁ h₂ => cB z y (by linarith) (by linarith)
  obtain ⟨g₀, s₀, -, l₀⟩ := hCross G W K ρ hK hρ Γ S A B c a b (fun g => h g + N * b g) h _ R₀ D₀ Op₀ H₀
    (coneI (10 * R)) hAS hBS pA pB hAa hBb hBβ hS W₀ (oc_coneI _).1 (cond_first hN h₀ cA' cB')
  obtain ⟨gc, -, rc, lc⟩ := hCross G W K ρ hK hρ Γ Q₂ B B c (fun g => -b g) (fun g => -b g)
    (fun g => -b g) (fun g => h g + b g) _ Rc Dc Opc Hc (coneC (10 * R)) hBQ hBQ pB pB hBn hBn hBn hQb
    Wc (isOpen_coneC _) (cond_c hN hc cB')
  obtain ⟨ga, -, ra, la⟩ := hCross G W K ρ hK hρ Γ S B A c b a (fun g => N * a g - h g) h _ Ra Da Opa Ha
    (coneA (10 * R)) hBS hAS pB pA hBb hAa hAβ hS Wa (isOpen_coneA _) (cond_a hN ha cA' cB')
  obtain ⟨gb, -, rb, lb⟩ := hCross G W K ρ hK hρ Γ Q₁ A A c (fun g => h g - a g) (fun g => h g - a g)
    (fun g => (N - 1) * (h g - a g)) a _ Rb Db Opb Hb (coneC (10 * R)) hAQ hAQ pA pA hAd hAd hAe hQa
    Wb (isOpen_coneC _) (cond_b hN hb cA')
  obtain ⟨gl, sl, rl, -⟩ := hCross G W K ρ hK hρ Γ S A B c a b (fun g => h g + N * b g) h _ Rl Dl Opl Hl
    (coneI (10 * R)) hAS hBS pA pB hAa hBb hBβ hS Wl (oc_coneI _).1 (cond_first hN hl cA' cB')
  have J₀ : ∀ l ∈ tube (chamberPairOneTwo (100 * R)), ∀ g, Dc (yv N l) • outer Γ (Γ ⊓ S) h H₀ l g =
      (outer Γ (Γ ⊓ Q₂) (fun g => h g + b g) Hc (mc N l) g).comp (Op₀ l.1) := by
    intro l hl g
    have hl' : l.1.re < -(100 * R) ∧ 100 * R < l.1.re + l.2.re := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : l ∈ tube (coneI (10 * R)) := tube_coneI_iff.2 ⟨by linarith, by linarith⟩
    have t₂ : mc N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mc_re₁, mc_re₂]; constructor <;> linarith)
    have cv := cB' (N - l.1.re) (l.1.re + l.2.re + 1 - N) (by linarith) (by linarith)
    have e₁ := l₀ l t₁ (by linarith) (conv_congr cv fun x => by ring) g
    have e₂ := rc (mc N l) t₂ (by rw [mc_re₁]; linarith)
      (conv_congr cv fun x => by rw [mc_re₁, mc_re₂]; ring) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [e₁, e₂]
    exact eis_congr g _ rfl fun x => by simp only [chg, aff]; push_cast; ring
  have J₁ : ∀ l ∈ tube (chamberPairTwoThree (100 * R)), ∀ g,
      Da (zv N l) • outer Γ (Γ ⊓ Q₂) (fun g => h g + b g) Hc (mc N l) g =
        (outer Γ (Γ ⊓ S) h Ha (ma N l) g).comp (Opc (yv N l)) := by
    intro l hl g
    have hl' : l.1.re + l.2.re < -(100 * R) ∧ 100 * R < l.1.re + 2 * l.2.re := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : mc N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mc_re₁, mc_re₂]; constructor <;> linarith)
    have t₂ : ma N l ∈ tube (coneA (10 * R)) := tube_coneA_iff.2 (by
      rw [ma_re₁, ma_re₂]; constructor <;> linarith)
    have cv := cB' (l.1.re + 2 * l.2.re + 1 - N) (N - l.1.re - l.2.re) (by linarith) (by linarith)
    have e₁ := lc (mc N l) t₁ (by rw [mc_re₁]; linarith)
      (conv_congr cv fun x => by rw [mc_re₁, mc_re₂]; ring) g
    have e₂ := ra (ma N l) t₂ (by rw [ma_re₁]; linarith)
      (conv_congr cv fun x => by rw [ma_re₁, ma_re₂]; ring) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [e₁, e₂]
    exact eis_congr g _ rfl fun x => by simp only [chg, aff]; push_cast; ring
  have J₂ : ∀ l ∈ tube (chamberPairThreeFour (100 * R)), ∀ g, Db l.2 • outer Γ (Γ ⊓ S) h Ha (ma N l) g =
      (outer Γ (Γ ⊓ Q₁) a Hb (mb N l) g).comp (Opa (zv N l)) := by
    intro l hl g
    have hl' : l.1.re + 2 * l.2.re < -(100 * R) ∧ 100 * R < l.2.re := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : ma N l ∈ tube (coneA (10 * R)) := tube_coneA_iff.2 (by
      rw [ma_re₁, ma_re₂]; constructor <;> linarith)
    have t₂ : mb N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mb_fst, mb_re₂]; constructor <;> linarith)
    have cv := cA' (N - (l.1.re + 2 * l.2.re + 1 - N)) l.2.re (by linarith) (by linarith)
    have e₁ := la (ma N l) t₁ (by rw [ma_re₁]; linarith)
      (conv_congr cv fun x => by rw [ma_re₁, ma_re₂]; ring) g
    have e₂ := rb (mb N l) t₂ (by rw [mb_fst]; linarith)
      (conv_congr cv fun x => by rw [mb_fst, mb_re₂]; ring) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [e₁, e₂]
    exact eis_congr g _ (by rw [mb_fst]) fun x => by simp only [chg, aff]; push_cast; ring
  have J₃ : ∀ l ∈ tube (chamberPairFourLast (100 * R)), ∀ g,
      (-d (nz N l)) • (outer Γ (Γ ⊓ Q₁) a Hb (mb N l) g).comp
        ((Opa (zv N l)).comp ((Opc (yv N l)).comp (Op₀ l.1))) =
      (outer Γ (Γ ⊓ S) h Hl (ml N l) g).comp
        ((Opb l.2).comp ((Opa (zv N l)).comp ((Opc (yv N l)).comp (O l.1)))) := by
    intro l hl g
    have hl' : l.2.re < -(100 * R) ∧ l.1.re < -(100 * R) := hl
    obtain ⟨x₁, x₂⟩ := hl'
    have t₁ : mb N l ∈ tube (coneC (10 * R)) := tube_coneC_iff.2 (by
      rw [mb_fst, mb_re₂]; constructor <;> linarith)
    have t₂ : ml N l ∈ tube (coneI (10 * R)) := tube_coneI_iff.2 (by
      rw [ml_re₁, ml_re₂]; constructor <;> linarith)
    have cv := cA' (N - l.1.re) (N - 1 - l.2.re) (by linarith) (by linarith)
    have hz := hOp l.1 (by linarith)
    have e₁ := lb (mb N l) t₁ (by rw [mb_fst]; linarith)
      (conv_congr cv fun x => by rw [mb_fst, mb_re₂]; ring) g
    have e₂ := rl (ml N l) t₂ (by rw [ml_re₁]; linarith)
      (conv_congr cv fun x => by rw [ml_re₁, ml_re₂]) g
    refine ContinuousLinearMap.ext fun w => ?_
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    rw [hz]
    simp only [ContinuousLinearMap.smul_apply, map_smul]
    rw [e₁, e₂, mb_fst, smul_smul, hDl]
    exact eis_congr g _ (by rw [ml_fst, nz_eq]; push_cast; ring)
      fun x => by simp only [chg, aff]; push_cast; ring
  obtain ⟨Φ, hΦ, eR, eL⟩ := core hId hTC N R hN g₀ gc ga gb gl Wc.dEnt Wa.dEnt Wb.dEnt hd
    (LeftGood_mono W₀.op (by linarith)) hO (LeftGood_mono Wc.op (by linarith))
    (LeftGood_mono Wa.op (by linarith)) (LeftGood_mono Wb.op (by linarith)) J₀ J₁ J₂ J₃
  have hdN' : d N ≠ 0 := hdN
  have hsl := slice_good hΦ
  have hOpa' : LeftGood Opa (-R) := LeftGood_mono Wa.op (by linarith)
  have hOpb' : LeftGood Opb (-R) := LeftGood_mono Wb.op (by linarith)
  have hOpc' : LeftGood Opc (-R) := LeftGood_mono Wc.op (by linarith)
  refine ⟨20 * R,
    fun y => Complex.exp ((0 : ℂ) ^ 2 + y ^ 2) * (Dc (yv N (0, y)) * Da (zv N (0, y)) * Db y) * a₀,
    fun y => (Complex.exp ((0 : ℂ) ^ 2 + y ^ 2) * (-(d N)⁻¹)) •
      T.comp ((Opb y).comp ((Opa (aff 0 2 (1 - N) (0, y))).comp
        ((Opc (aff 0 1 (1 - N) (0, y))).comp (O 0)))),
    fun y g => Φ (0, y) g, ?_⟩
  refine
    { le := le_rfl
      pos := by linarith
      convR := fun x hx => cS x (by linarith)
      convL := fun x hx => conv_congr (cS (N - x) (by linarith)) fun g => by ring
      dEnt := ?_
      dNe := ?_
      op := ?_
      hol := hsl.1
      cont := hsl.2.1
      bdd := hsl.2.2
      eqR := ?_
      eqL := ?_ }
  · exact stripEntire_of_fac (A := fun l => Complex.exp (l.1 ^ 2 + l.2 ^ 2) *
      (Dc (yv N l) * Da (zv N l) * Db l.2) * a₀)
      (Fac_mul (Fac_mul (Fac_exp _) (Fac_mul (Fac_mul (Fac_strip Wc.dEnt _ _ _ _)
        (Fac_strip Wa.dEnt _ _ _ _)) (Fac_strip_snd Wb.dEnt _))) (Fac_const _ _)) fun _ => rfl
  · have d₁ : Differentiable ℂ fun y : ℂ => Dc (yv N (0, y)) :=
      (stripEntire_of_fac (A := fun l => Dc (yv N l)) (Fac_strip Wc.dEnt _ _ _ _) fun _ => rfl).1
    have d₂ : Differentiable ℂ fun y : ℂ => Da (zv N (0, y)) :=
      (stripEntire_of_fac (A := fun l => Da (zv N l)) (Fac_strip Wa.dEnt _ _ _ _) fun _ => rfl).1
    obtain ⟨y₁, hy₁⟩ := exists_ne_mul d₁ d₂ (exists_ne_aff Wc.dNe 1 1 (1 - N) one_ne_zero)
      (exists_ne_aff Wa.dNe 1 2 (1 - N) two_ne_zero)
    obtain ⟨y, hy⟩ := exists_ne_mul (f := fun y : ℂ => Dc (yv N (0, y)) * Da (zv N (0, y)))
      (d₁.mul d₂) Wb.dEnt.1 ⟨y₁, hy₁⟩ Wb.dNe
    exact ⟨y, mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hy) ha₀⟩
  · refine leftGood_of_fac (A := fun l => (Complex.exp (l.1 ^ 2 + l.2 ^ 2) * (-(d N)⁻¹)) •
      T.comp ((Opb l.2).comp ((Opa (aff 0 2 (1 - N) l)).comp
        ((Opc (aff 0 1 (1 - N) l)).comp (O 0))))) ?_ fun _ => rfl
    refine Fac_smul (Fac_mul (Fac_exp _) (Fac_const _ _)) (Fac_comp (Fac_const _ _) (Fac_comp
      (Fac_left_snd hOpb' fun x hx => ?_) (Fac_comp (Fac_left hOpa' _ _ _ fun x hx => ?_)
        (Fac_comp (Fac_left hOpc' _ _ _ fun x hx => ?_) (Fac_const _ _)))))
    · have : x.2 < -(20 * R) := hx
      linarith
    · have : x.2 < -(20 * R) := hx
      simp only [affR]; linarith
    · have : x.2 < -(20 * R) := hx
      simp only [affR]; linarith
  · intro z hz g w
    have hm : ((0 : ℂ), z) ∈ tube (coneI (10 * R)) :=
      tube_coneI_iff.2 (by simp only [Complex.zero_re, add_zero]; constructor <;> linarith)
    have e₂ := series_first hH₀ z g (s₀ (0, z) hm g) w
    change Φ (0, z) g w = _
    rw [eR (0, z) hm g]
    simp only [ContinuousLinearMap.smul_apply]
    rw [e₂]
    simp only [smul_smul]
    congr 1
    ring
  · intro y hy g w
    have hm : ((0 : ℂ), y) ∈ tube (Om4 N (10 * R)) := by
      refine mem_Om4.2 ⟨⟨?_, ?_⟩, ?_⟩
      · show 10 * R < N - 1 - y.re
        linarith
      · show 10 * R < 2 * N - 1 - y.re - (0 : ℂ).re
        simp only [Complex.zero_re]; linarith
      · show (0 : ℂ).re < 1 / 2
        simp
    have e := eL (0, y) hm g
    have ez : nz N ((0 : ℂ), y) = N := by simp [aff]
    have ez₁ : zv N ((0 : ℂ), y) = aff 0 2 (1 - N) (0, y) := by simp [aff]
    have ez₂ : yv N ((0 : ℂ), y) = aff 0 1 (1 - N) (0, y) := by simp [aff]
    obtain ⟨u, hu, hu'⟩ : ∃ u : ℂ, ml N ((0 : ℂ), y) = ((N : ℂ), u) ∧ u = N - 1 - y :=
      ⟨_, Prod.ext (by simp [chg, aff]) rfl, by simp [chg, aff]; ring⟩
    have hm₂ : ml N ((0 : ℂ), y) ∈ tube (coneI (10 * R)) := tube_coneI_iff.2 (by
      rw [ml_re₁, ml_re₂]
      simp only [Complex.zero_re]
      constructor <;> linarith)
    have hs := sl _ hm₂ g
    rw [hu] at hs e
    rw [ez, ez₁, ez₂] at e
    set w' := (Opb y) ((Opa (aff 0 2 (1 - N) (0, y))) ((Opc (aff 0 1 (1 - N) (0, y))) (O 0 w)))
      with hw'
    have e' := DFunLike.congr_fun e w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply] at e'
    rw [series_last hT u g hs w'] at e'
    have hinv : (Φ (0, y) g) w = (-(d N))⁻¹ • ((-d N) • (Φ (0, y) g) w) := by
      rw [smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hdN'), one_smul]
    change (Φ (0, y) g) w = eis Γ K S c ρ (fun x => (N * h x : ℝ) - y * h x) g
      (((Complex.exp ((0 : ℂ) ^ 2 + y ^ 2) * (-(d N)⁻¹)) • T w' : secSp K S c ρ) : W)
    rw [hinv, e', Submodule.coe_smul, eis_smul, smul_smul]
    refine eis_congr g _ ?_ fun x => ?_
    · field_simp
    · rw [hu']; push_cast; ring

end GlobalTheory.CompanionTheory.RgEisGal
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gallery_of_tubes_and_crossing : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.IdTube → PositivityTheory.RgEis.TubeChain → PositivityTheory.RgEis.Cross → PositivityTheory.RgEis.Gallery := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RgEisGal.gallery
end
