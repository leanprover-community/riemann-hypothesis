import ReciprocityTheory.SemistableReduction.LatSemiSt

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem ratEmb_conj (σ : ℚ →+* ℂ) (x : ℚ) : σ x = conj (σ x) := by
  rw [eq_ratCast σ x, map_ratCast]

def ratHermitianOne : HermForm ℚ 1 where
  c := RingHom.id ℚ
  c_invol := fun _ => rfl
  c_emb := fun σ x => ratEmb_conj σ x
  G := 1
  G_herm := fun a b => by rw [Subsingleton.elim a b]; rfl

def ratMajorantOne : Majorant ratHermitianOne where
  H := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  major := fun σ => by simp [ratHermitianOne]
  conj_compat := fun σ => by simp

def hermQ (r : ℕ) : HermForm ℚ r where
  c := RingHom.id ℚ
  c_invol := fun _ => rfl
  c_emb := fun σ x => ratEmb_conj σ x
  G := 1
  G_herm := fun a b => by
    by_cases h : a = b
    · subst h; rfl
    · simp [h, Ne.symm h]

def majQ (r : ℕ) : Majorant (hermQ r) where
  H := fun _ => 1
  posDef := fun _ => Matrix.PosDef.one
  major := fun σ => by simp [hermQ]
  conj_compat := fun σ => by simp

example (a : ℕ) : IsTriEquivariant (fun _ : Fin 1 => a) (fun x => x 0 0 ^ a) := by
  intro x b _ _ _
  simp [triChar, Matrix.mul_apply, mul_pow, mul_comm]

example (c : ℂ) : IsTriEquivariant (fun _ : Fin 0 => 0) (fun _ => c) := by
  intro x b _ _ _
  simp [triChar]

example (c : ℂ) : IsBW (fun _ : Fin 0 => 0) (fun _ => c) := by
  refine ⟨differentiableOn_const c, ?_, ?_⟩
  · intro x b _ _ _
    simp [triChar]
  · intro x hx
    simp at hx

example : IsOpen (Metric.ball (0 : ℂ) 1) ∧ Balanced ℂ (Metric.ball (0 : ℂ) 1) ∧
    DifferentiableOn ℂ (fun z : ℂ => z) (Metric.ball 0 1) ∧
    ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖(fun z : ℂ => z) w‖ ≤ 1 := by
  refine ⟨Metric.isOpen_ball, balanced_ball_zero, differentiableOn_id, fun w hw => ?_⟩
  simpa using (Metric.mem_ball.mp hw).le

example : let V := EuclideanSpace ℂ (Fin 0)
    Differentiable ℂ (fun _ : V => (1 : ℂ)) ∧ (∃ _z : V, (1 : ℂ) ≠ 0) ∧
    (∀ v : V, ∃ l ∈ (⊤ : AddSubgroup V), ‖v - l‖ ≤ 0) ∧ 5 * (0 : ℝ) < (1 : ℕ) := by
  refine ⟨differentiable_const 1, ⟨0, one_ne_zero⟩, fun v => ⟨v, trivial, by simp⟩, by norm_num⟩

example (x y : Fin 1 → ℂ) : jForm 1 x y = conj (x 0) * y 0 := by
  simp [jForm, sgn]

example : (Real.exp (1 / 3) + 1) * ((1 : ℕ) : ℝ) < ((4 : ℕ) : ℝ) := by
  have h1 : Real.exp (1 / 3) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
  have h2 := Real.exp_one_lt_d9
  push_cast
  linarith

example (r : ℕ) (u : Fin r → ℂ) :
    normSq (((1 : Matrix (Fin r) (Fin r) ℂ) * (1 : Matrix (Fin r) (Fin r) ℚ).map (Rat.castHom ℂ) *
      (1 : Matrix (Fin r) (Fin r) ℂ)⁻¹) *ᵥ u) ≤ Real.exp (2 / (3 * (r : ℝ))) * normSq u := by
  have h0 : 0 ≤ normSq u := Finset.sum_nonneg fun k _ => by positivity
  have h1 : 1 ≤ Real.exp (2 / (3 * (r : ℝ))) := Real.one_le_exp (by positivity)
  simp only [Matrix.map_one, map_zero, map_one, inv_one, mul_one, one_mulVec]
  nlinarith

example (x : Matrix (Fin 1) (Fin 1) ℂ) : leadMinor x 0 = x 0 0 := by
  simp [leadMinor, Matrix.det_unique]

abbrev QI : Type := CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ QI := by
  have : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension (n := 4) (K := ℚ)

instance : IsCMField QI :=
  IsCyclotomicExtension.Rat.isCMField QI (S := {4}) ⟨4, rfl, by norm_num⟩

example : Nonempty (QI →+* ℂ) := inferInstance

def hermQI : HermForm QI 1 where
  c := (IsCMField.complexConj QI : QI →+* QI)
  c_invol := fun x => IsCMField.complexConj_apply_apply QI x
  c_emb := fun σ x => IsCMField.complexEmbedding_complexConj QI σ x
  G := 1
  G_herm := fun a b => by rw [Subsingleton.elim a b]; simp

def intLat (K : Type) [Field K] [NumberField K] (r : ℕ) : Submodule (𝓞 K) (Fin r → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

theorem mem_intLat {K : Type} [Field K] [NumberField K] {r : ℕ} (x : Fin r → K) :
    x ∈ intLat K r ↔ ∀ a, IsIntegralElt (x a) := by
  simp only [intLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  rfl





end ReciprocityTheory.MultiplicativeHeights
