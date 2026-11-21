import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetExtensionSquareZero
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetMorphismExtendingTranslation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

section
section
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.SecondOrderNbhd

open TrivSqZeroExt

noncomputable def deform {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) : O →+* DualNumber R where
  toFun x := inl (f x) + inr (f (D x))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

@[simp] lemma deform_fst {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).fst = f x := by
  simp [deform]

@[simp] lemma deform_snd {O R : Type} [CommRing O] [Algebra ℂ O] [CommRing R]
    (D : Derivation ℂ O O) (f : O →+* R) (x : O) : (deform D f x).snd = f (D x) := by
  simp [deform]

lemma isNilpotent_span_of_sq {C : Type} [CommRing C] {e : C} (h : e * e = 0) :
    IsNilpotent (Ideal.span {e}) := by
  refine ⟨2, ?_⟩
  rw [Ideal.span_singleton_pow, pow_two, h]
  simp

theorem exists_second_order_nbhd : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  intro O _ _ D₁ D₂ h
  let i : O →+* DualNumber O := (inlHom O O)
  let j : DualNumber O →+* DualNumber (DualNumber O) := inlHom _ _
  let e₁ : DualNumber (DualNumber O) := inl DualNumber.eps
  let e₂ : DualNumber (DualNumber O) := DualNumber.eps
  have h1 : e₁ * e₁ = 0 := by
    simp only [e₁]; rw [inl_mul_inl, DualNumber.eps_mul_eps]; simp
  have h2 : e₂ * e₂ = 0 := DualNumber.eps_mul_eps
  refine ⟨DualNumber (DualNumber O), inferInstance, Ideal.span {e₁} + Ideal.span {e₂},
    j.comp i, j.comp (deform D₁ (RingHom.id O)), deform D₂ i,
    deform D₂ (deform D₁ (RingHom.id O)), e₁, e₂, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Commute.all _ _).isNilpotent_add (isNilpotent_span_of_sq h1) (isNilpotent_span_of_sq h2)
  · exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  · exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  · intro x; ext <;> simp [i, j, e₁]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₂]
  · intro x; ext <;> simp [i, j, e₁, h]
  · intro x hx
    have := congrArg (fun z : DualNumber (DualNumber O) => z.snd.snd) hx
    simpa [i, j, e₁, e₂] using this

end GlobalTheory.SecondOrderNbhd
end

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  atlas_forward_decl GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd
end

section
section
set_option autoImplicit false

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem dw_comm (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W) :
    dw a (dw b x) = dw b (dw a x) := by
  have key : ∀ (u v : Tot I g) (p : Tot I g), p ∈ W →
      (Hol.der u (Hol.der v x)).fn p = fderiv ℂ (fderiv ℂ x.fn) p u v := by
    intro u v p hp
    have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
    have e : (Hol.der v x).fn =ᶠ[nhds p] fun q ↦ fderiv ℂ x.fn q v := by
      filter_upwards [W.isOpen.mem_nhds hp] with q hq using Hol.fn_der v x hq
    rw [Hol.fn_der u _ hp, e.fderiv_eq,
      fderiv_clm_apply hx.fderiv.differentiableAt (differentiableAt_const v)]
    simp
  refine Hol.ext_fn fun p hp ↦ ?_
  have hx : AnalyticAt ℂ x.fn p := x.analytic p hp
  have hs : IsSymmSndFDerivAt ℂ x.fn p :=
    (hx.contDiffAt (n := ⊤)).isSymmSndFDerivAt (by simp)
  unfold dw
  rw [key _ _ p hp, key _ _ p hp]
  exact hs _ _

end GlobalTheory.AnPer
end

open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreCoordinatePartialDerivation_comm : ∀ (I : Type) [Fintype I] (g : ℕ) (W : Opens (Tot I g)) (a b : Fin g) (x : Hol W), dw a (dw b x) = dw b (dw a x) := by
  atlas_forward_decl GlobalTheory.AnPer.dw_comm
end

section
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

theorem step_single {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C}
    {ρ₁ ρ₂ : Hol W →+* C} (a : Fin g) (e : C) (he : e ∈ J) (h2 : e * e = 0)
    (h : ∀ x, ρ₂ x = ρ₁ x + ρ₁ (dw a x) * e) : Step J ρ₁ ρ₂ := by
  refine ⟨Pi.single a e, fun c ↦ ?_, fun c d ↦ ?_, fun x ↦ ?_⟩
  · by_cases hc : c = a
    · subst hc; simpa using he
    · simp [hc]
  · by_cases hc : c = a
    · by_cases hd : d = a
      · subst hc; subst hd; simpa using h2
      · simp [hd]
    · simp [hc]
  · rw [h, Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp

theorem exists_second_order_nbhd : ∀ (I : Type) [Fintype I] (g : ℕ) (Λ : Type) [AddCommGroup Λ] (F : Fam I g Λ) (K : Charts F) (k : K.K) (a b : Fin g), ∃ (T : K.Obj) (φ₀ φ₁ φ₂ φ₃ : K.triv k ⟶ T) (e₁ e₂ : T.C), φ₀.deg = 0 ∧ φ₁.deg = 0 ∧ φ₂.deg = 0 ∧ φ₃.deg = 0 ∧ e₁ ∈ T.J ∧ e₂ ∈ T.J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x : Hol (K.W k), φ₁.φ x = φ₀.φ x + φ₀.φ (dw a x) * e₁) ∧ (∀ x : Hol (K.W k), φ₂.φ x = φ₀.φ x + φ₀.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₁.φ x + φ₁.φ (dw b x) * e₂) ∧ (∀ x : Hol (K.W k), φ₃.φ x = φ₂.φ x + φ₂.φ (dw a x) * e₁) ∧ ∀ x : Hol (K.W k), φ₀.φ x * e₁ * e₂ = 0 → x = 0 := by
  intro I _ g Λ _ F K k a b
  obtain ⟨C, _, J, φ₀, φ₁, φ₂, φ₃, e₁, e₂, hJ, h1, h2, h11, h22, H1, H2, H3, H4, H5⟩ :=
    GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations (Hol (K.W k)) (dw a) (dw b) (GlobalTheory.T.fibreCoordinatePartialDerivation_comm I g (K.W k) a b)
  let T : K.Obj :=
    { k := k, C := C, alg := (φ₀.comp (K.cst k)).toAlgebra, J := J, nil := hJ, ρ := φ₀, ρ_cst := fun _ ↦ rfl }
  have hs : T.ρ.comp (sh (K.le_refl k)) = φ₀ := RingHom.ext fun f ↦ congrArg φ₀ (sh_refl _ f)
  have c0 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₀ := by rw [hs]; exact Relation.ReflTransGen.refl
  have c1 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₁ := Relation.ReflTransGen.tail c0 (step_single a e₁ h1 h11 H1)
  have c2 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₂ := Relation.ReflTransGen.tail c0 (step_single b e₂ h2 h22 H2)
  have c3 : Close T.J (T.ρ.comp (sh (K.le_refl k))) φ₃ := Relation.ReflTransGen.tail c1 (step_single b e₂ h2 h22 H3)
  have a1 : ∀ f, φ₁ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H1, dw_cst]; simp
  have a2 : ∀ f, φ₂ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H2, dw_cst]; simp
  have a3 : ∀ f, φ₃ (K.cst k f) = φ₀ (K.cst k f) := fun f ↦ by rw [H3, dw_cst, a1]; simp
  exact ⟨T, fromTriv T (K.le_refl k) φ₀ (fun _ ↦ rfl) c0, fromTriv T (K.le_refl k) φ₁ a1 c1,
    fromTriv T (K.le_refl k) φ₂ a2 c2, fromTriv T (K.le_refl k) φ₃ a3 c3, e₁, e₂, rfl, rfl, rfl, rfl,
    h1, h2, h11, h22, H1, H2, H3, H4, H5⟩

end GlobalTheory.AnPer
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.ClosedSq

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)

theorem diff (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k))
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (n : Fin g → T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (hn : ∀ a, n a ∈ T.J) (hnn : ∀ a b, n a * n b = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + ∑ a, f₁.φ (dw a x : Hol (K.W k)) * n a) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.fst : Hol (K.W k)) + ∑ a, f₁.φ (θ.snd a : Hol (K.W k)) * n a := by
  obtain ⟨χ, hd, h0, h1, hχ⟩ := exists_jet_factor K f₁ f₂ n (d₁.trans d₂.symm) hn hnn hf
  have e0 := hh _ _ _ (jet0 k) χ rfl (hd.trans d₁)
  have e1 := hh _ _ _ (jet1 k) χ rfl (hd.trans d₁)
  rw [h0] at e0
  rw [h1] at e1
  rw [← hχ θ, hθ, h₁, h₂, e0, e1]
  exact (add_sub_add_right_eq_sub _ _ _).trans (map_sub χ.φ _ _).symm

theorem sum_single {O : Type} [CommRing O] (v : Fin g → O) (a : Fin g) (e : O) :
    ∑ c, v c * (Pi.single a e : Fin g → O) c = v a * e := by
  simp [Pi.single_apply]

theorem diff1 (h : C1 K.Oc) (hh : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k : K.K)
    (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))) (hθ : θ = h _ _ (jet0 k) - h _ _ (jet1 k)) (h0 : θ.fst = 0)
    {T : K.Obj} (f₁ f₂ : K.triv k ⟶ T) (a : Fin g) (e : T.C) (d₁ : f₁.deg = 0) (d₂ : f₂.deg = 0)
    (he : e ∈ T.J) (hee : e * e = 0)
    (hf : ∀ x : Hol (K.W k), f₂.φ x = f₁.φ x + f₁.φ (dw a x : Hol (K.W k)) * e) (u₁ u₂ : T.C)
    (h₁ : u₁ = h _ _ f₁) (h₂ : u₂ = h _ _ f₂) :
    u₁ - u₂ = f₁.φ (θ.snd a : Hol (K.W k)) * e := by
  have := diff K h hh k θ hθ f₁ f₂ (Pi.single a e) d₁ d₂
    (fun c ↦ by rw [Pi.single_apply]; split_ifs; exacts [he, T.J.zero_mem])
    (fun c d ↦ by
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs
      exacts [hee, mul_zero _, zero_mul _, mul_zero _])
    (fun x ↦ (hf x).trans (congrArg (f₁.φ x + ·) (sum_single (fun c ↦ f₁.φ (dw c x : Hol (K.W k))) a e).symm)) u₁ u₂ h₁ h₂
  rw [this, h0, sum_single (fun c ↦ f₁.φ (θ.snd c : Hol (K.W k)))]
  exact (congrArg (· + _) (map_zero f₁.φ)).trans (zero_add _)

theorem units_mul_relation_rearrange_commRing {C : Type} [CommRing C] (u₀ u₁ u₂ u₃ A B A' B' A₂ B₁ e₁ e₂ : C) (h1 : u₀ - u₁ = A * e₁)
    (h2 : u₁ - u₃ = B₁ * e₂) (h3 : u₀ - u₂ = B * e₂) (h4 : u₂ - u₃ = A₂ * e₁) (h5 : B₁ = B + B' * e₁)
    (h6 : A₂ = A + A' * e₂) : (B' - A') * e₁ * e₂ = 0 := by
  subst h5 h6
  linear_combination -h1 - h2 + h3 + h4

theorem connForm_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  intro I _ g Λ _ F K h hh k θ hθ
  have h0 : θ.fst = 0 := by
    have := diff K h hh k θ hθ (𝟙 (K.triv k)) (𝟙 (K.triv k)) (fun _ ↦ 0) rfl rfl (fun _ ↦ (K.triv k).J.zero_mem)
      (fun _ _ ↦ mul_zero _) (fun x ↦ by simp only [mul_zero, Finset.sum_const_zero, add_zero]) _ _ rfl rfl
    simp only [mul_zero, Finset.sum_const_zero, add_zero, sub_self] at this
    exact this.symm
  refine ⟨h0, fun a b ↦ ?_⟩
  obtain ⟨T, φ₀, φ₁, φ₂, φ₃, e₁, e₂, d₀, d₁, d₂, d₃, m₁, m₂, s₁, s₂, p₁, p₂, p₃, p₄, inj⟩ :=
    exists_second_order_nbhd I g Λ F K k a b
  refine sub_eq_zero.1 (inj _ ?_)
  have := units_mul_relation_rearrange_commRing _ _ _ _ _ _ _ _ _ _ e₁ e₂
    (diff1 K h hh k θ hθ h0 φ₀ φ₁ a e₁ d₀ d₁ m₁ s₁ p₁ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₁ φ₃ b e₂ d₁ d₃ m₂ s₂ p₃ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₀ φ₂ b e₂ d₀ d₂ m₂ s₂ p₂ _ _ rfl rfl)
    (diff1 K h hh k θ hθ h0 φ₂ φ₃ a e₁ d₂ d₃ m₁ s₁ p₄ _ _ rfl rfl) (p₁ _) (p₂ _)
  exact (congrArg (· * e₁ * e₂) (map_sub φ₀.φ _ _)).trans this

end GlobalTheory.AnPer.ClosedSq
end
end

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectionForm_degZeroCocycle_closed : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∀ (k : K.K) (θ : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))), θ = h _ _ (jet0 k) - h _ _ (jet1 k) → θ.fst = 0 ∧ ∀ a b, dw a (θ.snd b) = dw b (θ.snd a) := by
  atlas_forward_decl GlobalTheory.AnPer.ClosedSq.connForm_closed
end

section
open Set

namespace GlobalTheory

private lemma eq_of_fderiv_fibre_zero_convex {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {g : ℕ}
    (F : P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (hC : IsOpen C)
    (hCc : Convex ℝ C) (hF : AnalyticOnNhd ℂ F (Z ×ˢ C))
    (hd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0)
    {z : P} (hz : z ∈ Z) {y y' : Fin g → ℂ} (hy : y ∈ C) (hy' : y' ∈ C) :
    F (z, y) = F (z, y') := by
  have hda : ∀ x ∈ C, HasFDerivAt (fun w => F (z, w))
      ((fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ))) x := by
    intro x hx
    exact (hF (z, x) ⟨hz, hx⟩).differentiableAt.hasFDerivAt.comp x (hasFDerivAt_prodMk_right z x)
  have hzero : ∀ x ∈ C,
      (fderiv ℂ F (z, x)).comp (ContinuousLinearMap.inr ℂ P (Fin g → ℂ)) = 0 := by
    intro x hx
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.pi_ext
    intro a t
    have e : ((0 : P), (Pi.single a t : Fin g → ℂ)) = t • ((0 : P), (Pi.single a 1 : Fin g → ℂ)) := by
      refine Prod.ext (by simp) ?_
      funext j
      by_cases h : j = a
      · subst h; simp
      · simp [h]
    show fderiv ℂ F (z, x) ((0 : P), Pi.single a t) = 0
    rw [e, map_smul, hd a (z, x) ⟨hz, hx⟩, smul_zero]
  exact hCc.is_const_of_fderivWithin_eq_zero
    (fun x hx => (hda x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [fderivWithin_of_isOpen hC hx, (hda x hx).fderiv, hzero x hx]) hy hy'

theorem exists_analytic_param_of_primitives_on_box : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (G G' : K → P × (Fin g → ℂ) → ℂ), (∀ k, IsOpen (W k)) → IsOpen Z → IsOpen C → Convex ℝ C → C.Nonempty → (∀ p ∈ Z ×ˢ C, ∃ k, p ∈ W k) → ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) → ((∀ k, AnalyticOnNhd ℂ (G' k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G' k p - G' l p = c k l p) → ∃ h : P → ℂ, AnalyticOnNhd ℂ h Z ∧ ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → G k p = G' k p + h p.1 := by
  intro P _ _ _ g K W c ω Z C G G' hW hZ hC hCc hCn hcov hG hG'
  obtain ⟨hGa, hGd, hGc⟩ := hG
  obtain ⟨hG'a, hG'd, hG'c⟩ := hG'
  classical
  have hov : ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G' k p = G l p - G' l p := by
    intro k l p hk hl hp
    have h1 := hGc k l p hk hl hp
    have h2 := hG'c k l p hk hl hp
    linear_combination h1 - h2
  let F : P × (Fin g → ℂ) → ℂ := fun p =>
    if h : ∃ k, p ∈ W k then G h.choose p - G' h.choose p else 0
  have hFeq : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → F p = G k p - G' k p := by
    intro k p hk hp
    have h : ∃ k, p ∈ W k := ⟨k, hk⟩
    simp only [F, dif_pos h]
    exact hov _ _ p h.choose_spec hk hp
  have hFloc : ∀ k, ∀ p ∈ W k, p ∈ Z ×ˢ C → (fun q => G k q - G' k q) =ᶠ[nhds p] F := by
    intro k p hk hp
    filter_upwards [((hW k).inter (hZ.prod hC)).mem_nhds ⟨hk, hp⟩] with q hq
    exact (hFeq k q hq.1 hq.2).symm
  have hFa : AnalyticOnNhd ℂ F (Z ×ˢ C) := by
    intro p hp
    obtain ⟨k, hk⟩ := hcov p hp
    exact ((hGa k p ⟨hk, hp⟩).sub (hG'a k p ⟨hk, hp⟩)).congr (hFloc k p hk hp)
  have hFd : ∀ a, ∀ p ∈ Z ×ˢ C, fderiv ℂ F p (0, Pi.single a 1) = 0 := by
    intro a p hp
    obtain ⟨k, hk⟩ := hcov p hp
    have hs : HasFDerivAt (fun q => G k q - G' k q)
        (fderiv ℂ (G k) p - fderiv ℂ (G' k) p) p :=
      (hGa k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt.sub
        (hG'a k p ⟨hk, hp⟩).differentiableAt.hasFDerivAt
    rw [← (hFloc k p hk hp).fderiv_eq, hs.fderiv]
    simp [hGd k a p hk hp, hG'd k a p hk hp]
  obtain ⟨y₀, hy₀⟩ := hCn
  refine ⟨fun z => F (z, y₀), ?_, ?_⟩
  · intro z hz
    have hi : AnalyticAt ℂ (fun w : P => (w, y₀)) z := analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (g := F) (f := fun w : P => (w, y₀)) (hFa (z, y₀) ⟨hz, hy₀⟩) hi
  · intro k p hk hp
    have hc := eq_of_fderiv_fibre_zero_convex F Z C hC hCc hFa hFd hp.1 hp.2 hy₀
    have hp' : ((p.1, p.2) : P × (Fin g → ℂ)) = p := rfl
    rw [hp'] at hc
    show G k p = G' k p + F (p.1, y₀)
    rw [← hc, hFeq k p hk hp]
    ring

end GlobalTheory
end

section
open Set

namespace GlobalTheory

open Set in

theorem _root_.GlobalTheory.exists_merge_fibre_primitives : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (C' : Set (Fin g → ℂ)) (G G' : K → P × (Fin g → ℂ) → ℂ), (∀ k, IsOpen (W k)) → IsOpen Z → IsOpen C → Convex ℝ C → IsOpen C' → Convex ℝ C' → (C ∩ C').Nonempty → (∀ p ∈ Z ×ˢ (C ∪ C'), ∃ k, p ∈ W k) → ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) → ((∀ k, AnalyticOnNhd ℂ (G' k) (W k ∩ Z ×ˢ C')) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C' → fderiv ℂ (G' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C' → G' k p - G' l p = c k l p) → ∃ G'' : K → P × (Fin g → ℂ) → ℂ, ((∀ k, AnalyticOnNhd ℂ (G'' k) (W k ∩ Z ×ˢ (C ∪ C'))) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ (C ∪ C') → fderiv ℂ (G'' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ (C ∪ C') → G'' k p - G'' l p = c k l p) := by
  intro P _ _ _ g K W c ω Z C C' G G' hW hZ hC hCc hC' hC'c hne hcov ⟨hGa, hGd, hGc⟩
    ⟨hG'a, hG'd, hG'c⟩
  have hsubC : Z ×ˢ (C ∩ C') ⊆ Z ×ˢ C := prod_mono subset_rfl inter_subset_left
  have hsubC' : Z ×ˢ (C ∩ C') ⊆ Z ×ˢ C' := prod_mono subset_rfl inter_subset_right
  obtain ⟨h, hh, hGG⟩ := _root_.GlobalTheory.exists_analytic_param_of_primitives_on_box W c ω Z (C ∩ C') G G' hW hZ
    (hC.inter hC') (hCc.inter hC'c) hne
    (fun p hp => hcov p (prod_mono subset_rfl subset_union_left (hsubC hp)))
    ⟨fun k => (hGa k).mono (inter_subset_inter_right _ hsubC),
      fun k a p hpk hp => hGd k a p hpk (hsubC hp),
      fun k l p hk hl hp => hGc k l p hk hl (hsubC hp)⟩
    ⟨fun k => (hG'a k).mono (inter_subset_inter_right _ hsubC'),
      fun k a p hpk hp => hG'd k a p hpk (hsubC' hp),
      fun k l p hk hl hp => hG'c k l p hk hl (hsubC' hp)⟩
  classical
  have hCeq : ∀ k, ∀ q ∈ W k ∩ Z ×ˢ C,
      (if q.2 ∈ C then G k q else G' k q + h q.1) = G k q := fun k q hq => if_pos hq.2.2
  have hC'eq : ∀ k, ∀ q ∈ W k ∩ Z ×ˢ C',
      (if q.2 ∈ C then G k q else G' k q + h q.1) = G' k q + h q.1 := by
    intro k q hq
    split_ifs with hqC
    · exact hGG k q hq.1 ⟨hq.2.1, hqC, hq.2.2⟩
    · rfl
  have hU : ∀ k, IsOpen (W k ∩ Z ×ˢ C) := fun k => (hW k).inter (hZ.prod hC)
  have hU' : ∀ k, IsOpen (W k ∩ Z ×ˢ C') := fun k => (hW k).inter (hZ.prod hC')
  have evC : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C,
      (fun q => if q.2 ∈ C then G k q else G' k q + h q.1) =ᶠ[nhds p] G k :=
    fun k p hp => Filter.eventually_of_mem ((hU k).mem_nhds hp) (hCeq k)
  have evC' : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C',
      (fun q => if q.2 ∈ C then G k q else G' k q + h q.1) =ᶠ[nhds p]
        fun q => G' k q + h q.1 :=
    fun k p hp => Filter.eventually_of_mem ((hU' k).mem_nhds hp) (hC'eq k)
  have memcase : ∀ p ∈ Z ×ˢ (C ∪ C'), p ∈ Z ×ˢ C ∨ p ∈ Z ×ˢ C' := fun p hp =>
    hp.2.elim (fun h1 => Or.inl ⟨hp.1, h1⟩) (fun h2 => Or.inr ⟨hp.1, h2⟩)
  have hfd : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C', HasFDerivAt (fun q => G' k q + h q.1)
      (fderiv ℂ (G' k) p + (fderiv ℂ h p.1).comp (ContinuousLinearMap.fst ℂ P (Fin g → ℂ))) p :=
    fun k p hp => (hG'a k p hp).differentiableAt.hasFDerivAt.add
      ((hh p.1 hp.2.1).differentiableAt.hasFDerivAt.comp p (hasFDerivAt_fst))
  refine ⟨fun k => (fun k p => if p.2 ∈ C then G k p else G' k p + h p.1) k, ?_⟩
  refine ⟨fun k p hp => ?_, fun k a p hpk hp => ?_, fun k l p hk hl hp => ?_⟩
  · dsimp only
    rcases memcase p hp.2 with h1 | h2
    · exact (hGa k p ⟨hp.1, h1⟩).congr (evC k p ⟨hp.1, h1⟩).symm
    · exact (hfd k p ⟨hp.1, h2⟩).differentiableAt |> fun _ =>
        ((hG'a k p ⟨hp.1, h2⟩).add ((hh p.1 h2.1).comp analyticAt_fst)).congr
          (evC' k p ⟨hp.1, h2⟩).symm
  · dsimp only
    rcases memcase p hp with h1 | h2
    · rw [(evC k p ⟨hpk, h1⟩).fderiv_eq]
      exact hGd k a p hpk h1
    · rw [(evC' k p ⟨hpk, h2⟩).fderiv_eq, (hfd k p ⟨hpk, h2⟩).fderiv,
        ContinuousLinearMap.add_apply, hG'd k a p hpk h2]
      simp
  · dsimp only
    rcases memcase p hp with h1 | h2
    · rw [if_pos h1.2, if_pos h1.2]
      exact hGc k l p hk hl h1
    · rw [hC'eq k p ⟨hk, h2⟩, hC'eq l p ⟨hl, h2⟩, add_sub_add_right_eq_sub]
      exact hG'c k l p hk hl h2

end GlobalTheory
end

section
open Set

namespace GlobalTheory

set_option autoImplicit false in
open Set Metric in
private theorem hasFDerivAt_integral_unit_of_analytic {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (f : E × ℂ → ℂ) (O : Set (E × ℂ)) (hO : IsOpen O) (hf : AnalyticOnNhd ℂ f O) (S : Set E) (hS : IsOpen S)
    (hSO : ∀ x ∈ S, ∀ t ∈ Icc (0:ℝ) 1, (x, (t:ℂ)) ∈ O) (x₀ : E) (hx₀ : x₀ ∈ S) :
    HasFDerivAt (fun x => ∫ t in (0:ℝ)..1, f (x, (t:ℂ)))
      (∫ t in (0:ℝ)..1, (fderiv ℂ f (x₀, (t:ℂ))).comp (ContinuousLinearMap.inl ℂ E ℂ)) x₀ ∧
    IntervalIntegrable (fun t : ℝ => (fderiv ℂ f (x₀, (t:ℂ))).comp (ContinuousLinearMap.inl ℂ E ℂ)) MeasureTheory.volume 0 1 := by
  obtain ⟨ρ, hρ, hρS⟩ := Metric.isOpen_iff.1 hS x₀ hx₀
  have hsub : closedBall x₀ (ρ/2) ⊆ S := (closedBall_subset_ball (by linarith)).trans hρS
  set Kc : Set (E × ℂ) := closedBall x₀ (ρ/2) ×ˢ ((fun t : ℝ => (t:ℂ)) '' Icc 0 1) with hKc
  have hKcomp : IsCompact Kc := (isCompact_closedBall _ _).prod (isCompact_Icc.image Complex.continuous_ofReal)
  have hKO : Kc ⊆ O := by
    rintro ⟨x, τ⟩ ⟨hx, t, ht, rfl⟩
    exact hSO x (hsub hx) t ht
  have hcd : ContDiffOn ℂ 1 f O := hf.contDiffOn hO.uniqueDiffOn
  have hcont : ContinuousOn (fderiv ℂ f) O := hcd.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨M, hM⟩ := hKcomp.exists_bound_of_continuousOn (hcont.mono hKO)
  have hγ : ∀ x : E, Continuous (fun t : ℝ => (x, (t:ℂ))) := fun x => continuous_const.prodMk Complex.continuous_ofReal
  have hdiffAt : ∀ x ∈ S, ∀ t ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f (x, (t:ℂ)) :=
    fun x hx t ht => (hf _ (hSO x hx t ht)).differentiableAt
  have hcontf : ∀ x ∈ S, ContinuousOn (fun t : ℝ => f (x, (t:ℂ))) (Icc 0 1) := by
    intro x hx t ht
    exact ((hdiffAt x hx t ht).continuousAt.comp (x := t) (hγ x).continuousAt).continuousWithinAt
  have hIoc : uIoc (0:ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have hCl : ContinuousOn (fun t : ℝ => (fderiv ℂ f (x₀, (t:ℂ))).comp (ContinuousLinearMap.inl ℂ E ℂ)) (Icc 0 1) := by
    intro t ht
    have h1 : ContinuousAt (fun t : ℝ => fderiv ℂ f (x₀, (t:ℂ))) t :=
      (hcont.continuousAt (hO.mem_nhds (hSO x₀ hx₀ t ht))).comp (x := t) (hγ x₀).continuousAt
    exact (((ContinuousLinearMap.compL ℂ E (E × ℂ) ℂ).flip (ContinuousLinearMap.inl ℂ E ℂ)).continuous.continuousAt.comp (x := t) h1).continuousWithinAt
  refine ⟨?_, (hCl.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (bound := fun _ => M)
    (F' := fun x t => (fderiv ℂ f (x, (t:ℂ))).comp (ContinuousLinearMap.inl ℂ E ℂ))
    (ball_mem_nhds x₀ (half_pos hρ)) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [hS.mem_nhds hx₀] with x hx
    exact ((hcontf x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · exact ((hcontf x₀ hx₀).mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  · exact (hCl.mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    have hxK : (x, (t:ℂ)) ∈ Kc := ⟨ball_subset_closedBall hx, t, hIoc ht, rfl⟩
    calc ‖(fderiv ℂ f (x, (t:ℂ))).comp (ContinuousLinearMap.inl ℂ E ℂ)‖
        ≤ ‖fderiv ℂ f (x, (t:ℂ))‖ * ‖ContinuousLinearMap.inl ℂ E ℂ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * 1 := by
          gcongr
          · exact (norm_nonneg _).trans (hM _ hxK)
          · exact hM _ hxK
          · exact ContinuousLinearMap.norm_inl_le_one ℂ E ℂ
      _ = M := mul_one M
  · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    have hxS : x ∈ S := hsub (ball_subset_closedBall hx)
    exact (hdiffAt x hxS t (hIoc ht)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left x (t:ℂ))

set_option autoImplicit false in
open Set Metric in
private theorem integral_radial_derivative_eq {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {g : ℕ}
    (W : Set (P × (Fin g → ℂ))) (hW : IsOpen W) (ω : Fin g → P × (Fin g → ℂ) → ℂ) (hω : ∀ a, AnalyticOnNhd ℂ (ω a) W)
    (w₁ : Fin g → ℂ) (x : P × (Fin g → ℂ)) (a : Fin g) (hx : ∀ t ∈ Icc (0:ℝ) 1, (x.1, w₁ + (t:ℂ) • (x.2 - w₁)) ∈ W) :
    ∫ t in (0:ℝ)..1, ((t:ℂ) * fderiv ℂ (ω a) (x.1, w₁ + (t:ℂ) • (x.2 - w₁)) (0, x.2 - w₁) + ω a (x.1, w₁ + (t:ℂ) • (x.2 - w₁))) = ω a x := by
  have hcurve : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((x.1, w₁ + (t:ℂ) • (x.2 - w₁)) : P × (Fin g → ℂ))) ((0, x.2 - w₁) : P × (Fin g → ℂ)) t := by
    intro t
    refine (hasDerivAt_const _ _).prodMk ?_
    have := ((hasDerivAt_id t).ofReal_comp).smul_const (x.2 - w₁) |>.const_add w₁
    simpa using this
  have hd : ∀ t ∈ uIcc (0:ℝ) 1, HasDerivAt (fun t : ℝ => (t:ℂ) * ω a (x.1, w₁ + (t:ℂ) • (x.2 - w₁)))
      ((t:ℂ) * fderiv ℂ (ω a) (x.1, w₁ + (t:ℂ) • (x.2 - w₁)) (0, x.2 - w₁) + ω a (x.1, w₁ + (t:ℂ) • (x.2 - w₁))) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 := ((hω a _ (hx t ht)).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hcurve t)
    have h2 := ((hasDerivAt_id t).ofReal_comp).mul h1
    refine (h2.congr_deriv ?_ : _)
    simp only [id, Complex.ofReal_one, one_mul, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    exact add_comm _ _
  have hcont : ContinuousOn (fun t : ℝ => (t:ℂ) * fderiv ℂ (ω a) (x.1, w₁ + (t:ℂ) • (x.2 - w₁)) (0, x.2 - w₁) + ω a (x.1, w₁ + (t:ℂ) • (x.2 - w₁))) (uIcc 0 1) := by
    have hfc : ContinuousOn (fderiv ℂ (ω a)) W := ((hω a).contDiffOn hW.uniqueDiffOn (n := 1)).continuousOn_fderiv_of_isOpen hW le_rfl
    have hγc : Continuous (fun t : ℝ => ((x.1, w₁ + (t:ℂ) • (x.2 - w₁)) : P × (Fin g → ℂ))) :=
      continuous_const.prodMk (continuous_const.add (Complex.continuous_ofReal.smul continuous_const))
    rw [uIcc_of_le zero_le_one]
    intro t ht
    have hA : ContinuousAt (fun t : ℝ => fderiv ℂ (ω a) (x.1, w₁ + (t:ℂ) • (x.2 - w₁))) t :=
      (hfc.continuousAt (hW.mem_nhds (hx t ht))).comp (x := t) hγc.continuousAt
    have hB : ContinuousAt (fun t : ℝ => ω a (x.1, w₁ + (t:ℂ) • (x.2 - w₁))) t :=
      (hω a _ (hx t ht)).continuousAt.comp (x := t) hγc.continuousAt
    exact ((Complex.continuous_ofReal.continuousAt.mul (hA.clm_apply continuousAt_const)).add hB).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
  simp

set_option autoImplicit false in
open Set Metric in
private theorem hasDerivAt_radial_integrand {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] {g : ℕ}
    (W : Set (P × (Fin g → ℂ))) (ω : Fin g → P × (Fin g → ℂ) → ℂ) (hω : ∀ a, AnalyticOnNhd ℂ (ω a) W)
    (hcl : ∀ a b, ∀ p ∈ W, fderiv ℂ (ω b) p (0, Pi.single a 1) = fderiv ℂ (ω a) p (0, Pi.single b 1))
    (w₁ : Fin g → ℂ) (x : P × (Fin g → ℂ)) (τ : ℂ) (a : Fin g) (hq : (x.1, w₁ + τ • (x.2 - w₁)) ∈ W) :
    HasDerivAt (fun s : ℂ => ∑ c, ω c (x.1, w₁ + τ • (x.2 + s • (Pi.single a 1 : Fin g → ℂ) - w₁)) * ((x.2 + s • (Pi.single a 1 : Fin g → ℂ) - w₁ : Fin g → ℂ) c))
      (τ * fderiv ℂ (ω a) (x.1, w₁ + τ • (x.2 - w₁)) (0, x.2 - w₁) + ω a (x.1, w₁ + τ • (x.2 - w₁))) 0 := by
  set p := (x.1, w₁ + τ • (x.2 - w₁)) with hp
  have hline : ∀ c : Fin g, HasDerivAt (fun s : ℂ => ω c (x.1, w₁ + τ • (x.2 + s • (Pi.single a 1 : Fin g → ℂ) - w₁)))
      (fderiv ℂ (ω c) p (0, τ • Pi.single a 1)) 0 := by
    intro c
    have h1 : HasDerivAt (fun s : ℂ => ((x.1, w₁ + τ • (x.2 + s • (Pi.single a 1 : Fin g → ℂ) - w₁)) : P × (Fin g → ℂ)))
        ((0, τ • Pi.single a 1) : P × (Fin g → ℂ)) 0 := by
      refine (hasDerivAt_const _ _).prodMk ?_
      have := ((((hasDerivAt_id (0:ℂ)).smul_const (Pi.single a 1 : Fin g → ℂ)).const_add x.2).sub_const w₁).const_smul τ |>.const_add w₁
      simpa using this
    have h2 := (hω c p hq).differentiableAt.hasFDerivAt
    exact h2.comp_hasDerivAt_of_eq (0:ℂ) h1 (by simp [hp])
  have hcoord : ∀ c : Fin g, HasDerivAt (fun s : ℂ => ((x.2 + s • (Pi.single a 1 : Fin g → ℂ) - w₁ : Fin g → ℂ) c)) ((Pi.single a 1 : Fin g → ℂ) c) 0 := by
    intro c
    have := ((hasDerivAt_id (0:ℂ)).mul_const ((Pi.single a 1 : Fin g → ℂ) c)).const_add (x.2 c - w₁ c)
    have hfun : (fun s : ℂ => ((x.2 + s • (Pi.single a 1 : Fin g → ℂ) - w₁ : Fin g → ℂ) c)) = fun s => x.2 c - w₁ c + id s * (Pi.single a 1 : Fin g → ℂ) c := by
      funext s; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, id]; ring
    rw [hfun]
    simpa using this
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun c _ => (hline c).mul (hcoord c))
  refine HasDerivAt.congr_deriv hsum ?_
  symm
  · have hlin : fderiv ℂ (ω a) p (0, x.2 - w₁) = ∑ c, (x.2 - w₁) c * fderiv ℂ (ω a) p (0, Pi.single c 1) := by
      have hv : ((0 : P), x.2 - w₁) = ∑ c, (x.2 - w₁) c • ((0 : P), (Pi.single c 1 : Fin g → ℂ)) := by
        refine Prod.ext ?_ ?_
        · simp [Prod.fst_sum]
        · funext i
          simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
      rw [hv, map_sum]
      simp only [map_smul, smul_eq_mul]
    have hterm : ∀ c, fderiv ℂ (ω c) p (0, τ • Pi.single a 1) = τ * fderiv ℂ (ω a) p (0, Pi.single c 1) := by
      intro c
      have : ((0 : P), τ • (Pi.single a 1 : Fin g → ℂ)) = τ • ((0 : P), (Pi.single a 1 : Fin g → ℂ)) := by simp
      rw [this, map_smul, smul_eq_mul, hcl a c p hq]
    simp only [zero_smul, add_zero, hterm, Finset.sum_add_distrib, hlin, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl (fun c _ => by ring)
    · simp [Pi.single_apply, mul_ite, hp]

set_option autoImplicit false in
open Set Metric in
private theorem exists_fibre_primitive_on_ball {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ}
    (W : Set (P × (Fin g → ℂ))) (hW : IsOpen W) (ω : Fin g → P × (Fin g → ℂ) → ℂ) (hω : ∀ a, AnalyticOnNhd ℂ (ω a) W)
    (hcl : ∀ a b, ∀ p ∈ W, fderiv ℂ (ω b) p (0, Pi.single a 1) = fderiv ℂ (ω a) p (0, Pi.single b 1))
    (Z : Set P) (hZ : IsOpen Z) (w₁ : Fin g → ℂ) (r : ℝ) (hsub : Z ×ˢ ball w₁ r ⊆ W) :
    ∃ F : P × (Fin g → ℂ) → ℂ, AnalyticOnNhd ℂ F (Z ×ˢ ball w₁ r) ∧
      ∀ a, ∀ p ∈ Z ×ˢ ball w₁ r, fderiv ℂ F p (0, Pi.single a 1) = ω a p := by
  let γ : (P × (Fin g → ℂ)) × ℂ → P × (Fin g → ℂ) := fun q => (q.1.1, w₁ + q.2 • (q.1.2 - w₁))
  have hγ : ∀ q, AnalyticAt ℂ γ q := by
    intro q
    refine (analyticAt_fst.comp analyticAt_fst).prod ?_
    exact analyticAt_const.add (analyticAt_snd.smul ((analyticAt_snd.comp analyticAt_fst).sub analyticAt_const))
  let f : (P × (Fin g → ℂ)) × ℂ → ℂ := fun q => ∑ c, ω c (γ q) * (q.1.2 - w₁) c
  have hO : IsOpen (γ ⁻¹' W) := hW.preimage (continuous_iff_continuousAt.2 fun q => (hγ q).continuousAt)
  have hf : AnalyticOnNhd ℂ f (γ ⁻¹' W) := by
    intro q hq
    have e : f = ∑ c, fun q : (P × (Fin g → ℂ)) × ℂ => ω c (γ q) * (q.1.2 - w₁) c := by
      funext q'; simp [f, Finset.sum_apply]
    rw [e]
    refine Finset.analyticAt_sum Finset.univ (fun c _ => ?_)
    refine ((hω c _ hq).comp (hγ q)).mul ?_
    have : AnalyticAt ℂ (fun q : (P × (Fin g → ℂ)) × ℂ => q.1.2 - w₁) q := (analyticAt_snd.comp analyticAt_fst).sub analyticAt_const
    exact ((ContinuousLinearMap.proj c : (Fin g → ℂ) →L[ℂ] ℂ).analyticAt _).comp this
  have hS : IsOpen (Z ×ˢ ball w₁ r) := hZ.prod isOpen_ball
  have hSO : ∀ x ∈ Z ×ˢ ball w₁ r, ∀ t ∈ Icc (0:ℝ) 1, (x, (t:ℂ)) ∈ γ ⁻¹' W := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩ t ⟨h0, h1⟩
    apply hsub
    refine ⟨hz, ?_⟩
    show w₁ + (t:ℂ) • (w - w₁) ∈ ball w₁ r
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg h0]
    rw [mem_ball, dist_eq_norm] at hw
    nlinarith [norm_nonneg (w - w₁)]
  have hA := fun x hx => hasFDerivAt_integral_unit_of_analytic f _ hO hf _ hS hSO x hx
  refine ⟨fun x => ∫ t in (0:ℝ)..1, f (x, (t:ℂ)), ?_, ?_⟩
  · exact _root_.GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hS (fun x hx => (hA x hx).1.differentiableAt.differentiableWithinAt)
  · intro a x hx
    rw [(hA x hx).1.fderiv, ContinuousLinearMap.intervalIntegral_apply (hA x hx).2]
    rw [← integral_radial_derivative_eq W hW ω hω w₁ x a (fun t ht => hSO x hx t ht)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le zero_le_one] at ht
    have hq := hSO x hx t ht
    have hC := hasDerivAt_radial_integrand W ω hω hcl w₁ x (t:ℂ) a hq
    have hline : HasDerivAt (fun s : ℂ => (((x.1, x.2 + s • (Pi.single a 1 : Fin g → ℂ)), (t:ℂ)) : (P × (Fin g → ℂ)) × ℂ))
        (((0, (Pi.single a 1 : Fin g → ℂ)), 0) : (P × (Fin g → ℂ)) × ℂ) 0 := by
      refine ((hasDerivAt_const _ _).prodMk ?_).prodMk (hasDerivAt_const _ _)
      simpa using ((hasDerivAt_id (0:ℂ)).smul_const (Pi.single a 1 : Fin g → ℂ)).const_add x.2
    have hD := (hf _ hq).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℂ) hline (by simp)
    exact hD.unique hC

set_option autoImplicit false in
open Set Metric in
private theorem cech_shift_lemma_2 {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (S : Set (P × (Fin g → ℂ))) (j : K) (F : P × (Fin g → ℂ) → ℂ)
  (hW : ∀ k, IsOpen (W k)) (hS : IsOpen S) (hSj : S ⊆ W j)
  (hc : ∀ k l, AnalyticOnNhd ℂ (c k l) (W k ∩ W l))
  (hcoc : ∀ k l m, ∀ p ∈ W k, p ∈ W l → p ∈ W m → c k m p = c k l p + c l m p)
  (hdiff : ∀ k l a, ∀ p ∈ W k, p ∈ W l → ω k a p - ω l a p = fderiv ℂ (c k l) p (0, Pi.single a 1))
  (hF : AnalyticOnNhd ℂ F S) (hFd : ∀ a, ∀ p ∈ S, fderiv ℂ F p (0, Pi.single a 1) = ω j a p) :
  (∀ k, AnalyticOnNhd ℂ ((fun k p => F p - c j k p) k) (W k ∩ S)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ S → fderiv ℂ ((fun k p => F p - c j k p) k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ S → (fun k p => F p - c j k p) k p - (fun k p => F p - c j k p) l p = c k l p := by
  refine ⟨fun k p hp => ?_, fun k a p hpk hpS => ?_, fun k l p hpk hpl hpS => ?_⟩
  · exact (hF p hp.2).sub (hc j k p ⟨hSj hp.2, hp.1⟩)
  · have h1 := (hF p hpS).differentiableAt
    have h2 := (hc j k p ⟨hSj hpS, hpk⟩).differentiableAt
    have h3 := hdiff j k a p (hSj hpS) hpk
    simp only
    rw [show (fun q => F q - c j k q) = F - c j k from rfl, fderiv_sub h1 h2]
    simp only [ContinuousLinearMap.sub_apply, hFd a p hpS]
    linear_combination h3
  · have := hcoc j k l p (hSj hpS) hpk hpl
    simp only
    linear_combination this

set_option autoImplicit false in
open Set Metric in
private theorem convex_iUnion_ball_smul_Icc {g : ℕ} (w₀ : Fin g → ℂ) (ρ a b : ℝ) :
    Convex ℝ (⋃ u ∈ Icc a b, ball (u • w₀) ρ) := by
  intro x hx y hy s t hs ht hst
  simp only [mem_iUnion, exists_prop] at hx hy ⊢
  obtain ⟨u, hu, hxu⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  refine ⟨s * u + t * v, convex_Icc a b hu hv hs ht hst, ?_⟩
  have hx' : x - u • w₀ ∈ ball (0 : Fin g → ℂ) ρ := by rwa [mem_ball, dist_zero_right, ← dist_eq_norm]
  have hy' : y - v • w₀ ∈ ball (0 : Fin g → ℂ) ρ := by rwa [mem_ball, dist_zero_right, ← dist_eq_norm]
  have hc := convex_ball (0 : Fin g → ℂ) ρ hx' hy' hs ht hst
  rw [mem_ball, dist_zero_right] at hc
  rw [mem_ball, dist_eq_norm]
  have e : s • x + t • y - (s * u + t * v) • w₀ = s • (x - u • w₀) + t • (y - v • w₀) := by module
  rw [e]; exact hc

set_option autoImplicit false in
open Set Metric in
private theorem iUnion_ball_smul_Icc_union {g : ℕ} (w₀ : Fin g → ℂ) (ρ a m b : ℝ) (ham : a ≤ m) (hmb : m ≤ b) :
    (⋃ u ∈ Icc a m, ball (u • w₀) ρ) ∪ (⋃ u ∈ Icc m b, ball (u • w₀) ρ) = ⋃ u ∈ Icc a b, ball (u • w₀) ρ := by
  ext w
  simp only [mem_union, mem_iUnion, exists_prop, mem_Icc]
  constructor
  · rintro (⟨u, ⟨h1, h2⟩, h⟩ | ⟨u, ⟨h1, h2⟩, h⟩)
    · exact ⟨u, ⟨h1, h2.trans hmb⟩, h⟩
    · exact ⟨u, ⟨ham.trans h1, h2⟩, h⟩
  · rintro ⟨u, ⟨h1, h2⟩, h⟩
    rcases le_total u m with hum | hum
    · exact Or.inl ⟨u, ⟨h1, hum⟩, h⟩
    · exact Or.inr ⟨u, ⟨hum, h2⟩, h⟩

set_option autoImplicit false in
open Set Metric in

theorem _root_.GlobalTheory.exists_cechPrimitive_box_segment : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (V : Set P), IsOpen V → (∀ k, IsOpen (W k)) → (∀ p : P × (Fin g → ℂ), p.1 ∈ V → ∃ k, p ∈ W k) → (∀ k l, AnalyticOnNhd ℂ (c k l) (W k ∩ W l)) → (∀ k l m, ∀ p ∈ W k, p ∈ W l → p ∈ W m → c k m p = c k l p + c l m p) → (∀ k a, AnalyticOnNhd ℂ (ω k a) (W k)) → (∀ k a b, ∀ p ∈ W k, fderiv ℂ (ω k b) p (0, Pi.single a 1) = fderiv ℂ (ω k a) p (0, Pi.single b 1)) → (∀ k l a, ∀ p ∈ W k, p ∈ W l → ω k a p - ω l a p = fderiv ℂ (c k l) p (0, Pi.single a 1)) → ∀ z₀ ∈ V, ∀ w₀ : Fin g → ℂ, ∃ (Z : Set P) (C : Set (Fin g → ℂ)) (G : K → P × (Fin g → ℂ) → ℂ), IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ V ∧ IsOpen C ∧ Convex ℝ C ∧ 0 ∈ C ∧ w₀ ∈ C ∧ ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) := by
  intro P _ _ _ g K W c ω V hV hW hcov hc hcoc hω hcl hdiff z₀ hz₀ w₀
  have hloc : ∀ (Z : Set P), IsOpen Z → ∀ (w : Fin g → ℂ) (r : ℝ) (k₀ : K), Z ×ˢ ball w r ⊆ W k₀ →
      ∀ C' ⊆ ball w r, ∃ G : K → P × (Fin g → ℂ) → ℂ, (∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C')) ∧
        (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C' → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧
        ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C' → G k p - G l p = c k l p := by
    intro Z hZ w r k₀ hsub C' hC'
    obtain ⟨F, hF, hFd⟩ := exists_fibre_primitive_on_ball (W k₀) (hW k₀) (ω k₀) (hω k₀) (hcl k₀) Z hZ w r hsub
    obtain ⟨h1, h2, h3⟩ := cech_shift_lemma_2 W c ω (Z ×ˢ ball w r) k₀ F hW (hZ.prod isOpen_ball) hsub hc hcoc hdiff hF hFd
    have hm : Z ×ˢ C' ⊆ Z ×ˢ ball w r := prod_mono subset_rfl hC'
    exact ⟨fun k p => F p - c k₀ k p, fun k => (h1 k).mono (inter_subset_inter_right _ hm),
      fun k a p hp hq => h2 k a p hp (hm hq), fun k l p hk hl hq => h3 k l p hk hl (hm hq)⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV z₀ hz₀
  have hKc : IsCompact (({z₀} : Set P) ×ˢ ((fun u : ℝ => u • w₀) '' Icc 0 1)) :=
    isCompact_singleton.prod (isCompact_Icc.image (continuous_id.smul continuous_const))
  have hKcov : ({z₀} : Set P) ×ˢ ((fun u : ℝ => u • w₀) '' Icc 0 1) ⊆ ⋃ k, W k := by
    rintro ⟨z, w⟩ ⟨hz, -⟩
    rw [mem_singleton_iff] at hz
    obtain ⟨k, hk⟩ := hcov (z, w) (by rw [hz]; exact hz₀)
    exact mem_iUnion.2 ⟨k, hk⟩
  obtain ⟨δ, hδ, hδW⟩ := lebesgue_number_lemma_of_metric hKc hW hKcov
  have hη : 0 < min ε δ := lt_min hε hδ
  have hball : ∀ u ∈ Icc (0:ℝ) 1, ∃ k, ball z₀ (min ε δ) ×ˢ ball (u • w₀) (min ε δ) ⊆ W k := by
    intro u hu
    obtain ⟨k, hk⟩ := hδW (z₀, u • w₀) ⟨rfl, u, hu, rfl⟩
    refine ⟨k, fun p hp => hk ?_⟩
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_right _ _) hp.1, ball_subset_ball (min_le_right _ _) hp.2⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖w₀‖ / min ε δ)
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hstep : ‖w₀‖ / N ≤ min ε δ / 2 := by
    rw [div_le_iff₀ hNpos]
    rw [div_lt_iff₀ hη] at hN
    nlinarith
  have hZV : ball z₀ (min ε δ) ⊆ V := (ball_subset_ball (min_le_left _ _)).trans hεV
  have hpiece : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b - a ≤ 1 / N → a ≤ b →
      ∃ G : K → P × (Fin g → ℂ) → ℂ,
        (∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ ball z₀ (min ε δ) ×ˢ (⋃ u ∈ Icc a b, ball (u • w₀) (min ε δ / 2)))) ∧
        (∀ k a', ∀ p ∈ W k, p ∈ ball z₀ (min ε δ) ×ˢ (⋃ u ∈ Icc a b, ball (u • w₀) (min ε δ / 2)) →
          fderiv ℂ (G k) p (0, Pi.single a' 1) = ω k a' p) ∧
        ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ ball z₀ (min ε δ) ×ˢ (⋃ u ∈ Icc a b, ball (u • w₀) (min ε δ / 2)) →
          G k p - G l p = c k l p := by
    intro a b ha hab hab'
    obtain ⟨k, hk⟩ := hball a ha
    refine hloc _ isOpen_ball (a • w₀) (min ε δ) k hk _ ?_
    intro w hw
    simp only [mem_iUnion, exists_prop, mem_Icc] at hw
    obtain ⟨u, ⟨hu1, hu2⟩, hwu⟩ := hw
    rw [mem_ball] at hwu ⊢
    have hd : dist (u • w₀) (a • w₀) ≤ min ε δ / 2 := by
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_of_nonneg (by linarith)]
      calc (u - a) * ‖w₀‖ ≤ (1 / N) * ‖w₀‖ := by gcongr; linarith
        _ = ‖w₀‖ / N := by ring
        _ ≤ min ε δ / 2 := hstep
    calc dist w (a • w₀) ≤ dist w (u • w₀) + dist (u • w₀) (a • w₀) := dist_triangle _ _ _
      _ < min ε δ / 2 + min ε δ / 2 := add_lt_add_of_lt_of_le hwu hd
      _ = min ε δ := by ring
  have hind : ∀ n : ℕ, n ≤ N → ∃ G : K → P × (Fin g → ℂ) → ℂ,
        (∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ ball z₀ (min ε δ) ×ˢ (⋃ u ∈ Icc 0 ((n:ℝ) / N), ball (u • w₀) (min ε δ / 2)))) ∧
        (∀ k a', ∀ p ∈ W k, p ∈ ball z₀ (min ε δ) ×ˢ (⋃ u ∈ Icc 0 ((n:ℝ) / N), ball (u • w₀) (min ε δ / 2)) →
          fderiv ℂ (G k) p (0, Pi.single a' 1) = ω k a' p) ∧
        ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ ball z₀ (min ε δ) ×ˢ (⋃ u ∈ Icc 0 ((n:ℝ) / N), ball (u • w₀) (min ε δ / 2)) →
          G k p - G l p = c k l p := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [Nat.cast_zero, zero_div]
      exact hpiece 0 0 ⟨le_rfl, zero_le_one⟩ (by rw [sub_zero]; positivity) le_rfl
    | succ n ih =>
      intro hn
      obtain ⟨G, hG⟩ := ih (Nat.le_of_succ_le hn)
      have hn0 : (0:ℝ) ≤ n / N := by positivity
      have hn1 : (n:ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast Nat.le_of_succ_le hn
      have hnn : (n:ℝ) / N ≤ ((n + 1 : ℕ) : ℝ) / N := by
        gcongr; exact_mod_cast Nat.le_succ n
      obtain ⟨G', hG'⟩ := hpiece ((n:ℝ) / N) (((n + 1 : ℕ) : ℝ) / N) ⟨hn0, hn1⟩
        (by push_cast; rw [add_div]; linarith) hnn
      obtain ⟨G'', hG''⟩ := _root_.GlobalTheory.exists_merge_fibre_primitives W c ω (ball z₀ (min ε δ))
        (⋃ u ∈ Icc 0 ((n:ℝ) / N), ball (u • w₀) (min ε δ / 2))
        (⋃ u ∈ Icc ((n:ℝ) / N) (((n + 1 : ℕ) : ℝ) / N), ball (u • w₀) (min ε δ / 2)) G G' hW isOpen_ball
        (isOpen_biUnion fun _ _ => isOpen_ball) (convex_iUnion_ball_smul_Icc w₀ _ _ _)
        (isOpen_biUnion fun _ _ => isOpen_ball) (convex_iUnion_ball_smul_Icc w₀ _ _ _)
        ⟨((n:ℝ) / N) • w₀, mem_iUnion₂.2 ⟨(n:ℝ) / N, ⟨hn0, le_rfl⟩, mem_ball_self (half_pos hη)⟩,
          mem_iUnion₂.2 ⟨(n:ℝ) / N, ⟨le_rfl, hnn⟩, mem_ball_self (half_pos hη)⟩⟩
        (fun p hp => hcov p (hZV hp.1)) hG hG'
      rw [iUnion_ball_smul_Icc_union w₀ _ 0 ((n:ℝ) / N) (((n + 1 : ℕ) : ℝ) / N) hn0 hnn] at hG''
      exact ⟨G'', hG''⟩
  obtain ⟨G, hG⟩ := hind N le_rfl
  rw [div_self hNpos.ne'] at hG
  refine ⟨ball z₀ (min ε δ), ⋃ u ∈ Icc (0:ℝ) 1, ball (u • w₀) (min ε δ / 2), G, isOpen_ball, mem_ball_self hη, hZV,
    isOpen_biUnion fun _ _ => isOpen_ball, convex_iUnion_ball_smul_Icc w₀ _ 0 1, ?_, ?_, hG⟩
  · exact mem_iUnion₂.2 ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa using half_pos hη⟩
  · exact mem_iUnion₂.2 ⟨1, ⟨zero_le_one, le_rfl⟩, by simpa using half_pos hη⟩

end GlobalTheory
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

set_option autoImplicit false in
open CategoryTheory TopologicalSpace in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} in
private theorem exists_global_cechPrimitive_of_zero_section_lemma
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type}
    (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ)
    (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (V : Set P) (hV : IsOpen V) (hW : ∀ k, IsOpen (W k))
    (hcov : ∀ p : P × (Fin g → ℂ), p.1 ∈ V → ∃ k, p ∈ W k)
    (hc : ∀ k l, AnalyticOnNhd ℂ (c k l) (W k ∩ W l))
    (hcoc : ∀ k l m, ∀ p ∈ W k, p ∈ W l → p ∈ W m → c k m p = c k l p + c l m p)
    (hω : ∀ k a, AnalyticOnNhd ℂ (ω k a) (W k))
    (hcl : ∀ k a b, ∀ p ∈ W k,
      fderiv ℂ (ω k b) p (0, Pi.single a 1) = fderiv ℂ (ω k a) p (0, Pi.single b 1))
    (hd : ∀ k l a, ∀ p ∈ W k, p ∈ W l →
      ω k a p - ω l a p = fderiv ℂ (c k l) p (0, Pi.single a 1))
    (k₀ : K) (h₀ : ∀ z ∈ V, (z, (0 : Fin g → ℂ)) ∈ W k₀) :
    ∃ G : K → P × (Fin g → ℂ) → ℂ,
      (∀ k, ∀ p ∈ W k, p.1 ∈ V → AnalyticAt ℂ (G k) p) ∧
      (∀ k a, ∀ p ∈ W k, p.1 ∈ V → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧
      (∀ k l, ∀ p ∈ W k, p ∈ W l → p.1 ∈ V → G k p - G l p = c k l p) := by
  have box := _root_.GlobalTheory.exists_cechPrimitive_box_segment W c ω V hV hW hcov hc hcoc hω hcl hd
  have box' : ∀ q : P × (Fin g → ℂ), ∃ Z : Set P, ∃ C : Set (Fin g → ℂ),
      ∃ G : K → P × (Fin g → ℂ) → ℂ, q.1 ∈ V →
        (IsOpen Z ∧ q.1 ∈ Z ∧ Z ⊆ V ∧ IsOpen C ∧ Convex ℝ C ∧ (0 : Fin g → ℂ) ∈ C ∧ q.2 ∈ C ∧
        (∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧
        (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧
        ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) := by
    intro q
    by_cases hq : q.1 ∈ V
    · obtain ⟨Z, C, G, h⟩ := box q.1 hq q.2
      exact ⟨Z, C, G, fun _ => h⟩
    · exact ⟨∅, ∅, fun _ _ => 0, fun h => absurd h hq⟩
  choose Z C G hG using box'
  choose κ hκ using hcov

  have hfib : ∀ q, q.1 ∈ V → ∀ k, ∀ y ∈ W k, y ∈ Z q ×ˢ C q → ∀ v : Fin g → ℂ,
      fderiv ℂ (G q k) y ((0 : P), v) = ∑ a, v a * ω k a y := by
    intro q hq k y hy hyB v
    have hv : ((0 : P), v) = ∑ a, v a • ((0 : P), (Pi.single a (1 : ℂ) : Fin g → ℂ)) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul, (hG q hq).2.2.2.2.2.2.2.2.1 k a y hy hyB]
  set H : P × (Fin g → ℂ) → K → P × (Fin g → ℂ) → ℂ :=
    fun q k x => G q k x - G q k₀ (x.1, 0) with hH
  have huniq : ∀ q q' k x, q.1 ∈ V → q'.1 ∈ V → x ∈ W k → x.1 ∈ Z q → x.1 ∈ Z q' →
      x.2 ∈ C q → x.2 ∈ C q' → H q k x = H q' k x := by
    intro q q' k x hq hq' hxk hz hz' hw hw'
    obtain ⟨-, -, hZV, hCo, hCc, h0C, -, hGa, -, hGc⟩ := hG q hq
    obtain ⟨-, -, -, hCo', hCc', h0C', -, hGa', -, hGc'⟩ := hG q' hq'
    have hzV : x.1 ∈ V := hZV hz
    have hind : ∀ k k' (y : P × (Fin g → ℂ)), y ∈ W k → y ∈ W k' → y.1 ∈ Z q → y.1 ∈ Z q' →
        y.2 ∈ C q → y.2 ∈ C q' → G q k y - G q' k y = G q k' y - G q' k' y := by
      intro k k' y hk hk' h1 h2 h3 h4
      have e1 := hGc k k' y hk hk' ⟨h1, h3⟩
      have e2 := hGc' k k' y hk hk' ⟨h2, h4⟩
      linear_combination e1 - e2
    set φ : (Fin g → ℂ) → ℂ := fun w =>
      G q (κ (x.1, w) hzV) (x.1, w) - G q' (κ (x.1, w) hzV) (x.1, w) with hφ
    have hS : IsOpen (C q ∩ C q') := hCo.inter hCo'
    have hderiv : ∀ w ∈ C q ∩ C q', HasFDerivAt φ (0 : (Fin g → ℂ) →L[ℂ] ℂ) w := by
      intro w hw
      set k := κ (x.1, w) hzV
      have hk : (x.1, w) ∈ W k := hκ (x.1, w) hzV
      have hU : IsOpen ({w' | (x.1, w') ∈ W k} ∩ (C q ∩ C q')) :=
        ((hW k).preimage (continuous_const.prodMk continuous_id)).inter hS
      have heq : (fun w' => G q k (x.1, w') - G q' k (x.1, w')) =ᶠ[nhds w] φ := by
        filter_upwards [hU.mem_nhds ⟨hk, hw⟩] with w' hw'
        exact hind k _ (x.1, w') hw'.1 (hκ (x.1, w') hzV) hz hz' hw'.2.1 hw'.2.2
      have hA : HasFDerivAt (G q k) (fderiv ℂ (G q k) (x.1, w)) (x.1, w) :=
        ((hGa k (x.1, w) ⟨hk, hz, hw.1⟩).differentiableAt).hasFDerivAt
      have hA' : HasFDerivAt (G q' k) (fderiv ℂ (G q' k) (x.1, w)) (x.1, w) :=
        ((hGa' k (x.1, w) ⟨hk, hz', hw.2⟩).differentiableAt).hasFDerivAt
      have hin : HasFDerivAt (fun w' : Fin g → ℂ => (x.1, w'))
          ((0 : (Fin g → ℂ) →L[ℂ] P).prod (ContinuousLinearMap.id ℂ (Fin g → ℂ))) w :=
        (hasFDerivAt_const x.1 w).prodMk (hasFDerivAt_id w)
      have hsum := (hA.comp w hin).sub (hA'.comp w hin)
      refine (hsum.congr_of_eventuallyEq heq.symm).congr_fderiv ?_
      ext v
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.prod_apply, ContinuousLinearMap.zero_apply,
        ContinuousLinearMap.id_apply]
      rw [hfib q hq k _ hk ⟨hz, hw.1⟩, hfib q' hq' k _ hk ⟨hz', hw.2⟩, sub_self]
    have hconst : φ x.2 = φ 0 := by
      refine Convex.is_const_of_fderivWithin_eq_zero (hCc.inter hCc')
        (fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt)
        (fun w hw => ?_) ⟨hw, hw'⟩ ⟨h0C, h0C'⟩
      rw [fderivWithin_of_isOpen hS hw, (hderiv w hw).fderiv]
    have e1 : φ x.2 = G q k x - G q' k x :=
      hind _ k (x.1, x.2) (hκ (x.1, x.2) hzV) hxk hz hz' hw hw'
    have e2 : φ 0 = G q k₀ (x.1, 0) - G q' k₀ (x.1, 0) :=
      hind _ k₀ (x.1, 0) (hκ (x.1, 0) hzV) (h₀ _ hzV) hz hz' h0C h0C'
    simp only [hH]
    linear_combination e1.symm.trans (hconst.trans e2)
  have hloc : ∀ k x, x ∈ W k → x.1 ∈ V →
      (fun y => H y k y) =ᶠ[nhds x] H x k := by
    intro k x hxk hxV
    obtain ⟨hZo, hxZ, hZV, hCo, -, -, hxC, -⟩ := hG x hxV
    filter_upwards [((hW k).inter (hZo.prod hCo)).mem_nhds ⟨hxk, hxZ, hxC⟩] with y hy
    have hyV : y.1 ∈ V := hZV hy.2.1
    obtain ⟨-, hyZ, -, -, -, -, hyC, -⟩ := hG y hyV
    exact huniq y x k y hyV hxV hy.1 hyZ hy.2.1 hyC hy.2.2
  set L : P × (Fin g → ℂ) →L[ℂ] P × (Fin g → ℂ) :=
    (ContinuousLinearMap.fst ℂ P (Fin g → ℂ)).prod 0 with hL
  have hfun : ∀ x k, H x k = G x k - G x k₀ ∘ L := by
    intro x k
    funext y
    simp [hH, hL]
  refine ⟨fun k y => H y k y, ?_, ?_, ?_⟩
  · intro k x hxk hxV
    obtain ⟨-, hxZ, -, -, -, h0C, hxC, hGa, -⟩ := hG x hxV
    have h1 : AnalyticAt ℂ (G x k) x := hGa k x ⟨hxk, hxZ, hxC⟩
    have h2 : AnalyticAt ℂ (G x k₀) (L x) := hGa k₀ (x.1, 0) ⟨h₀ _ hxV, hxZ, h0C⟩
    have h3 := (h1.sub (h2.comp (L.analyticAt x)))
    rw [← hfun] at h3
    exact h3.congr (hloc k x hxk hxV).symm
  · intro k a x hxk hxV
    obtain ⟨-, hxZ, -, -, -, h0C, hxC, hGa, hGd, -⟩ := hG x hxV
    have h1 : HasFDerivAt (G x k) (fderiv ℂ (G x k) x) x :=
      (hGa k x ⟨hxk, hxZ, hxC⟩).differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (G x k₀) (fderiv ℂ (G x k₀) (L x)) (L x) :=
      (hGa k₀ (x.1, 0) ⟨h₀ _ hxV, hxZ, h0C⟩).differentiableAt.hasFDerivAt
    have h3 := h1.sub (h2.comp x L.hasFDerivAt)
    rw [← hfun] at h3
    rw [(hloc k x hxk hxV).fderiv_eq, h3.fderiv]
    have hL0 : L ((0 : P), (Pi.single a (1 : ℂ) : Fin g → ℂ)) = 0 := by simp [hL]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, hL0, map_zero, sub_zero,
      hGd k a x hxk ⟨hxZ, hxC⟩]
  · intro k l x hxk hxl hxV
    obtain ⟨-, hxZ, -, -, -, -, hxC, -, -, hGc⟩ := hG x hxV
    simp only [hH]
    linear_combination hGc k l x hxk hxl ⟨hxZ, hxC⟩

set_option autoImplicit false in
open CategoryTheory TopologicalSpace in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} in
private theorem hol_sub_fn {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : TopologicalSpace.Opens E} (f h : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f - h).fn p = f.fn p - h.fn p := by
  rw [← _root_.GlobalTheory.AnPer.Hol.ev_apply p hp, map_sub,
    _root_.GlobalTheory.AnPer.Hol.ev_apply, _root_.GlobalTheory.AnPer.Hol.ev_apply]

set_option autoImplicit false in
open CategoryTheory TopologicalSpace in
variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  {F : _root_.GlobalTheory.AnPer.Fam I g Λ} in

theorem _root_.GlobalTheory.AnPer.Charts.exists_primitive_of_rich {I : Type} [Fintype I] {g : ℕ} {Λ : Type}
    [AddCommGroup Λ] {F : _root_.GlobalTheory.AnPer.Fam I g Λ}
    (K : _root_.GlobalTheory.AnPer.Charts F) (hR : K.Rich)
    (hB : K.Based)
    (a : ∀ k k', K.le 0 k' k → _root_.GlobalTheory.AnPer.Hol (K.W k'))
    (ω : ∀ k, Fin g → _root_.GlobalTheory.AnPer.Hol (K.W k))
    (hcoc : ∀ k k' k'' (e : K.le 0 k' k)
      (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k),
      a k k'' e'' = _root_.GlobalTheory.AnPer.Charts.sh e' (a k k' e) + a k' k'' e')
    (hcl : ∀ k i j, _root_.GlobalTheory.AnPer.dw i (ω k j) =
      _root_.GlobalTheory.AnPer.dw j (ω k i))
    (hd : ∀ k k' (e : K.le 0 k' k) i,
      ω k' i - _root_.GlobalTheory.AnPer.Charts.sh e (ω k i) =
        _root_.GlobalTheory.AnPer.dw i (a k k' e)) :
    ∃ G : ∀ k, _root_.GlobalTheory.AnPer.Hol (K.W k),
      (∀ k i, _root_.GlobalTheory.AnPer.dw i (G k) = ω k i) ∧
      ∀ k k' (e : K.le 0 k' k),
        a k k' e = G k' - _root_.GlobalTheory.AnPer.Charts.sh e (G k) := by
  classical
  obtain ⟨hcov, hmeet⟩ := hR
  obtain ⟨k₀, hk₀⟩ := hB
  have hsub : ∀ {k k' : K.K}, K.le 0 k' k → ∀ p ∈ K.W k', p ∈ K.W k := by
    intro k k' e p hp
    have := K.maps e p hp
    rwa [_root_.GlobalTheory.AnPer.Fam.shift_zero] at this
  have htrans : ∀ {k k' k'' : K.K}, K.le 0 k' k → K.le 0 k'' k' → K.le 0 k'' k := by
    intro k k' k'' e e'
    simpa using K.le_trans e e'
  have hsh : ∀ {k k' : K.K} (e : K.le 0 k' k) (f : _root_.GlobalTheory.AnPer.Hol (K.W k)),
      ∀ p ∈ K.W k', (_root_.GlobalTheory.AnPer.Charts.sh e f).fn p = f.fn p := by
    intro k k' e f p hp
    rw [_root_.GlobalTheory.AnPer.Charts.fn_sh e f hp, _root_.GlobalTheory.AnPer.Fam.shift_zero]
  have hdw : ∀ {k : K.K} (i : Fin g) (f : _root_.GlobalTheory.AnPer.Hol (K.W k)), ∀ p ∈ K.W k,
      (_root_.GlobalTheory.AnPer.dw i f).fn p = fderiv ℂ f.fn p (0, Pi.single i 1) := by
    intro k i f p hp
    exact _root_.GlobalTheory.AnPer.Hol.fn_der _ f hp

  have hpc : ∀ k k' k'' (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k),
      ∀ p ∈ K.W k'', (a k k'' e'').fn p = (a k k' e).fn p + (a k' k'' e').fn p := by
    intro k k' k'' e e' e'' p hp
    rw [hcoc k k' k'' e e' e'', _root_.GlobalTheory.AnPer.Hol.fn_add _ _ hp, hsh e' _ p hp]
  have hmeet0 : ∀ (k₁ k₂ : K.K) (p : _root_.GlobalTheory.AnPer.Tot I g), p ∈ K.W k₁ →
      p ∈ K.W k₂ → ∃ k, p ∈ K.W k ∧ K.le 0 k k₁ ∧ K.le 0 k k₂ := by
    intro k₁ k₂ p h₁ h₂
    exact hmeet 0 k₁ k₂ p h₁ (by rwa [_root_.GlobalTheory.AnPer.Fam.shift_zero])
  choose! μ hμ using hmeet0

  let c : K.K → K.K → _root_.GlobalTheory.AnPer.Tot I g → ℂ := fun k₁ k₂ p =>
    if h : p ∈ K.W k₁ ∧ p ∈ K.W k₂ then
      (a k₂ (μ k₁ k₂ p) (hμ k₁ k₂ p h.1 h.2).2.2).fn p -
        (a k₁ (μ k₁ k₂ p) (hμ k₁ k₂ p h.1 h.2).2.1).fn p
    else 0
  have hind : ∀ (k₁ k₂ k : K.K) (e₁ : K.le 0 k k₁) (e₂ : K.le 0 k k₂), ∀ p ∈ K.W k,
      c k₁ k₂ p = (a k₂ k e₂).fn p - (a k₁ k e₁).fn p := by
    intro k₁ k₂ k e₁ e₂ p hp
    have h₁ := hsub e₁ p hp
    have h₂ := hsub e₂ p hp
    simp only [c, dif_pos (And.intro h₁ h₂)]
    obtain ⟨hpm, em₁, em₂⟩ := hμ k₁ k₂ p h₁ h₂
    set k' := μ k (μ k₁ k₂ p) p with hk'
    obtain ⟨hpk', f₁, f₂⟩ := hμ k (μ k₁ k₂ p) p hp hpm
    have r1 := hpc k₁ k k' e₁ f₁ (htrans e₁ f₁) p hpk'
    have r2 := hpc k₂ k k' e₂ f₁ (htrans e₂ f₁) p hpk'
    have r3 := hpc k₁ _ k' em₁ f₂ (htrans e₁ f₁) p hpk'
    have r4 := hpc k₂ _ k' em₂ f₂ (htrans e₂ f₁) p hpk'
    linear_combination r3 - r4 - r1 + r2
  obtain ⟨Gf, hGa, hGd, hGc⟩ := exists_global_cechPrimitive_of_zero_section_lemma
    (P := I → ℂ) (g := g) (fun k => (K.W k : Set (_root_.GlobalTheory.AnPer.Tot I g))) c
    (fun k i => (ω k i).fn) (F.V : Set (I → ℂ)) F.V.isOpen (fun k => (K.W k).isOpen) hcov
    (by
      intro k₁ k₂ p hp
      obtain ⟨hpk, e₁, e₂⟩ := hμ k₁ k₂ p hp.1 hp.2
      have hev : (fun q => (a k₂ _ e₂).fn q - (a k₁ _ e₁).fn q) =ᶠ[nhds p] c k₁ k₂ := by
        filter_upwards [(K.W _).isOpen.mem_nhds hpk] with q hq
        exact (hind k₁ k₂ _ e₁ e₂ q hq).symm
      exact (((a k₂ _ e₂).analytic p hpk).sub
        ((a k₁ _ e₁).analytic p hpk)).congr hev)
    (by
      intro k l m p hk hl hm
      obtain ⟨hp', e₁, e₂⟩ := hμ k l p hk hl
      obtain ⟨hp'', f₁, f₂⟩ := hμ _ m p hp' hm
      rw [hind k m _ (htrans e₁ f₁) f₂ p hp'', hind k l _ (htrans e₁ f₁) (htrans e₂ f₁) p hp'',
        hind l m _ (htrans e₂ f₁) f₂ p hp'']
      ring)
    (fun k i => (ω k i).analytic)
    (by
      intro k i j p hp
      rw [← hdw i _ p hp, ← hdw j _ p hp, hcl])
    (by
      intro k₁ k₂ i p h₁ h₂
      obtain ⟨hpk, e₁, e₂⟩ := hμ k₁ k₂ p h₁ h₂
      have hev : ((a k₂ _ e₂).fn - (a k₁ _ e₁).fn) =ᶠ[nhds p] c k₁ k₂ := by
        filter_upwards [(K.W _).isOpen.mem_nhds hpk] with q hq
        exact (hind k₁ k₂ _ e₁ e₂ q hq).symm
      have d₁ := ((a k₁ _ e₁).analytic p hpk).differentiableAt
      have d₂ := ((a k₂ _ e₂).analytic p hpk).differentiableAt
      have hfd := (d₂.hasFDerivAt.sub d₁.hasFDerivAt).fderiv
      rw [← hev.fderiv_eq]
      rw [hfd, ContinuousLinearMap.sub_apply, ← hdw i _ p hpk,
        ← hdw i _ p hpk, ← hd k₂ _ e₂ i, ← hd k₁ _ e₁ i, hol_sub_fn _ _ hpk,
        hol_sub_fn _ _ hpk, hsh e₂ _ p hpk, hsh e₁ _ p hpk]
      ring)
    k₀ hk₀
  set Gh : ∀ k, _root_.GlobalTheory.AnPer.Hol (K.W k) := fun k =>
    _root_.GlobalTheory.AnPer.Hol.mk (Gf k)
      (fun p hp => hGa k p hp (K.base k p hp)) with hGh
  have hfn : ∀ k, ∀ q ∈ K.W k, (Gh k).fn q = Gf k q := fun k q hq =>
    _root_.GlobalTheory.AnPer.Hol.fn_mk _ _ hq
  refine ⟨Gh, ?_, ?_⟩
  · intro k i
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    rw [hdw i (Gh k) p hp, _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr (Gh k) (hfn k) hp]
    exact hGd k i p hp (K.base k p hp)
  · intro k k' e
    apply _root_.GlobalTheory.AnPer.Hol.ext_fn
    intro p hp
    rw [hol_sub_fn _ _ hp, hsh e _ p hp]
    rw [hfn k' p hp, hfn k p (hsub e p hp)]
    have h1 := hGc k k' p (hsub e p hp) hp (K.base k' p hp)
    have h2 := hind k k' k' e (K.le_refl k') p hp
    have h3 := hpc k' k' k' (K.le_refl k') (K.le_refl k') (K.le_refl k') p hp
    linear_combination h1 + h2 - h3

end GlobalTheory.AnPer.Charts
end
end

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_cech_poincare_rich_charts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (a : ∀ k k', K.le 0 k' k → Hol (K.W k')) (ω : ∀ k, Fin g → Hol (K.W k)), (∀ k k' k'' (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k), a k k'' e'' = sh e' (a k k' e) + a k' k'' e') → (∀ k i j, dw i (ω k j) = dw j (ω k i)) → (∀ k k' (e : K.le 0 k' k) i, ω k' i - sh e (ω k i) = dw i (a k k' e)) → ∃ G : ∀ k, Hol (K.W k), (∀ k i, dw i (G k) = ω k i) ∧ ∀ k k' (e : K.le 0 k' k), a k k' e = G k' - sh e (G k) := by
  atlas_forward_decl GlobalTheory.AnPer.Charts.exists_primitive_of_rich
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts.DegZero

theorem sub_rel {M : Type} [AddCommGroup M] {p0 p1 u0 u1 v0 v1 w z0 z1 : M}
    (c0 : p0 = u0 + w) (c0' : p0 = v0 + z0) (c1 : p1 = u1 + w) (c1' : p1 = v1 + z1) :
    u0 - u1 = v0 - v1 + (z0 - z1) := by
  have e0 : u0 = v0 + z0 - w := eq_sub_of_add_eq (c0.symm.trans c0')
  have e1 : u1 = v1 + z1 - w := eq_sub_of_add_eq (c1.symm.trans c1')
  rw [e0, e1]; abel

theorem sub_sub_eq_of_sub_eq_addCommGroup {M : Type} [AddCommGroup M] {h0 h1 j0 j1 d X : M}
    (e : h0 - h1 = d) (e' : j1 - j0 = d) : h0 - (X - j0) = h1 - (X - j1) := by
  have a0 : h0 = d + h1 := eq_add_of_sub_eq e
  have a1 : j1 = d + j0 := eq_add_of_sub_eq e'
  rw [a0, a1]; abel

theorem eq_inr {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    (x : TrivSqZeroExt O M) (hx : x.fst = 0) : x = TrivSqZeroExt.inr x.snd :=
  TrivSqZeroExt.ext hx rfl

theorem tszeSec_sub_inl {g : ℕ} {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) (x : O) :
    tszeSec D x - TrivSqZeroExt.inl x = TrivSqZeroExt.inr fun a ↦ D a x := by
  show TrivSqZeroExt.inl x + TrivSqZeroExt.inr (fun a ↦ D a x) - TrivSqZeroExt.inl x = _
  abel

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

theorem translationChartShiftSubstitution_comp_degZero {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k)
    (f : Hol (K.W k)) : sh e' (sh e f) = sh e'' f :=
  Hol.ext_fn fun p hp ↦ by
    rw [fn_sh e' _ hp, fn_sh e _ (K.maps e' p hp), fn_sh e'' _ hp]
    simp only [F.shift_zero]

theorem ptHom_refl_triv (k : K.K) : ptHom (K.triv k) (K.le_refl k) = 𝟙 (K.triv k) :=
  hom_ext (fun c ↦ sh_refl (K.le_refl k) c) rfl

theorem ptHom_comp0 {k k' k'' : K.K} (e : K.le 0 k' k) (e' : K.le 0 k'' k') (e'' : K.le 0 k'' k) :
    ptHom (K.triv k') e ≫ ptHom (K.triv k'') e' = ptHom (K.triv k'') e'' :=
  hom_ext (fun c ↦ translationChartShiftSubstitution_comp_degZero e e' e'' c) (add_zero (0 : Λ))

def corr (h : C1 K.Oc) (G : C0 K.Oc) : C1 K.Oc := fun T T' φ ↦ h T T' φ - (G T' - φ.φ (G T))

theorem zero_id (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (T : K.Obj) : h T T (𝟙 T) = 0 := by
  have e := hc T T T (𝟙 T) (𝟙 T) rfl rfl
  rw [Category.id_comp] at e
  change (h T T (𝟙 T) : T.C) = h T T (𝟙 T) + h T T (𝟙 T) at e
  exact (add_eq_left.mp e.symm)

theorem corr_cocycle (h : C1 K.Oc) (G : C0 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) :
    ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      corr h G T T'' (φ ≫ ψ) = ψ.φ (corr h G T T' φ) + corr h G T' T'' ψ := by
  intro T T' T'' φ ψ hφ hψ
  change (h T T'' (φ ≫ ψ) : T''.C) - (G T'' - ψ.φ (φ.φ (G T))) =
    ψ.φ ((h T T' φ : T'.C) - (G T' - φ.φ (G T))) + ((h T' T'' ψ : T''.C) - (G T'' - ψ.φ (G T')))
  rw [hc T T' T'' φ ψ hφ hψ, map_sub, map_sub]
  abel

theorem vanish (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ)
    (v1 : ∀ T : K.Obj, h _ _ (ptHom T (K.le_refl T.k)) = 0)
    (v2 : ∀ k k' (e : K.le 0 k' k), h _ _ (ptHom (K.triv k') e) = 0)
    (v3 : ∀ k, h _ _ (jet0 k) = h _ _ (jet1 k)) (T T' : K.Obj) (φ : T ⟶ T') (hφ : φ.deg = 0) :
    h T T' φ = 0 := by
  have hm := GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism K h 0 (fun k T χ hχ ↦ by
    rw [hc _ _ _ (jet0 k) χ rfl hχ, hc _ _ _ (jet1 k) χ rfl hχ, v3 k])
  have v5 : ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = 0 → h _ _ f = 0 := by
    intro k T f hd
    have e : K.le 0 T.k k := hd ▸ Charts.Hom.le f
    have hs : ∀ c : Hol (K.W k), sh (Charts.Hom.le f) c = sh (K.le_refl T.k) (sh e c) := fun c ↦ by
      rw [sh_refl]
      exact Hol.ext_fn fun p hp ↦ by rw [fn_sh (Charts.Hom.le f) c hp, fn_sh e c hp, hd]
    have hcomp : ptHom T (Charts.Hom.le f) = ptHom (K.triv T.k) e ≫ ptHom T (K.le_refl T.k) :=
      hom_ext (fun c ↦ congrArg T.ρ (hs c)) (hd.trans (add_zero (0 : Λ)).symm)
    rw [hm k T f hd, hcomp, hc _ _ _ _ _ rfl rfl, v2, v1, map_zero, add_zero]
  have e := hc _ _ _ (ptHom T (K.le_refl T.k)) φ rfl hφ
  rw [v5 _ _ _ ((zero_add φ.deg).trans hφ), v1, map_zero, zero_add] at e
  exact e.symm

def jetDiff (h : C1 K.Oc) (k : K.K) : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) :=
  h _ _ (jet0 k) - h _ _ (jet1 k)

def trans0 (h : C1 K.Oc) (k k' : K.K) (e : K.le 0 k' k) : Hol (K.W k') := h _ _ (ptHom (K.triv k') e)

theorem jetDiff_sh (h : C1 K.Oc)
    (hc : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 →
      h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) (k k' : K.K) (e : K.le 0 k' k) (i : Fin g) :
    (jetDiff h k').snd i - sh e ((jetDiff h k).snd i) = dw i (trans0 h k k' e) := by
  obtain ⟨χ, hχ, h0, h1, hx⟩ := GlobalTheory.T.exists_jet_morphism_extending_translation K e
  have c0 := hc _ _ _ (jet0 k) χ rfl hχ
  have c1 := hc _ _ _ (jet1 k) χ rfl hχ
  rw [h0] at c0
  rw [h1] at c1
  have key := sub_rel c0 (hc _ _ _ (ptHom (K.triv k') e) (jet0 k') rfl rfl) c1
    (hc _ _ _ (ptHom (K.triv k') e) (jet1 k') rfl rfl)
  have key' : χ.φ (jetDiff h k) = (jet0 k').φ (trans0 h k k' e) - (jet1 k').φ (trans0 h k k' e) + jetDiff h k' :=
    (map_sub χ.φ _ _).trans key
  have s := (hx (jetDiff h k)).2 i
  rw [key'] at s
  have s' : (0 : Hol (K.W k')) - (tszeSec (g := g) dw (trans0 h k k' e)).snd i + (jetDiff h k').snd i =
      sh e ((jetDiff h k).snd i) := s
  rw [snd_tszeSec] at s'
  rw [← s']
  abel

def gauge (h : C1 K.Oc) (G₀ : ∀ k, Hol (K.W k)) : C0 K.Oc :=
  fun T ↦ (T.ρ (G₀ T.k) + (h _ _ (ptHom T (K.le_refl T.k)) : T.C) : T.C)

theorem exists_gauge : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T) := by
  intro I _ g Λ _ F K hR hB h hc
  have hcl := fun k ↦ GlobalTheory.T.connectionForm_degZeroCocycle_closed K h hc k (jetDiff h k) rfl
  obtain ⟨G₀, hd, ha⟩ := GlobalTheory.T.exists_primitive_cech_poincare_rich_charts K hR hB (trans0 h) (fun k ↦ (jetDiff h k).snd)
    (fun k k' k'' e e' e'' ↦ by
      have c := hc _ _ _ (ptHom (K.triv k') e) (ptHom (K.triv k'') e') rfl rfl
      rw [ptHom_comp0 e e' e''] at c
      exact c)
    (fun k i j ↦ (hcl k).2 i j) (jetDiff_sh h hc)
  have gt : ∀ k, gauge h G₀ (K.triv k) = G₀ k := fun k ↦ by
    have z : h _ _ (ptHom (K.triv k) (K.le_refl k)) = 0 := by
      rw [ptHom_refl_triv]; exact zero_id h hc _
    exact (congrArg (fun x : Hol (K.W k) ↦ G₀ k + x) z).trans (add_zero _)
  refine ⟨gauge h G₀, fun T T' φ hφ ↦ sub_eq_zero.mp
    (vanish (corr h (gauge h G₀)) (corr_cocycle h _ hc) (fun T ↦ ?_) (fun k k' e ↦ ?_) (fun k ↦ ?_) T T' φ hφ)⟩
  · have z : (ptHom T (K.le_refl T.k)).φ (gauge h G₀ (K.triv T.k)) = T.ρ (G₀ T.k) := by
      rw [gt]; exact congrArg T.ρ (sh_refl (K.le_refl T.k) _)
    unfold corr
    rw [z]
    exact sub_eq_zero.mpr (add_sub_cancel_left (G := T.C) _ _).symm
  · unfold corr
    rw [gt, gt]
    exact sub_eq_zero.mpr (ha k k' e)
  · unfold corr
    rw [gt]
    refine sub_sub_eq_of_sub_eq_addCommGroup (d := TrivSqZeroExt.inr (jetDiff h k).snd) (eq_inr (jetDiff h k) (hcl k).1) ?_
    have z0 : (jet0 k).φ (G₀ k) = TrivSqZeroExt.inl (G₀ k) :=
      congrArg TrivSqZeroExt.inl (sh_refl (K.le_refl k) (G₀ k))
    rw [z0]
    exact (tszeSec_sub_inl dw (G₀ k)).trans (congrArg TrivSqZeroExt.inr (funext (hd k)))

end GlobalTheory.AnPer.Charts.DegZero
end
end

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T) := by
  atlas_forward_decl GlobalTheory.AnPer.Charts.DegZero.exists_gauge
end
