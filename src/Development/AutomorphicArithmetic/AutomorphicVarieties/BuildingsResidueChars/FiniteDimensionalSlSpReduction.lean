import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BlockEmbeddingCommInfEmbAndExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem vecMul_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [CommRing R] (g : GL (Fin a) R) (y : Fin n → R) :
    y ᵥ* (emb e g).val = y + ((fun i => y (e i)) ᵥ* g.val - fun i => y (e i)) ᵥ* (inc e R)ᵀ := by
  have h : y ᵥ* inc e R = fun i => y (e i) := by
    ext i
    simp [inc, vecMul, dotProduct]
  rw [coe_emb, vecMul_add, vecMul_one, ext0, ← vecMul_vecMul, ← vecMul_vecMul, h, vecMul_sub, vecMul_one]

private theorem norm_emb {a n : ℕ} (e : Fin a ↪ Fin n) {R : Type} [NormedField R] (g : GL (Fin a) R)
    (hg : ∀ y, Reduction.euclidNorm (y ᵥ* g.val) = Reduction.euclidNorm y) (y : Fin n → R) :
    Reduction.euclidNorm (y ᵥ* (emb e g).val) = Reduction.euclidNorm y := by
  have h := hg fun i => y (e i)
  unfold Reduction.euclidNorm at h ⊢
  rw [Real.sqrt_inj (by positivity) (by positivity)] at h
  congr 1
  rw [← Finset.sum_add_sum_compl (Finset.univ.map e), ← Finset.sum_add_sum_compl (Finset.univ.map e),
    Finset.sum_map, Finset.sum_map, ← h, vecMul_emb]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) (e j) = z j := fun z => by simp [inc, vecMul, dotProduct]
    rw [Pi.add_apply, this, Pi.sub_apply, add_sub_cancel]
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : ∀ k, j ≠ e k := fun k hk => by simp [hk] at hj
    have : ∀ z : Fin a → R, (z ᵥ* (inc e R)ᵀ) j = 0 := fun z => by simp [inc, vecMul, dotProduct, hj']
    rw [Pi.add_apply, this, add_zero]

private theorem emb_transfer {a n : ℕ} (e : Fin a ↪ Fin n) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (g : GL (Fin a) R) (g' : GL (Fin a) S) (h' : GL (Fin n) S) (hg : ∀ i j, g'.val i j = f (g.val i j))
    (hh : ∀ i j, h'.val i j = f ((emb e g).val i j)) : h' = emb e g' := by
  have h1 : g' = Matrix.GeneralLinearGroup.map f g := Units.ext (Matrix.ext hg)
  have h2 : h' = Matrix.GeneralLinearGroup.map f (emb e g) := Units.ext (Matrix.ext hh)
  rw [h1, h2, emb_map]

private theorem int_emb {a n : ℕ} (e : Fin a ↪ Fin n) {F : Type} [Field F] [ValuativeRel F] (g : GL (Fin a) F)
    (hg : g ∈ GLnLocal.integralGL F a) : emb e g ∈ GLnLocal.integralGL F n := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨emb e u, emb_transfer e (ValuativeRel.valuation F).integer.subtype u _ _ (fun _ _ => rfl) (fun _ _ => rfl)⟩

theorem UpperTheory.blockEmbedding_adelic_norm_compat :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n), ∀ k ∈ Reduction.maxCompact (K := K) (n := a), emb e k ∈ Reduction.maxCompact (K := K) (n := n) := by
  intro K _ _ a n e k hk
  rw [Reduction.mem_maxCompact] at hk ⊢
  refine ⟨fun w => ?_, fun v => ?_⟩
  · rw [emb_transfer e (Reduction.infEval w) k (Reduction.infAt w k) (Reduction.infAt w (emb e k))
      (fun i j => Reduction.infAt_apply w k i j) (fun i j => Reduction.infAt_apply w _ i j), Reduction.mem_archCompact]
    exact norm_emb e _ (Reduction.mem_archCompact.1 (hk.1 w))
  · rw [emb_transfer e (Reduction.finEval v) k (Reduction.finAt v k) (Reduction.finAt v (emb e k))
      (fun i j => Reduction.finAt_apply v k i j) (fun i j => Reduction.finAt_apply v _ i j)]
    exact int_emb e _ (hk.2 v)
end

section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aux {G H G' H' : Type} [Monoid G] [Monoid H] [Monoid G'] [Monoid H'] (E : G →* H) (i : G' → G) (i' : H' → H)
    (j : G' → H') (hj : ∀ k k', j (k * k') = j k * j k') (hi : ∀ k, E (i k) = i' (j k)) (V : Submodule ℂ (H' → ℂ))
    (hst : ∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) :
    (∀ f ∈ V.map (LinearMap.funLeft ℂ ℂ j), ∀ k', (fun k => f (k * k')) ∈ V.map (LinearMap.funLeft ℂ ℂ j)) ∧
    ∀ (f : G → ℂ) (ψ : H → ℂ) (g₀ : H), (∀ g, (fun k => ψ (g * i' k)) ∈ V) → (∀ m, f m = ψ (g₀ * E m)) →
      ∀ g, (fun k => f (g * i k)) ∈ V.map (LinearMap.funLeft ℂ ℂ j) := by
  constructor
  · rintro _ ⟨f, hf, rfl⟩ k'
    refine ⟨_, hst f hf (j k'), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply, hj]
  · intro f ψ g₀ hψ hf g
    refine ⟨_, hψ (g₀ * E g), funext fun k => ?_⟩
    simp only [LinearMap.funLeft_apply]
    rw [hf, map_mul, hi, mul_assoc]

private theorem aux2 (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (k : archCompact K a) :
    embArch e k.1 ∈ archCompact K n := by
  have h := UpperTheory.blockEmbedding_adelic_norm_compat K a n e _ (Subgroup.mem_comap.1 k.2)
  rw [(UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1] at h
  exact Subgroup.mem_comap.2 h

private theorem aux3 {G X : Type} (A : Submodule ℂ (G → ℂ)) (s : Set A) (p : X → G) (W : Submodule ℂ (X → ℂ))
    (h : ∀ f ∈ s, (fun k => f.1 (p k)) ∈ W) : ∀ f ∈ Submodule.span ℂ s, (fun k => f.1 (p k)) ∈ W := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    convert W.zero_mem using 1
    funext k
    simp
  | add x y _ _ hx hy =>
    convert W.add_mem hx hy using 1
    funext k
    simp
  | smul c x _ hx =>
    convert W.smul_mem c hx using 1
    funext k
    simp

theorem UpperTheory.finiteDimensional_slSp_reduction :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S : Submodule ℂ (archSmooth K n)), Types S → Types (slSp e Γ S) := by
  intro K _ _ a n e Γ S hS
  obtain ⟨V, hVf, hVst, hV⟩ := hS
  let j : archCompact K a → archCompact K n := fun k => ⟨embArch e k.1, aux2 K a n e k⟩
  have hj : ∀ k k', j (k * k') = j k * j k' := fun k k' => Subtype.ext (map_mul (embArch e) k.1 k'.1)
  have hi : ∀ k : archCompact K a, emb e (infEmb K a k.1) = infEmb K n (j k).1 :=
    fun k => (UpperTheory.blockEmbedding_comm_infEmb_and_exp K a n e).1 k.1
  have key := aux (G := AdelicGLn.AdelicGL K a) (H := AdelicGLn.AdelicGL K n) (emb e)
    (fun k : archCompact K a => infEmb K a k.1)
    (fun k : archCompact K n => infEmb K n k.1) j hj hi V hVst
  refine ⟨V.map (LinearMap.funLeft ℂ ℂ j), ?_, key.1, ?_⟩
  · exact Module.Finite.map V _
  · intro f hf g
    unfold slSp at hf
    refine aux3 (archSmooth K a) _ (fun k : archCompact K a => g * infEmb K a k.1)
      (V.map (LinearMap.funLeft ℂ ℂ j)) ?_ f hf
    rintro f' ⟨ψ, hψ, g₀, -, hf'⟩
    exact key.2 f'.1 ψ.1 g₀ (hV ψ hψ) hf' g
end
