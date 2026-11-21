import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TraceHermNondegenerate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.FormPartialDerivatives
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfEvalGridEqZeroOfTotalDegreeLe
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMinorProdEqSmulColActBasePoly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SumFinsuppAntidiagProdPowDivMultiFactorial
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.FormPerpVectorMemOfIntegral
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo

section
open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.TB (perpVec hMat)
open ReciprocityTheory.ChartRestriction.G.FD (cc)

namespace GlobalTheory.Harm

section Perp

variable {R S : Type} [CommRing R] [CommRing S] {p n : ℕ}

variable (R n) in

def dotPairing : (Fin n → R) →ₗ[R] ((Fin n → R) → R) where
  toFun x y := x ⬝ᵥ y
  map_add' x x' := funext fun y => add_dotProduct x x' y
  map_smul' r x := funext fun y => smul_dotProduct r x y

@[simp] theorem dotPairing_apply (x y : Fin n → R) : dotPairing R n x y = x ⬝ᵥ y := rfl

theorem map_perpVec_apply (f : R →+* S) (h : (Fin n → R) →ₗ[R] ((Fin n → R) → R))
    (h' : (Fin n → S) →ₗ[S] ((Fin n → S) → S)) (e e' : Fin p → Fin n → R) (g : Fin n → R)
    (ε ε' : Fin p → Fin n → S) (γ : Fin n → S) (he' : ∀ a k, f (e' a k) = ε' a k)
    (hg : ∀ k, f (g k) = γ k) (hM : ∀ a' a, f (h (e' a') (e a)) = h' (ε' a') (ε a))
    (hge : ∀ a, f (h g (e a)) = h' γ (ε a)) (k : Fin n) :
    f (perpVec h e e' g k) = perpVec h' ε ε' γ k := by
  have hm : f.mapMatrix (hMat h e e') = hMat h' ε ε' := by
    ext a' a; exact hM a' a
  have hadj (a a') : f ((hMat h e e').adjugate a a') = (hMat h' ε ε').adjugate a a' := by
    rw [← hm, ← RingHom.map_adjugate]; rfl
  simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_sub, map_mul,
    map_sum, RingHom.map_det, hm, hadj, hg, hge, he']

theorem map_perpVec_dotPairing (f : R →+* S) (ε ε' : Fin p → Fin n → R) (γ : Fin n → R) :
    f ∘ perpVec (dotPairing R n) ε ε' γ =
      perpVec (dotPairing S n) (fun a => f ∘ ε a) (fun a => f ∘ ε' a) (f ∘ γ) :=
  funext fun k => map_perpVec_apply f _ _ _ _ _ _ _ _ (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => by simp [dotProduct]) (fun _ => by simp [dotProduct]) k

theorem adjugate_isHomogeneous {σ : Type*} (M : Matrix (Fin p) (Fin p) (MvPolynomial σ R)) (d : ℕ)
    (hM : ∀ a b, (M a b).IsHomogeneous d) (a b : Fin p) :
    (M.adjugate a b).IsHomogeneous ((p - 1) * d) := by
  rw [adjugate_apply]
  have := det_isWeightedHomogeneous (1 : σ → ℕ) (M.updateRow b (Pi.single a 1))
    (fun i => if i = b then 0 else d) (fun i j => by
      by_cases hi : i = b
      · subst hi
        rw [updateRow_self, if_pos rfl, Pi.single_apply]
        split_ifs
        · exact isWeightedHomogeneous_one _ _
        · exact isWeightedHomogeneous_zero _ _ _
      · rw [updateRow_ne hi, if_neg hi]; exact hM i j)
  change IsWeightedHomogeneous 1 _ _
  convert this using 1
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem perpVec_dotPairing_isHomogeneous {σ : Type} (ε ε' : Fin p → Fin n → MvPolynomial σ R)
    (γ : Fin n → MvPolynomial σ R) (hε : ∀ a k, (ε a k).IsHomogeneous 1)
    (hε' : ∀ a k, (ε' a k).IsHomogeneous 1) (hγ : ∀ k, (γ k).IsHomogeneous 1) (k : Fin n) :
    (perpVec (dotPairing _ n) ε ε' γ k).IsHomogeneous (2 * p + 1) := by
  have hM (a' a) : (hMat (dotPairing _ n) ε ε' a' a).IsHomogeneous 2 :=
    show (∑ k, ε' a' k * ε a k).IsHomogeneous 2 from
      IsHomogeneous.sum _ _ _ fun k _ => (hε' a' k).mul (hε a k)
  have hge (a) : (dotPairing _ n γ (ε a)).IsHomogeneous 2 :=
    IsHomogeneous.sum _ _ _ fun k _ => (hγ k).mul (hε a k)
  have hdet : (hMat (dotPairing _ n) ε ε').det.IsHomogeneous (2 * p) := by
    have := det_isWeightedHomogeneous (1 : σ → ℕ) _ (fun _ => 2) hM
    simpa [mul_comm, IsHomogeneous] using this
  simp only [perpVec, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine (hdet.mul (hγ k)).sub (IsHomogeneous.sum _ _ _ fun a _ => IsHomogeneous.sum _ _ _
    fun a' _ => ?_)
  have := ((adjugate_isHomogeneous _ 2 hM a a').mul (hge a)).mul (hε' a' k)
  have hp := a.pos
  rwa [show (p - 1) * 2 + 2 + 1 = 2 * p + 1 by omega] at this

end Perp

section Param

variable {K : Type*} [CommRing K] {σ ω T κ : Type*} {p q : ℕ}

noncomputable def swapVars : MvPolynomial ω (MvPolynomial σ K) →+* MvPolynomial σ (MvPolynomial ω K) :=
  eval₂Hom (MvPolynomial.map C) fun v => C (X v)

theorem eval_swapVars (x : σ → K) (F : MvPolynomial ω (MvPolynomial σ K)) :
    eval (fun i => C (x i)) (swapVars F) = MvPolynomial.map (eval x) F := by
  have : (eval fun i => (C (x i) : MvPolynomial ω K)).comp swapVars = MvPolynomial.map (eval x) := by
    ext1
    · ext1
      · ext1 r; simp [swapVars]
      · simp [swapVars]
    · simp [swapVars]
  exact DFunLike.congr_fun this F

variable [Fintype κ]

theorem swapVars_rowForm_isHomogeneous (t : T) (r : Fin p ⊕ Fin q) (u : κ → MvPolynomial σ K)
    {d : ℕ} (hu : ∀ k, (u k).IsHomogeneous d) : (swapVars (rowForm t r u)).IsHomogeneous d := by
  rw [rowForm_apply, map_sum]
  refine IsHomogeneous.sum _ _ _ fun k _ => ?_
  simp only [swapVars, map_mul, eval₂Hom_C, eval₂Hom_X']
  simpa using ((hu k).map C).mul (isHomogeneous_C σ (X (t, r, k) : Poly K T p q κ))

theorem swapVars_minorProd_isHomogeneous [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → κ → MvPolynomial σ K) (φ : T → Fin q → κ → MvPolynomial σ K) {d d' : ℕ}
    (hε : ∀ t a k, (ε t a k).IsHomogeneous d) (hφ : ∀ t b k, (φ t b k).IsHomogeneous d') :
    (swapVars (minorProd c c' ε φ)).IsHomogeneous
      (∑ t, (d * partSize (c t) + d' * partSize (c' t))) := by
  simp only [minorProd, map_prod, map_mul, map_pow]
  refine IsHomogeneous.prod _ _ _ fun t _ => IsHomogeneous.mul ?_ ?_
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [xMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (xForm t (lead i a) (ε t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d) fun a b => swapVars_rowForm_isHomogeneous t _ _ (hε t _)
    simpa [mul_comm, IsHomogeneous] using this
  · rw [partSize, Finset.mul_sum]
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    rw [← mul_assoc]
    refine IsHomogeneous.pow ?_ _
    rw [yMinor, RingHom.map_det]
    have := det_isWeightedHomogeneous (1 : σ → ℕ) (swapVars.mapMatrix (Matrix.of
      fun a b : Fin (i.val + 1) => (yForm t (lead i a) (φ t (lead i b)) : Poly _ T p q κ)))
      (fun _ => d') fun a b => swapVars_rowForm_isHomogeneous t _ _ (hφ t _)
    simpa [mul_comm, IsHomogeneous] using this

end Param

section Field

variable {R S : Type} [CommRing R] [CommRing S] {T : Type*} [Fintype T] {ι : Type} [Fintype ι]
  {p q n : ℕ}

noncomputable def coordProd (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) (w w' : T → ι → Fin n → R)
    (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) : Poly R T p q (Fin n) :=
  minorProd c c' (fun t a k => ∑ i, x (Sum.inl a, i) * w' t i k)
    fun t b => perpVec (dotPairing R n) (fun a k => ∑ i, x (Sum.inl a, i) * w' t i k)
      (fun a k => ∑ i, x (Sum.inr (Sum.inl a), i) * w t i k)
      fun k => ∑ i, x (Sum.inr (Sum.inr b), i) * w t i k

theorem map_coordProd (f : R →+* S) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → R) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → R) :
    MvPolynomial.map f (coordProd c c' w w' x) =
      coordProd c c' (fun t i k => f (w t i k)) (fun t i k => f (w' t i k)) fun j => f (x j) := by
  simp only [coordProd, map_minorProd, map_perpVec_dotPairing]
  simp only [Function.comp_def, map_sum, map_mul]

variable {K : Type} [Field K]

theorem coordProd_mem_orbitSpan (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
    coordProd c c' w w' x ∈ orbitSpan K hpq c c' :=
  minorProd_mem_orbitSpan hpq c c' fun _ a _ => by
    rw [dotProduct_comm]; exact perpendicular_vector_exists K _ p (dotPairing K n) _ _ _ a

theorem span_range_coordProd (hpq : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K)
    (hw : ∀ y y' : T → Fin n → K, ∃ x : ι → K,
      (∀ t k, ∑ i, x i * w t i k = y t k) ∧ ∀ t k, ∑ i, x i * w' t i k = y' t k) :
    Submodule.span K (Set.range (coordProd c c' w w')) = orbitSpan K hpq c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact coordProd_mem_orbitSpan hpq c c' w w' x
  rw [orbitSpan_eq_span_linearIndependent]
  refine Submodule.span_mono ?_
  rintro _ ⟨ε, φ, hε, -, hperp, rfl⟩
  choose ε' hε' using fun t a => surjective_mulVecLin_of (hε t) (Pi.single a 1)
  choose x₁ _ hx₁ using fun a => hw 0 fun t => ε t a
  choose x₂ hx₂ _ using fun a => hw (fun t => ε' t a) 0
  choose x₃ hx₃ _ using fun b => hw (fun t => φ t b) 0
  refine ⟨fun j => Sum.elim x₁ (Sum.elim x₂ x₃) j.1 j.2, ?_⟩
  simp only [coordProd, Sum.elim_inl, Sum.elim_inr, hx₁, hx₂, hx₃]
  congr 1
  funext t b
  have hM : hMat (dotPairing K n) (ε t) (ε' t) = 1 := by
    ext a' a
    have := congrFun (hε' t a') a
    rw [one_eq_pi_single, ← this]
    exact dotProduct_comm (ε' t a') (ε t a)
  have := perpendicular_vector_perp K _ p (dotPairing K n) (ε t) (ε' t) (φ t b) fun a => by
    rw [dotPairing_apply, dotProduct_comm]; exact hperp t a b
  rw [hM, det_one, one_smul] at this
  exact this

theorem span_grid_coordProd [CharZero K] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (w w' : T → ι → Fin n → K) {dg : ℕ} (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K ((fun x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → ℕ =>
      coordProd c c' w w' fun j => (x j : K)) '' {x | ∀ j, x j ≤ dg}) =
      Submodule.span K (Set.range (coordProd c c' w w')) := by
  let F : MvPolynomial ((Fin p ⊕ Fin p ⊕ Fin q) × ι) (Poly K T p q (Fin n)) :=
    swapVars (coordProd c c' (fun t i k => C (w t i k)) (fun t i k => C (w' t i k)) X)
  have hlin (r : Fin p ⊕ Fin p ⊕ Fin q) (u : ι → K) :
      (∑ i, X (r, i) * C (u i) : MvPolynomial _ K).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X K (r, i)).mul (isHomogeneous_C _ (u i))
  have hF : F.IsHomogeneous _ := swapVars_minorProd_isHomogeneous c c' _ _ (d := 1)
    (d' := 2 * p + 1) (fun t a k => hlin _ _) fun t b k =>
      perpVec_dotPairing_isHomogeneous _ _ _ (fun a k => hlin _ _) (fun a k => hlin _ _)
        (fun k => hlin _ _) k
  have hdeg : F.totalDegree ≤ dg := by
    refine hF.totalDegree_le.trans (le_trans ?_ hdg)
    rw [typeDegree, Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [mul_add]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) _
  have hev (x : (Fin p ⊕ Fin p ⊕ Fin q) × ι → K) :
      eval (fun j => C (x j)) F = coordProd c c' w w' x := by
    rw [eval_swapVars, map_coordProd]; simp only [eval_C, eval_X]
  have := span_grid_eval_eq_span_range (A := K) (K := K) dg F
    fun j => (degreeOf_le_totalDegree F j).trans hdeg
  simp only [Algebra.algebraMap_self, RingHom.id_apply, algebraMap_eq, hev] at this
  rw [← this]
  congr 2
  funext x
  rw [← hev]; simp only [map_natCast]

end Field

section Embeddings

theorem exists_sum_mul_embedding_eq {E K J κ ι : Type*} [Field E] [CharZero E] [Field K]
    [Finite J] [Finite κ] [Fintype ι] (σ : J → E →+* K) (hσ : Function.Injective σ)
    (v : ι → κ → E) (hv : Submodule.span ℚ (Set.range v) = ⊤) (y : J → κ → K) :
    ∃ x : ι → K, ∀ j k, ∑ i, x i * σ j (v i k) = y j k := by
  classical
  have := Fintype.ofFinite J
  have := Fintype.ofFinite κ
  let u : (κ → E) → J × κ → K := fun z s => σ s.1 (z s.2)
  let U : Submodule K (J × κ → K) := Submodule.span K (Set.range fun i => u (v i))
  have hU (z : κ → E) : u z ∈ U := by
    have hz : z ∈ Submodule.span ℚ (Set.range v) := hv ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => convert U.zero_mem; ext s; simp [u]
    | add z z' _ _ h h' => convert U.add_mem h h'; ext s; simp [u]
    | smul r z _ h => convert U.smul_mem (r : K) h; ext s; simp [u, Rat.smul_def]
  have hind : LinearIndependent K fun j => (σ j : E → K) :=
    (linearIndependent_monoidHom E K).comp (fun j => (σ j : E →* K)) fun j j' e =>
      hσ (RingHom.ext fun a => DFunLike.congr_fun e a)
  have hy : (fun s : J × κ => y s.1 s.2) ∈ U := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
    intro l hl
    have h0 (j k) : l (Pi.single (j, k) 1) = 0 := by
      refine Fintype.linearIndependent_iff.1 hind (fun j => l (Pi.single (j, k) 1)) ?_ j
      funext a
      have h1 := (Submodule.mem_dualAnnihilator l).1 hl _ (hU (Pi.single k a))
      have h2 : u (Pi.single k a) = ∑ j, σ j a • Pi.single (j, k) 1 := by
        ext ⟨j', k'⟩
        by_cases hk : k' = k <;> simp [u, Finset.sum_apply, Pi.single_apply, hk]
      rw [h2, map_sum] at h1
      simpa [mul_comm] using h1
    rw [← Finset.univ_sum_single (fun s : J × κ => y s.1 s.2), map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_one (y s.1 s.2), ← smul_eq_mul, Pi.single_smul', map_smul, h0, smul_zero]
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
  exact ⟨x, fun j k => by simpa [u] using congrFun hx (j, k)⟩

end Embeddings

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type} [Field K] [CharZero K]
  {T : Type*} [Fintype T] {ι : Type} [Fintype ι] {p q n : ℕ}

theorem span_grid_perpVec_eq_orbitSpan_of_le (τ : T → E →+* K)
    (hτ : Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x))
    (hpq : p + q ≤ n) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (v : ι → Fin n → E)
    (hv : Submodule.span ℚ (Set.range v) = ⊤) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {dg : ℕ}
    (hdg : (2 * p + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K {P | ∃ (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ),
      (∀ a i, A a i ≤ dg) ∧ (∀ a i, A' a i ≤ dg) ∧ (∀ b i, B b i ≤ dg) ∧
      P = minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)} =
      orbitSpan K hpq c c' := by
  let γ : E →+* E := (IsCMField.complexConj E : E ≃ₐ[_] E)
  have hγ (x) : cc x = γ x := rfl
  let σ : T × Bool → E →+* K := fun s => if s.2 then (τ s.1).comp γ else τ s.1
  have hσ : Function.Injective σ := fun s s' e => hτ (funext fun x => by
    have := DFunLike.congr_fun e x
    obtain ⟨t, _ | _⟩ := s <;> obtain ⟨t', _ | _⟩ := s' <;> exact this)
  rw [← span_range_coordProd hpq c c' (fun t i k => τ t (v i k)) (fun t i k => τ t (γ (v i k)))
    fun y y' => by
      obtain ⟨x, hx⟩ := exists_sum_mul_embedding_eq σ hσ v hv fun s => if s.2 then y' s.1 else y s.1
      exact ⟨x, fun t => hx (t, false), fun t => hx (t, true)⟩,
    ← span_grid_coordProd c c' _ _ hdg]
  have key (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ) :
      minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        (fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)) =
      coordProd c c' (fun t i k => τ t (v i k)) (fun t i k => τ t (γ (v i k)))
        fun j => ((Sum.elim A (Sum.elim A' B) j.1 j.2 : ℕ) : K) := by
    rw [coordProd]
    congr 1
    · funext t a k
      simp [hγ]
    · funext t b k
      refine map_perpVec_apply _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ k
      all_goals intros; simp [hγ, hh, dotProduct]
  congr 1
  ext P
  constructor
  · rintro ⟨A, A', B, hA, hA', hB, rfl⟩
    refine ⟨fun j => Sum.elim A (Sum.elim A' B) j.1 j.2, ?_, (key A A' B).symm⟩
    rintro ⟨a | a | b, i⟩
    exacts [hA a i, hA' a i, hB b i]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun a i => x (Sum.inl a, i), fun a i => x (Sum.inr (Sum.inl a), i),
      fun b i => x (Sum.inr (Sum.inr b), i), fun _ _ => hx _, fun _ _ => hx _, fun _ _ => hx _, ?_⟩
    rw [key]
    congr 1
    funext j
    obtain ⟨a | a | b, i⟩ := j <;> rfl

theorem span_grid_perpVec_eq_orbitSpan (τ : T → E →+* K)
    (hτ : Function.Injective fun s : T × Bool => fun x : E => τ s.1 (if s.2 then cc x else x))
    (hpq : p + q ≤ n) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (v : ι → Fin n → E)
    (hv : Submodule.span ℚ (Set.range v) = ⊤) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {dg : ℕ}
    (hdg : (2 * (p + q) + 1) * typeDegree c c' ≤ dg) :
    Submodule.span K {P | ∃ (A A' : Fin p → ι → ℕ) (B : Fin q → ι → ℕ),
      (∀ a i, A a i ≤ dg) ∧ (∀ a i, A' a i ≤ dg) ∧ (∀ b i, B b i ≤ dg) ∧
      P = minorProd c c' (fun t a k => τ t (cc ((∑ i, (A a i : E) • v i) k)))
        fun t b k => τ t (perpVec h (fun a => ∑ i, (A a i : E) • v i)
          (fun a => ∑ i, (A' a i : E) • v i) (∑ i, (B b i : E) • v i) k)} =
      orbitSpan K hpq c c' :=
  span_grid_perpVec_eq_orbitSpan_of_le τ hτ hpq h hh v hv c c'
    ((Nat.mul_le_mul_right _ (by omega)).trans hdg)

end CM

end GlobalTheory.Harm
end

section
open scoped BigOperators
open NumberField

namespace GlobalTheory.GridSize

open GlobalTheory.Harm GlobalTheory.MvPoly

section Minor

variable {T : Type*} {p q n : ℕ}

theorem l1Norm_rowBlockLinearForm_le (t : T) (r : Fin p ⊕ Fin q) (v : Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hv : ∑ k, ‖v k‖ ^ 2 ≤ R ^ 2) : l1Norm (rowForm t r v) ≤ √(n : ℝ) * R := by
  rw [rowForm_apply]
  refine (l1Norm_linearForm_le (fun k => (t, r, k)) v).trans ?_
  rw [Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.mpr ⟨hR, hv⟩) (Real.sqrt_nonneg _)

theorem l1Norm_det_le_of_entry_bound {σ : Type*} {i N : ℕ} (hi : i ≤ N)
    (M : Matrix (Fin i) (Fin i) (MvPolynomial σ ℂ)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ a b, l1Norm (M a b) ≤ B) : l1Norm M.det ≤ (N * B) ^ i := by
  refine (l1Norm_det_le_pow M h).trans ?_
  rw [Fintype.card_fin]
  have : (i : ℝ) ≤ N := by exact_mod_cast hi
  gcongr

theorem l1Norm_rowBlockLeadingMinorProduct_le [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (ε : T → Fin p → Fin n → ℂ) (φ : T → Fin q → Fin n → ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hε : ∀ t a, ∑ k, ‖ε t a k‖ ^ 2 ≤ R ^ 2) (hφ : ∀ t b, ∑ k, ‖φ t b k‖ ^ 2 ≤ R ^ 2)
    {N : ℕ} (hp : p ≤ N) (hq : q ≤ N) :
    l1Norm (minorProd c c' ε φ) ≤ (N * √(n : ℝ) * R) ^ typeDegree c c' := by
  have hB : 0 ≤ √(n : ℝ) * R := by positivity
  rw [minorProd, typeDegree, ← Finset.prod_pow_eq_pow_sum, mul_assoc]
  refine (l1Norm_prod_le _ _).trans (Finset.prod_le_prod (fun _ _ => l1Norm_nonneg _) fun t _ => ?_)
  rw [pow_add]
  refine (l1Norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (l1Norm_nonneg _) (by positivity))
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hε _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]
  · refine (l1Norm_prod_pow_le _ _ _ (fun i => (N * (√(n : ℝ) * R)) ^ (i.val + 1))
      fun i _ => ?_).trans_eq ?_
    · exact l1Norm_det_le_of_entry_bound (by have := i.isLt; omega) _ hB
        fun a b => l1Norm_rowBlockLinearForm_le _ _ _ hR (hφ _ _)
    · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, partSize]

end Minor

section Length

variable {E : Type*} [CommRing E] {κ : Type*} [Fintype κ]

noncomputable def embSeminorm (τ : E →+* ℂ) : RingSeminorm E where
  toFun x := ‖τ x‖
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by simp
  mul_le' x y := by simp

@[simp] theorem embSeminorm_apply (τ : E →+* ℂ) (x : E) : embSeminorm τ x = ‖τ x‖ := rfl

noncomputable def embVec (τ : E →+* ℂ) : (κ → E) →+ EuclideanSpace ℂ κ where
  toFun v := WithLp.toLp 2 fun k => τ (v k)
  map_zero' := by ext k; simp
  map_add' v w := by ext k; simp

omit [Fintype κ] in

@[simp] theorem embVec_apply (τ : E →+* ℂ) (v : κ → E) (k : κ) : embVec τ v k = τ (v k) := rfl

omit [Fintype κ] in

theorem embVec_smul (τ : E →+* ℂ) (x : E) (v : κ → E) : embVec τ (x • v) = τ x • embVec τ v := by
  ext k; simp

noncomputable def embLength (τ : E →+* ℂ) : AddGroupSeminorm (κ → E) where
  toFun v := ‖embVec τ v‖
  map_zero' := by simp
  add_le' x y := by rw [map_add]; exact norm_add_le _ _
  neg' x := by simp

theorem embLength_apply (τ : E →+* ℂ) (v : κ → E) : embLength τ v = ‖embVec τ v‖ := rfl

theorem embLength_sq (τ : E →+* ℂ) (v : κ → E) : embLength τ v ^ 2 = ∑ k, ‖τ (v k)‖ ^ 2 := by
  rw [embLength_apply, EuclideanSpace.norm_sq_eq]; rfl

theorem embLength_smul (τ : E →+* ℂ) (x : E) (v : κ → E) :
    embLength τ (x • v) = ‖τ x‖ * embLength τ v := by
  rw [embLength_apply, embVec_smul, norm_smul, embLength_apply]

theorem embLength_le_abs (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2) :
    embLength τ v ≤ |R| :=
  (le_abs_self _).trans (sq_le_sq.mp (by rwa [embLength_sq]))

theorem sum_sq_le_of_embLength_le (τ : E →+* ℂ) {v : κ → E} {R : ℝ} (h : embLength τ v ≤ |R|) :
    ∑ k, ‖τ (v k)‖ ^ 2 ≤ R ^ 2 := by
  rw [← embLength_sq, ← sq_abs R]
  exact pow_le_pow_left₀ (apply_nonneg _ _) h 2

theorem norm_emb_sum_mul_le (τ : E →+* ℂ) (s : E → E) (hs : ∀ x, ‖τ (s x)‖ = ‖τ x‖)
    (x y : κ → E) : ‖τ (∑ k, x k * s (y k))‖ ≤ embLength τ x * embLength τ y := by
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  simp only [map_mul, norm_mul, hs]
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_
    (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _)))
  rw [mul_pow, embLength_sq, embLength_sq]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

theorem sum_sq_combination_le (τ : E →+* ℂ) {ι : Type*} [Fintype ι] (v : ι → κ → E) {ρ : ℝ}
    (hv : ∀ i, ∑ k, ‖τ (v i k)‖ ^ 2 ≤ ρ ^ 2) (A : ι → ℕ) {d : ℕ} (hA : ∀ i, A i ≤ d) :
    ∑ k, ‖τ ((∑ i, (A i : E) • v i) k)‖ ^ 2 ≤ ((Fintype.card ι : ℝ) * d * ρ) ^ 2 := by
  apply sum_sq_le_of_embLength_le
  rw [embLength_apply, map_sum, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast, mul_assoc,
    ← nsmul_eq_mul, ← Finset.card_univ]
  refine (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ fun i _ => ?_)
  rw [← embLength_apply, embLength_smul, map_natCast, Complex.norm_natCast]
  exact mul_le_mul (by exact_mod_cast hA i) (embLength_le_abs τ (hv i)) (apply_nonneg _ _)
    (Nat.cast_nonneg _)

end Length

section Perp

open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.FD

theorem perpVec_eq_perpVector {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {p : ℕ}
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) :
    perpVec h e e' g = perpVector (fun a => (LinearMap.proj (e a)).comp h) e' g := rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {p n : ℕ}

theorem sum_sq_perpVec_le (τ : E →+* ℂ) (h : (Fin n → E) →ₗ[E] ((Fin n → E) → E))
    (hh : ∀ x y, h x y = ∑ k, x k * cc (y k)) (e e' : Fin p → Fin n → E) (g : Fin n → E) {R : ℝ}
    (he : ∀ a, ∑ k, ‖τ (e a k)‖ ^ 2 ≤ R ^ 2) (he' : ∀ a, ∑ k, ‖τ (e' a k)‖ ^ 2 ≤ R ^ 2)
    (hg : ∑ k, ‖τ (g k)‖ ^ 2 ≤ R ^ 2) :
    ∑ k, ‖τ (perpVec h e e' g k)‖ ^ 2 ≤ (((p + 1).factorial : ℝ) * R ^ (2 * p + 1)) ^ 2 := by
  have hs : ∀ x, ‖τ (cc x)‖ = ‖τ x‖ := fun x => by
    rw [cc, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have key : ∀ u v, embLength τ u ≤ |R| → embLength τ v ≤ |R| → ‖τ (h u v)‖ ≤ |R| ^ 2 :=
    fun u v hu hv => by
      rw [hh, sq]
      exact (norm_emb_sum_mul_le τ cc hs u v).trans
        (mul_le_mul hu hv (apply_nonneg _ _) (abs_nonneg _))
  apply sum_sq_le_of_embLength_le
  rw [perpVec_eq_perpVector, abs_mul, Nat.abs_cast, abs_pow, pow_succ, pow_mul, ← mul_assoc]
  exact seminorm_perpVector_le (embSeminorm τ) (by simp) (embLength τ)
    (fun x v => (embLength_smul τ x v).le) _ e' g
    (fun a a' => key _ _ (embLength_le_abs τ (he' a')) (embLength_le_abs τ (he a)))
    (fun a => key _ _ (embLength_le_abs τ hg) (embLength_le_abs τ (he a)))
    (fun a => embLength_le_abs τ (he' a)) (embLength_le_abs τ hg)

end Perp

end GlobalTheory.GridSize
end

section
open MvPolynomial Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)

namespace GlobalTheory.Harm

section Free

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ ι : Type*}

noncomputable def basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (b.repr (coeff m P) i)

theorem coeff_basisComponent (b : Module.Basis ι R S) (i : ι) (P : MvPolynomial σ S)
    (m : σ →₀ ℕ) : coeff m (basisComponent b i P) = b.repr (coeff m P) i := by
  classical
  rw [basisComponent, coeff_sum, Finset.sum_eq_single m]
  · simp
  · intro m' _ h; simp [coeff_monomial, h]
  · intro h; simp [notMem_support_iff.1 h]

theorem exists_eq_sum_basisComponent (b : Module.Basis ι R S) (P : MvPolynomial σ S) :
    ∃ J : Finset ι, P = ∑ i ∈ J, b i • MvPolynomial.map (algebraMap R S) (basisComponent b i P) := by
  classical
  refine ⟨P.support.biUnion fun m => (b.repr (coeff m P)).support, ?_⟩
  ext m
  simp only [coeff_sum, coeff_smul, coeff_map, coeff_basisComponent, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (coeff m P), Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset (s := P.support.biUnion fun m => (b.repr (coeff m P)).support)]
  · exact Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
  · by_cases hm : m ∈ P.support
    · exact Finset.subset_biUnion_of_mem (fun m => (b.repr (coeff m P)).support) hm
    · simp [notMem_support_iff.1 hm]
  · simp

theorem basisComponent_sum (b : Module.Basis ι R S) (J : Finset ι) (Q : ι → MvPolynomial σ R)
    {i : ι} (hi : i ∈ J) :
    basisComponent b i (∑ j ∈ J, b j • MvPolynomial.map (algebraMap R S) (Q j)) = Q i := by
  classical
  ext m
  simp only [coeff_basisComponent, coeff_sum, coeff_smul, coeff_map, smul_eq_mul, mul_comm (b _),
    ← Algebra.smul_def, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single i] <;> simp +contextual [hi]

variable {T : Type*} {p q : ℕ} {κ : Type*} [Fintype κ] {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}

theorem basisComponent_mem_rowHighest (b : Module.Basis ι R S) (i : ι) {P : Poly S T p q κ}
    (hP : P ∈ rowHighest S c c') : basisComponent b i P ∈ rowHighest R c c' := by
  classical
  obtain ⟨h₁, h₂, h₃⟩ := mem_rowHighest_iff_rowAdd.1 hP
  obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
  by_cases hi : i ∈ J
  swap
  · have : basisComponent b i P = 0 := by
      rw [← basisComponent_sum b (insert i J)
        (fun j => if j = i then 0 else basisComponent b j P) (Finset.mem_insert_self i J)
        |>.trans (if_pos rfl)]
      congr 1
      rw [Finset.sum_insert hi, if_pos rfl, map_zero, smul_zero, zero_add]
      refine hJ.trans (Finset.sum_congr rfl fun j hj => ?_)
      rw [if_neg (by rintro rfl; exact hi hj)]
    rw [this]; exact zero_mem _
  refine mem_rowHighest_iff_rowAdd.2 ⟨fun t a b' => ?_, fun t r m hm => h₂ t r fun e => hm ?_,
    fun t r r' hr s => ?_⟩
  · have := h₁ t a b'
    rw [hJ, map_sum] at this
    simp only [map_smul, ← map_laplacian] at this
    rw [← basisComponent_sum b J (fun j => laplacian t a b' (basisComponent b j P)) hi, this]
    simp [basisComponent]
  · rw [coeff_basisComponent, e]; simp
  · have := h₃ t r r' hr s
    conv_lhs at this => rw [hJ, map_sum]
    simp only [map_smul, ← map_intCast (algebraMap R S), ← map_rowAdd] at this
    rw [← basisComponent_sum b J (fun j => rowAdd t r r' (s : R) (basisComponent b j P)) hi, this]

variable (R S c c') in

theorem span_map_rowHighest [Module.Free R S] :
    Submodule.span S (MvPolynomial.map (algebraMap R S) ''
      (rowHighest R (κ := κ) c c' : Set (Poly R T p q κ))) = rowHighest S c c' := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨P, hP, rfl⟩
    exact map_mem_rowHighest _ hP
  · intro P hP
    let b := Module.Free.chooseBasis R S
    obtain ⟨J, hJ⟩ := exists_eq_sum_basisComponent b P
    rw [hJ]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, basisComponent_mem_rowHighest b i hP, rfl⟩)

end Free

section Scale

variable {R : Type*} [CommRing R] {T : Type*} {p q : ℕ} {κ : Type*}

theorem aeval_C_mul_X_of_isHomogeneous {σ : Type*} (r : R) {P : MvPolynomial σ R} {d : ℕ}
    (hP : P.IsHomogeneous d) : aeval (fun v => (C r * X v : MvPolynomial σ R)) P = r ^ d • P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ v ∈ m.support, m v = d := by
    rw [← hP (mem_support_iff.1 hm), Finsupp.weight_apply]; simp [Finsupp.sum]
  rw [aeval_monomial, monomial_eq, smul_eq_C_mul, ← hd]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_pow,
    algebraMap_eq]
  ring

end Scale

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {K : Type*} [Field K]
  {T : Type*} {p q n : ℕ}

noncomputable abbrev ccHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E ≃ₐ[_] E)

theorem ccHom_apply (x : E) : ccHom E x = cc x := rfl

theorem herm_one_eq_sum (x y : Fin n → E) : herm 1 x y = ∑ k, x k * cc (y k) := by
  simp [herm, Matrix.one_apply]

variable (p q) in

noncomputable def symO (τ : T → E →+* K) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Subalgebra (𝓞 K) (Poly K T p q (Fin n)) :=
  Algebra.adjoin (𝓞 K)
    ({P | ∃ t a, ∃ v ∈ Λ, P = xForm t a fun k => τ t (v k)} ∪
      {P | ∃ t b, ∃ v ∈ Λ, P = yForm t b fun k => τ t (cc (v k))})

noncomputable def Ha (τ : T → E →+* K) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 K) (Poly K T p q (Fin n)) :=
  (rowHighest K c c').restrictScalars (𝓞 K) ⊓ Subalgebra.toSubmodule (symO p q τ Λ)

variable (τ : T → E →+* K) {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ}
  {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} {P : Poly K T p q (Fin n)}

theorem mem_Ha : P ∈ Ha τ c c' Λ ↔ P ∈ rowHighest K c c' ∧ P ∈ symO p q τ Λ := Iff.rfl

theorem xForm_mem_symO (t : T) (a : Fin p) {v : Fin n → E} (hv : v ∈ Λ) :
    (xForm t a fun k => τ t (v k)) ∈ symO p q τ Λ :=
  Algebra.subset_adjoin (Or.inl ⟨t, a, v, hv, rfl⟩)

theorem yForm_mem_symO (t : T) (b : Fin q) {v : Fin n → E} (hv : v ∈ Λ) :
    (yForm t b fun k => τ t (cc (v k))) ∈ symO p q τ Λ :=
  Algebra.subset_adjoin (Or.inr ⟨t, b, v, hv, rfl⟩)

theorem symO_le_iff {A : Subalgebra (𝓞 K) (Poly K T p q (Fin n))} :
    symO p q τ Λ ≤ A ↔ (∀ t a, ∀ v ∈ Λ, (xForm t a fun k => τ t (v k)) ∈ A) ∧
      ∀ t b, ∀ v ∈ Λ, (yForm t b fun k => τ t (cc (v k))) ∈ A := by
  rw [symO, Algebra.adjoin_le_iff, Set.union_subset_iff]
  refine and_congr ⟨fun h t a v hv => h ⟨t, a, v, hv, rfl⟩, ?_⟩
    ⟨fun h t a v hv => h ⟨t, a, v, hv, rfl⟩, ?_⟩
  all_goals rintro h _ ⟨t, a, v, hv, rfl⟩; exact h t a v hv

theorem symO_mono (h : Λ ≤ Λ') : symO p q τ Λ ≤ symO p q τ Λ' :=
  (symO_le_iff τ).2 ⟨fun t a _ hv => xForm_mem_symO τ t a (h hv),
    fun t b _ hv => yForm_mem_symO τ t b (h hv)⟩


theorem det_mem_subalgebra {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    [DecidableEq ι] (B : Subalgebra R A) {M : Matrix ι ι A} (h : ∀ i j, M i j ∈ B) : M.det ∈ B := by
  rw [det_apply']
  exact B.sum_mem fun s _ => B.mul_mem (intCast_mem B _) (B.prod_mem fun i _ => h _ _)

variable (c c') in

theorem minorProd_mem_symO [Fintype T] {e : T → Fin p → Fin n → E} {f : T → Fin q → Fin n → E}
    (he : ∀ t a, e t a ∈ Λ) (hf : ∀ t b, f t b ∈ Λ) :
    minorProd c c' (fun t a k => τ t (e t a k)) (fun t b k => τ t (cc (f t b k))) ∈
      symO p q τ Λ :=
  Subalgebra.prod_mem _ fun t _ => Subalgebra.mul_mem _
    (Subalgebra.prod_mem _ fun _ _ => Subalgebra.pow_mem _
      (det_mem_subalgebra _ fun _ _ => xForm_mem_symO τ t _ (he t _)) _)
    (Subalgebra.prod_mem _ fun _ _ => Subalgebra.pow_mem _
      (det_mem_subalgebra _ fun _ _ => yForm_mem_symO τ t _ (hf t _)) _)

variable (c c') in

theorem minorProd_mem_Ha [Fintype T] {e : T → Fin p → Fin n → E} {f : T → Fin q → Fin n → E}
    (he : ∀ t a, e t a ∈ Λ) (hf : ∀ t b, f t b ∈ Λ) (h : ∀ t a b, herm 1 (e t a) (f t b) = 0) :
    minorProd c c' (fun t a k => τ t (e t a k)) (fun t b k => τ t (cc (f t b k))) ∈ Ha τ c c' Λ :=
  ⟨minorProd_mem_rowHighest c c' fun t a b => by
    have := congrArg (τ t) (h t a b)
    rw [herm_one_eq_sum] at this
    simpa [dotProduct] using this, minorProd_mem_symO τ c c' he hf⟩

variable (c c') in

theorem minorProd_conj_mem_Ha [Fintype T] (hΛ : ∀ v ∈ Λ, (fun k => cc (v k)) ∈ Λ')
    {e : T → Fin p → Fin n → E} {f : T → Fin q → Fin n → E}
    (he : ∀ t a, e t a ∈ Λ) (hf : ∀ t b, f t b ∈ Λ) (h : ∀ t a b, herm 1 (f t b) (e t a) = 0) :
    minorProd c c' (fun t a k => τ t (cc (e t a k))) (fun t b k => τ t (f t b k)) ∈
      Ha τ c c' Λ' := by
  have hcc (x : E) : cc (cc x) = x := IsCMField.complexConj_apply_apply E x
  have := minorProd_mem_Ha τ c c' (e := fun t a k => cc (e t a k)) (f := fun t b k => cc (f t b k))
    (fun t a => hΛ _ (he t a)) (fun t b => hΛ _ (hf t b)) fun t a b => by
      rw [← h t a b, herm_one_eq_sum, herm_one_eq_sum]
      simp only [hcc, mul_comm]
  simpa only [hcc] using this

variable (p q) in

noncomputable def pushLetters (A : Matrix (Fin n) (Fin n) E) :
    Poly K T p q (Fin n) →ₐ[K] Poly K T p q (Fin n) :=
  colSubst (fun t => (A.map (τ t))ᵀ) fun t => A.map ((τ t).comp (ccHom E))

theorem pushLetters_xForm (A : Matrix (Fin n) (Fin n) E) (t : T) (a : Fin p) (v : Fin n → E) :
    pushLetters p q τ A (xForm t a fun k => τ t (v k)) = xForm t a fun k => τ t ((A *ᵥ v) k) := by
  rw [pushLetters, colSubst_xForm, vecMul_transpose]
  congr 1; funext k; simp [mulVec, dotProduct]

theorem pushLetters_yForm (A : Matrix (Fin n) (Fin n) E) (t : T) (b : Fin q) (v : Fin n → E) :
    pushLetters p q τ A (yForm t b fun k => τ t (cc (v k))) =
      yForm t b fun k => τ t (cc ((A *ᵥ v) k)) := by
  rw [pushLetters, colSubst_yForm]
  congr 1; funext k; simp [mulVec, dotProduct, ← ccHom_apply]

theorem eq_pushLetters (A : Matrix (Fin n) (Fin n) E)
    (F : Poly K T p q (Fin n) →ₐ[K] Poly K T p q (Fin n))
    (hx : ∀ t a (v : Fin n → E), F (xForm t a fun k => τ t (v k)) =
      xForm t a fun k => τ t ((A *ᵥ v) k))
    (hy : ∀ t b (v : Fin n → E), F (yForm t b fun k => τ t (cc (v k))) =
      yForm t b fun k => τ t (cc ((A *ᵥ v) k))) : F = pushLetters p q τ A := by
  refine MvPolynomial.algHom_ext fun ⟨t, r, k⟩ => ?_
  have h₁ : (fun l => τ t ((Pi.single k 1 : Fin n → E) l)) = Pi.single k 1 := by
    funext l; simp [Pi.single_apply, apply_ite (τ t)]
  have h₂ : (fun l => τ t (cc ((Pi.single k 1 : Fin n → E) l))) = Pi.single k 1 := by
    funext l; rw [← ccHom_apply]; by_cases h : l = k <;> simp [h]
  rcases r with a | b
  · rw [← xForm_single, ← h₁, hx, pushLetters_xForm]
  · rw [← yForm_single, ← h₂, hy, pushLetters_yForm]


theorem map_pushLetters_symO (A : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    (symO p q τ Λ).map ((pushLetters p q τ A).restrictScalars (𝓞 K)) =
      symO p q τ (Λ.map (A.mulVecLin.restrictScalars (𝓞 E))) := by
  apply le_antisymm
  · rw [Subalgebra.map_le, symO_le_iff]
    refine ⟨fun t a v hv => ?_, fun t b v hv => ?_⟩
    · rw [Subalgebra.mem_comap, AlgHom.restrictScalars_apply, pushLetters_xForm]
      exact xForm_mem_symO τ t a (Submodule.mem_map_of_mem hv)
    · rw [Subalgebra.mem_comap, AlgHom.restrictScalars_apply, pushLetters_yForm]
      exact yForm_mem_symO τ t b (Submodule.mem_map_of_mem hv)
  · rw [symO_le_iff]
    constructor
    · rintro t a _ ⟨v, hv, rfl⟩
      exact ⟨_, xForm_mem_symO τ t a hv, pushLetters_xForm τ A t a v⟩
    · rintro t b _ ⟨v, hv, rfl⟩
      exact ⟨_, yForm_mem_symO τ t b hv, pushLetters_yForm τ A t b v⟩

theorem pushLetters_mem_symO {A : Matrix (Fin n) (Fin n) E} (h : ∀ v ∈ Λ, A *ᵥ v ∈ Λ')
    (hP : P ∈ symO p q τ Λ) : pushLetters p q τ A P ∈ symO p q τ Λ' := by
  refine symO_mono τ (Λ := Λ.map (A.mulVecLin.restrictScalars (𝓞 E))) ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩; exact h v hv
  · rw [← map_pushLetters_symO]; exact ⟨P, hP, rfl⟩

theorem pushLetters_intCast_of_isHomogeneous (M : ℤ) {d : ℕ} (hP : P.IsHomogeneous d) :
    pushLetters p q τ ((M : E) • 1) P = (M : 𝓞 K) ^ d • P := by
  have : (aeval fun v => C (M : K) * X v) =
      pushLetters p q τ ((M : E) • (1 : Matrix (Fin n) (Fin n) E)) := by
    refine eq_pushLetters τ _ _ (fun t a v => ?_) fun t b v => ?_
    · simp [xForm_apply, smul_mulVec, mul_left_comm, mul_assoc]
    · simp [yForm_apply, smul_mulVec, mul_left_comm, mul_assoc, ← ccHom_apply]
  rw [← this, aeval_C_mul_X_of_isHomogeneous _ hP]
  change _ = algebraMap (𝓞 K) K ((M : 𝓞 K) ^ d) • P
  rw [map_pow, map_intCast]

theorem pow_smul_mem_symO {M : ℤ} (h : ∀ v ∈ Λ, M • v ∈ Λ') {d : ℕ} (hd : P.IsHomogeneous d)
    (hP : P ∈ symO p q τ Λ) : (M : 𝓞 K) ^ d • P ∈ symO p q τ Λ' := by
  rw [← pushLetters_intCast_of_isHomogeneous τ M hd]
  refine pushLetters_mem_symO τ (fun v hv => ?_) hP
  rw [smul_mulVec, one_mulVec, Int.cast_smul_eq_zsmul]; exact h v hv

theorem pow_smul_mem_Ha [Fintype T] {M : ℤ} (h : ∀ v ∈ Λ, M • v ∈ Λ') (hP : P ∈ Ha τ c c' Λ) :
    (M : 𝓞 K) ^ typeDegree c c' • P ∈ Ha τ c c' Λ' :=
  ⟨((rowHighest K c c').restrictScalars (𝓞 K)).smul_mem _ hP.1,
    pow_smul_mem_symO τ h (isHomogeneous_of_mem_rowHighest hP.1) hP.2⟩

theorem pow_zsmul_mem_Ha [Fintype T] {M : ℤ} (h : ∀ v ∈ Λ, M • v ∈ Λ') (hP : P ∈ Ha τ c c' Λ) :
    M ^ typeDegree c c' • P ∈ Ha τ c c' Λ' := by
  have := pow_smul_mem_Ha τ h hP
  rw [← Int.cast_pow] at this
  exact (Int.cast_smul_eq_zsmul (𝓞 K) (M ^ typeDegree c c') P) ▸ this

theorem transpose_mul_map_ccHom_eq_one {A : Matrix (Fin n) (Fin n) E}
    (hA : ∀ x y, herm 1 (A *ᵥ x) (A *ᵥ y) = herm 1 x y) : Aᵀ * A.map (ccHom E) = 1 := by
  ext i j
  have := hA (Pi.single i 1) (Pi.single j 1)
  rw [herm_one_eq_sum, herm_one_eq_sum] at this
  simp only [mulVec_single_one, col_apply, ← ccHom_apply] at this
  rw [mul_apply]
  refine this.trans ?_
  by_cases h : i = j <;> simp [Pi.single_apply, one_apply, h, eq_comm]

theorem pushLetters_eq_colAct {γ : GL (Fin n) E}
    (hγ : ∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y) (P : Poly K T p q (Fin n)) :
    pushLetters p q τ γ.val P = colAct K T p q (Fin n)
      (fun t => Matrix.GeneralLinearGroup.map ((τ t).comp (ccHom E)) γ) P := by
  rw [colAct_apply, pushLetters]
  congr 2
  funext t
  refine (Units.inv_eq_of_mul_eq_one_left ?_).symm
  have := congrArg (fun B => B.map (τ t)) (transpose_mul_map_ccHom_eq_one hγ)
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem pushLetters_mem_rowHighest_iff {γ : GL (Fin n) E}
    (hγ : ∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y) :
    pushLetters p q τ γ.val P ∈ rowHighest K c c' ↔ P ∈ rowHighest K c c' := by
  rw [pushLetters_eq_colAct τ hγ, colAct_mem_rowHighest_iff]

variable (c c') in

theorem map_pushLetters_Ha {γ : GL (Fin n) E}
    (hγ : ∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y)
    (Λ : Submodule (𝓞 E) (Fin n → E)) :
    (Ha τ c c' Λ).map ((pushLetters p q τ γ.val).toLinearMap.restrictScalars (𝓞 K)) =
      Ha τ c c' (Λ.map (γ.val.mulVecLin.restrictScalars (𝓞 E))) := by
  ext Q
  rw [mem_Ha, ← map_pushLetters_symO]
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨(pushLetters_mem_rowHighest_iff τ hγ).2 hP.1, P, hP.2, rfl⟩
  · rintro ⟨hQ, P, hP, rfl⟩
    exact ⟨P, ⟨(pushLetters_mem_rowHighest_iff τ hγ).1 hQ, hP⟩, rfl⟩

omit [IsCMField E] in

theorem exists_zsmul_mem_of_mem_span {v : Fin n → E} (hv : v ∈ Submodule.span E (Λ : Set _)) :
    ∃ N : ℤ, N ≠ 0 ∧ N • v ∈ Λ := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨1, one_ne_zero, by simpa using hv⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨M, hM, hv⟩ := hv
    obtain ⟨N, hN, hw⟩ := hw
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact zsmul_mem hv N
    · rw [mul_smul]; exact zsmul_mem hw M
  | smul r v _ hv =>
    obtain ⟨N, hN, hv⟩ := hv
    have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
    obtain ⟨M, hM, hr⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) r).exists_integral_multiple
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have := Λ.smul_mem (⟨M • r, hr⟩ : 𝓞 E) hv
    convert this using 1
    change _ = (M • r) • N • v
    rw [smul_assoc, smul_comm r N v, mul_smul]

omit [IsCMField E] in

theorem exists_zsmul_le (hΛ : Λ.FG) (hΛ' : Submodule.span E (Λ' : Set (Fin n → E)) = ⊤) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ v ∈ Λ, N • v ∈ Λ' := by
  classical
  obtain ⟨s, rfl⟩ := hΛ
  choose N hN hN' using fun v => exists_zsmul_mem_of_mem_span (Λ := Λ') (v := v) (hΛ' ▸ trivial)
  refine ⟨∏ w ∈ s, N w, Finset.prod_ne_zero_iff.2 fun w _ => hN w, fun v hv => ?_⟩
  induction hv using Submodule.span_induction with
  | mem v hv => rw [← Finset.prod_erase_mul s N hv, mul_smul]; exact zsmul_mem (hN' v) _
  | zero => simp
  | add v w _ _ hv hw => rw [smul_add]; exact add_mem hv hw
  | smul r v _ hv => rw [smul_comm]; exact Λ'.smul_mem r hv

omit [NumberField E] [IsCMField E] in

theorem mem_pi_one_iff {v : Fin n → E} :
    v ∈ Submodule.pi Set.univ (fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, IsIntegral ℤ (v k) := by
  simp only [Submodule.mem_pi, Set.mem_univ, forall_const, Submodule.mem_one]
  exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun h => ⟨⟨_, h⟩, rfl⟩⟩

omit [NumberField E] [IsCMField E] in

theorem span_range_single_eq_pi_one :
    Submodule.span (𝓞 E) (Set.range fun k : Fin n => (Pi.single k 1 : Fin n → E)) =
      Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine mem_pi_one_iff.2 fun l => ?_
    by_cases h : l = k <;> simp [h, isIntegral_one, isIntegral_zero]
  · intro v hv
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hv k trivial)
    have : (Pi.single k (v k) : Fin n → E) = y • (Pi.single k 1 : Fin n → E) := by
      rw [← Pi.single_smul', Algebra.smul_def, mul_one, hy]
    rw [this]
    exact Submodule.smul_mem _ y (Submodule.subset_span ⟨k, rfl⟩)

omit [NumberField E] [IsCMField E] in

theorem fg_pi_one : (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)).FG :=
  span_range_single_eq_pi_one (E := E) ▸ Submodule.fg_span (Set.finite_range _)

omit [NumberField E] [IsCMField E] in

theorem span_pi_one_eq_top : Submodule.span E
    (Submodule.pi Set.univ (fun _ : Fin n => (1 : Submodule (𝓞 E) E)) : Set (Fin n → E)) = ⊤ := by
  rw [← span_range_single_eq_pi_one, Submodule.span_span_of_tower, ← (Pi.basisFun E (Fin n)).span_eq]
  congr 2; funext k; simp

theorem mem_range_map_ringOfIntegers_iff {σ : Type*} {P : MvPolynomial σ K} :
    (∃ Q, MvPolynomial.map (algebraMap (𝓞 K) K) Q = P) ↔ ∀ m, IsIntegral ℤ (coeff m P) := by
  constructor
  · rintro ⟨Q, rfl⟩ m
    rw [coeff_map]; exact (coeff m Q).isIntegral_coe
  · intro h
    refine ⟨∑ m ∈ P.support, monomial m ⟨_, h m⟩, ?_⟩
    conv_rhs => rw [P.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => map_monomial _ _ _

theorem symO_pi_one : symO p q τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
    (mapAlgHom (σ := Var T p q (Fin n)) (Algebra.ofId (𝓞 K) K)).range := by
  apply le_antisymm
  · refine (symO_le_iff τ).2 ⟨fun t a v hv => ?_, fun t b v hv => ?_⟩
    · exact ⟨xForm t a fun k => ⟨_, map_isIntegral_int (τ t) (mem_pi_one_iff.1 hv k)⟩,
        map_xForm (algebraMap (𝓞 K) K) t a _⟩
    · exact ⟨yForm t b fun k =>
        ⟨_, map_isIntegral_int ((τ t).comp (ccHom E)) (mem_pi_one_iff.1 hv k)⟩,
        map_yForm (algebraMap (𝓞 K) K) t b _⟩
  · rintro _ ⟨Q, rfl⟩
    change mapAlgHom (Algebra.ofId (𝓞 K) K) Q ∈ _
    induction Q using MvPolynomial.induction_on with
    | C r => rw [← algebraMap_eq, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ r
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | mul_X P v hP =>
      rw [map_mul]
      refine mul_mem hP ?_
      obtain ⟨t, r, k⟩ := v
      have hk : (Pi.single k 1 : Fin n → E) ∈
          Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E) :=
        span_range_single_eq_pi_one (E := E) ▸ Submodule.subset_span ⟨k, rfl⟩
      have h₁ : (fun l => τ t ((Pi.single k 1 : Fin n → E) l)) = Pi.single k 1 := by
        funext l; simp [Pi.single_apply, apply_ite (τ t)]
      have h₂ : (fun l => τ t (cc ((Pi.single k 1 : Fin n → E) l))) = Pi.single k 1 := by
        funext l; rw [← ccHom_apply]; by_cases h : l = k <;> simp [h]
      change MvPolynomial.map (algebraMap (𝓞 K) K) _ ∈ _
      rw [map_X]
      rcases r with a | b
      · rw [← xForm_single, ← h₁]; exact xForm_mem_symO τ t a hk
      · rw [← yForm_single, ← h₂]; exact yForm_mem_symO τ t b hk

theorem mem_symO_pi_one_iff :
    P ∈ symO p q τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
      ∀ m, IsIntegral ℤ (coeff m P) := by
  rw [symO_pi_one, ← mem_range_map_ringOfIntegers_iff]; rfl

variable (c c') in

theorem Ha_pi_one_eq_map :
    Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
      (rowHighest (𝓞 K) c c').map
        (mapAlgHom (σ := Var T p q (Fin n)) (Algebra.ofId (𝓞 K) K)).toLinearMap := by
  ext P
  rw [mem_Ha, symO_pi_one]
  constructor
  · rintro ⟨hP, Q, rfl⟩
    exact ⟨Q, (map_mem_rowHighest_iff (FaithfulSMul.algebraMap_injective (𝓞 K) K)).1 hP, rfl⟩
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨map_mem_rowHighest (algebraMap (𝓞 K) K) hQ, Q, rfl⟩

variable [NumberField K]

variable (c c') in

theorem Ha_pi_one_eq_span :
    Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
      Submodule.span (𝓞 K) (MvPolynomial.map (Int.castRingHom K) ''
        (rowHighest ℤ (κ := Fin n) c c' : Set (Poly ℤ T p q (Fin n)))) := by
  rw [Ha_pi_one_eq_map, ← span_map_rowHighest ℤ (𝓞 K), Submodule.map_span, Set.image_image]
  congr 2
  funext P
  change MvPolynomial.map (algebraMap (𝓞 K) K) _ = _
  rw [MvPolynomial.map_map]
  congr 2

variable [Fintype T]

variable (c c') in

theorem fg_Ha (hΛ : Λ.FG) : (Ha τ c c' Λ).FG := by
  obtain ⟨N, hN, h⟩ := exists_zsmul_le hΛ (span_pi_one_eq_top (E := E))
  have h₀ : (Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))).FG := by
    rw [Ha_pi_one_eq_map]
    exact (Module.Finite.iff_fg.1 inferInstance).map _
  have hd : (N : 𝓞 K) ^ typeDegree c c' ≠ 0 := pow_ne_zero _ (Int.cast_ne_zero.2 hN)
  refine Submodule.fg_of_fg_map_injective
    (LinearMap.lsmul (𝓞 K) (Poly K T p q (Fin n)) ((N : 𝓞 K) ^ typeDegree c c'))
    (LinearMap.lsmul_injective hd) (h₀.of_le ?_)
  rintro _ ⟨P, hP, rfl⟩
  exact pow_smul_mem_Ha τ h hP

theorem exists_zsmul_mem_Ha (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤)
    (hP : P ∈ rowHighest K c c') : ∃ N : ℤ, N ≠ 0 ∧ N • P ∈ Ha τ c c' Λ := by
  classical
  obtain ⟨N, hN, h⟩ := exists_zsmul_le (fg_pi_one (E := E)) hΛ
  have : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨M, hM, hM'⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (P.support.image fun m => coeff m P)
  have h₀ : M • P ∈ Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
    refine ⟨zsmul_mem hP M, (mem_symO_pi_one_iff τ).2 fun m => ?_⟩
    rw [coeff_smul]
    by_cases hm : m ∈ P.support
    · exact hM' _ (Finset.mem_image_of_mem _ hm)
    · rw [notMem_support_iff.1 hm, smul_zero]; exact isIntegral_zero
  refine ⟨N ^ typeDegree c c' * M, mul_ne_zero (pow_ne_zero _ hN) hM, ?_⟩
  rw [mul_smul]
  exact pow_zsmul_mem_Ha τ h h₀

variable (c c') in

theorem span_Ha (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    Submodule.span K (Ha τ c c' Λ : Set (Poly K T p q (Fin n))) = rowHighest K c c' := by
  refine le_antisymm (Submodule.span_le.2 fun P hP => hP.1) fun P hP => ?_
  obtain ⟨N, hN, h⟩ := exists_zsmul_mem_Ha τ hΛ hP
  rw [← Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hN : (N : K) ≠ 0), Int.cast_smul_eq_zsmul]
  exact Submodule.subset_span h

variable (c c') in

theorem Ha_ne_bot (h : p + q ≤ n) (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    Ha τ c c' Λ ≠ ⊥ := fun e =>
  rowHighest_ne_bot (R := K) h c c' (by rw [← span_Ha τ c c' hΛ, e]; simp)

omit [NumberField K] in
variable (c c') in

theorem pow_zsmul_Ha_of_isCoprime {ℓ M : ℤ} (hM : IsCoprime M ℓ) (h : ∀ v ∈ Λ, M • v ∈ Λ')
    (h' : ∀ v ∈ Λ', M • v ∈ Λ) :
    IsCoprime (M ^ typeDegree c c') ℓ ∧
      (∀ P ∈ Ha τ c c' Λ, M ^ typeDegree c c' • P ∈ Ha τ c c' Λ') ∧
      ∀ P ∈ Ha τ c c' Λ', M ^ typeDegree c c' • P ∈ Ha τ c c' Λ := by
  refine ⟨hM.pow_left, fun P hP => ?_, fun P hP => ?_⟩
  · exact pow_zsmul_mem_Ha τ h hP
  · exact pow_zsmul_mem_Ha τ h' hP

variable (c c' Λ) in

theorem integral_harmonic_on_lattice (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    (∀ (e : T → Fin p → Fin n → E) (f : T → Fin q → Fin n → E), (∀ t a, e t a ∈ Λ) →
      (∀ t b, f t b ∈ Λ) → (∀ t a b, herm 1 (e t a) (f t b) = 0) →
      minorProd c c' (fun t a k => τ t (e t a k)) (fun t b k => τ t (cc (f t b k))) ∈
        Ha τ c c' Λ) ∧
    ((Ha τ c c' Λ).FG ∧
      Submodule.span K (Ha τ c c' Λ : Set (Poly K T p q (Fin n))) = rowHighest K c c') ∧
    ((∀ P, P ∈ symO p q τ (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) ↔
        ∀ m, IsIntegral ℤ (coeff m P)) ∧
      Ha τ c c' (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) =
        Submodule.span (𝓞 K) (MvPolynomial.map (Int.castRingHom K) ''
          (rowHighest ℤ (κ := Fin n) c c' : Set (Poly ℤ T p q (Fin n))))) ∧
    (∀ γ : GL (Fin n) E, (∀ x y, herm 1 (γ.val *ᵥ x) (γ.val *ᵥ y) = herm 1 x y) →
      ∀ F, F = colAct K T p q (Fin n)
          (fun t => Matrix.GeneralLinearGroup.map ((τ t).comp (ccHom E)) γ) →
        (∀ t a (v : Fin n → E),
          F (xForm t a fun k => τ t (v k)) = xForm t a fun k => τ t ((γ.val *ᵥ v) k)) ∧
        (∀ t b (v : Fin n → E),
          F (yForm t b fun k => τ t (cc (v k))) = yForm t b fun k => τ t (cc ((γ.val *ᵥ v) k))) ∧
        (∀ P, F P ∈ rowHighest K c c' ↔ P ∈ rowHighest K c c') ∧
        F '' (Ha τ c c' Λ : Set (Poly K T p q (Fin n))) =
          Ha τ c c' (Λ.map (γ.val.mulVecLin.restrictScalars (𝓞 E)))) ∧
    ∀ (Λ' : Submodule (𝓞 E) (Fin n → E)) (M : ℤ), (∀ v ∈ Λ, M • v ∈ Λ') →
      ∀ P ∈ Ha τ c c' Λ, M ^ typeDegree c c' • P ∈ Ha τ c c' Λ' := by
  refine ⟨fun e f => minorProd_mem_Ha τ c c', ⟨fg_Ha τ c c' hfg, span_Ha τ c c' hspan⟩,
    ⟨fun P => mem_symO_pi_one_iff τ, Ha_pi_one_eq_span τ c c'⟩, ?_, fun Λ' M h P hP => ?_⟩
  · rintro γ hγ _ rfl
    simp only [← pushLetters_eq_colAct τ hγ, pushLetters_xForm, pushLetters_yForm,
      pushLetters_mem_rowHighest_iff τ hγ, implies_true, true_and]
    rw [← map_pushLetters_Ha τ c c' hγ]; rfl
  · exact pow_zsmul_mem_Ha τ h hP

end Lattice

end GlobalTheory.Harm
end

section
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.TB (perpVec)

namespace GlobalTheory.Harm

open GlobalTheory.MvPoly GlobalTheory.GridSize

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

variable (E n) in

noncomputable def conjVec : (Fin n → E) →ₛₗ[((IsCMField.ringOfIntegersComplexConj E).toRingEquiv :
    𝓞 E →+* 𝓞 E)] (Fin n → E) where
  toFun v k := cc (v k)
  map_add' v w := funext fun k => map_add (IsCMField.complexConj E) (v k) (w k)
  map_smul' a v := funext fun k => map_mul (IsCMField.complexConj E) (a : E) (v k)

@[simp] theorem conjVec_apply (v : Fin n → E) (k : Fin n) : conjVec E n v k = cc (v k) := rfl

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in

@[simp] theorem _root_.GlobalTheory.Harm.conjVec_conjVec (v : Fin n → E) :
    _root_.GlobalTheory.Harm.conjVec E n (_root_.GlobalTheory.Harm.conjVec E n v) = v := by
  funext k
  exact _root_.GlobalTheory.TraceDualMin.cc_cc (v k)

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in

theorem _root_.GlobalTheory.Harm.herm_conjVec (v w : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (_root_.GlobalTheory.Harm.conjVec E n v) (_root_.GlobalTheory.Harm.conjVec E n w)
      = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w v := by
  simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.Harm.conjVec_apply,
    _root_.GlobalTheory.TraceDualMin.cc_cc]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

noncomputable def conjLattice (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map (conjVec E n)

variable {Λ : Submodule (𝓞 E) (Fin n → E)}

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.mem_conjLattice {v : Fin n → E} :
    v ∈ _root_.GlobalTheory.Harm.conjLattice Λ ↔ _root_.GlobalTheory.Harm.conjVec E n v ∈ Λ := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec]
    exact hw
  · intro hv
    exact ⟨_, hv, _root_.GlobalTheory.Harm.conjVec_conjVec v⟩

@[simp] theorem conjLattice_conjLattice : conjLattice (conjLattice Λ) = Λ := by
  ext v; rw [mem_conjLattice, mem_conjLattice, conjVec_conjVec]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.conjLattice_selfDual (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    (_root_.GlobalTheory.Harm.conjLattice Λ).FG ∧
      (∀ x ∈ _root_.GlobalTheory.Harm.conjLattice Λ, ∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) ∧
      ∀ x, (∀ y ∈ _root_.GlobalTheory.Harm.conjLattice Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) →
        x ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
  refine ⟨hfg.map _, ?_, ?_⟩
  · intro x hx y hy
    rw [_root_.GlobalTheory.Harm.mem_conjLattice] at hx hy
    have h := hint _ hy _ hx
    rwa [_root_.GlobalTheory.Harm.herm_conjVec] at h
  · intro x hx
    rw [_root_.GlobalTheory.Harm.mem_conjLattice]
    refine hdual _ fun y hy => ?_
    have hy' : _root_.GlobalTheory.Harm.conjVec E n y ∈ _root_.GlobalTheory.Harm.conjLattice Λ := by
      rw [_root_.GlobalTheory.Harm.mem_conjLattice, _root_.GlobalTheory.Harm.conjVec_conjVec]
      exact hy
    have h := _root_.GlobalTheory.TraceDualMin.isIntegral_cc (hx _ hy')
    rw [← _root_.GlobalTheory.DualFamily.herm_one_symm] at h
    have h2 := _root_.GlobalTheory.Harm.herm_conjVec (E := E) x (_root_.GlobalTheory.Harm.conjVec E n y)
    rw [_root_.GlobalTheory.Harm.conjVec_conjVec] at h2
    rw [h2]
    exact h

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in
omit [IsCMField E] in

theorem _root_.GlobalTheory.Harm.one_le_rdE : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE E := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rdE _root_.ReciprocityTheory.ChartRestriction.G.FD.dE
  apply Real.one_le_rpow _ (by positivity)
  have h : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have h' : (1 : ℝ) ≤ |((discr E : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  exact_mod_cast h'

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.one_le_fdeg : 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
  have h := _root_.GlobalTheory.ShortVectors.finrank_eq (E := E)
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  omega

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.one_le_add_of_one_le_typeDegree {T : Type*} [Fintype T] {p q : ℕ}
    {c : T → Fin p → ℕ} {c' : T → Fin q → ℕ} (ha : 1 ≤ _root_.GlobalTheory.Harm.typeDegree c c') :
    1 ≤ p + q := by
  by_contra hpq
  obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
  simp [_root_.GlobalTheory.Harm.typeDegree, _root_.GlobalTheory.Harm.partSize] at ha

variable (E n) in

noncomputable def hermPairing : (Fin n → E) →ₗ[E] ((Fin n → E) → E) where
  toFun x y := herm 1 x y
  map_add' x x' := funext fun y => by simp [herm_one_eq_sum, add_mul, Finset.sum_add_distrib]
  map_smul' r x := funext fun y => TraceDualMin.herm_smul_left r x y

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
variable {Λ : Submodule (𝓞 E) (Fin n → E)} in

theorem _root_.GlobalTheory.Harm.perpVec_hermPairing_mem
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) {p : ℕ}
    {e e' : Fin p → Fin n → E} {g : Fin n → E} (he : ∀ a, e a ∈ Λ) (he' : ∀ a, e' a ∈ Λ)
    (hg : g ∈ Λ) : _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec (_root_.GlobalTheory.Harm.hermPairing E n) e e' g ∈ Λ := by
  classical
  unfold _root_.ReciprocityTheory.ChartRestriction.G.TB.perpVec
  set M := _root_.ReciprocityTheory.ChartRestriction.G.TB.hMat (_root_.GlobalTheory.Harm.hermPairing E n) e e' with hM
  have hMint : ∀ i j, IsIntegral ℤ (M i j) := fun i j => hint _ (he' i) _ (he j)
  let Mo : Matrix (Fin p) (Fin p) (𝓞 E) := fun i j => ⟨M i j, hMint i j⟩
  have hMo : M = (algebraMap (𝓞 E) E).mapMatrix Mo := by ext i j; rfl
  have key : ∀ (c : 𝓞 E) (x : Fin n → E), x ∈ Λ → ((c : E) • x) ∈ Λ :=
    fun c x hx => Λ.smul_mem c hx
  apply Λ.sub_mem
  · rw [hMo, ← RingHom.map_det]
    exact key _ _ hg
  · refine Λ.sum_mem fun a _ => Λ.sum_mem fun a' _ => ?_
    have hga : IsIntegral ℤ (_root_.GlobalTheory.Harm.hermPairing E n g (e a)) := hint _ hg _ (he a)
    rw [hMo, ← RingHom.map_adjugate]
    have hc : (algebraMap (𝓞 E) E).mapMatrix Mo.adjugate a a'
        * _root_.GlobalTheory.Harm.hermPairing E n g (e a)
        = ((Mo.adjugate a a' * ⟨_, hga⟩ : 𝓞 E) : E) := by
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
      rfl
    rw [hc]
    exact key _ _ (he' a')

end GlobalTheory.Harm
end
