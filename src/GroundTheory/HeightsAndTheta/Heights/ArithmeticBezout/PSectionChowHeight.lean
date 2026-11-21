import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemConePointsSpanX0
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRecQOfRecursion
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)

open Classical in

def SectionChowHeight.Statement : Prop :=
  ∀ (n e δ : ℕ) (S : Matrix (Fin n) (Fin n) ℂ) (P : Ideal (MRing (PBlk n)))
    (f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ) (u : Fin n → ℤ)
    (g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ)
    (d : Ideal (MRing (PBlk n)) → ℕ),
    IsUnit S → IsArithVar P (e + 1 + 1) →
    ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f) →
    IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P →
    (∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W))) →
      IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℚ)) f) δ =
        ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
          (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
            (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0)

end GroundTheory.Heights₂.Heights
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

namespace ChowHeightCycleEq

variable {n e : ℕ}

theorem chowHt_sub {K : Type} [Field K] [NumberField K]
    (μ ν : InfinitePlace K → Measure (Fin (e + 1) × Fin n → ℂ))
    (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ P δ - ReciprocityTheory.ChartRestriction.G.Geo.chowHt ν P δ =
      (∑ w : InfinitePlace K, (w.mult : ℝ) *
        (ReciprocityTheory.ChartRestriction.G.Geo.logMean (μ w) (map w.embedding P) -
          ReciprocityTheory.ChartRestriction.G.Geo.logMean (ν w) (map w.embedding P))) / Height.totalWeight K := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.chowHt ReciprocityTheory.ChartRestriction.G.Geo.chowHeightOfForm
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem cycle_of_mul {K : Type} [Field K] [NumberField K]
    (μ : InfinitePlace K → Measure (Fin (e + 1) × Fin n → ℂ))
    (hμ : ∀ (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ), f ≠ 0 → g ≠ 0 →
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f * g) (δ₁ + δ₂) =
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ f δ₁ + ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ g δ₂)
    {ι : Type} (Z : ι →₀ ℕ) (f : ι → MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ι → ℕ)
    (hf : ∀ i ∈ Z.support, f i ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (IndefiniteRowSideFullHecke.ArithBezout.cycleChowForm Z f) (Z.sum fun i m => m * δ i) =
      Z.sum fun i m => (m : ℝ) * ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f i) (δ i) := by
  classical
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (1 : MvPolynomial (Fin (e + 1) × Fin n) K) 0 = 0 := by
    have := hμ 1 1 0 0 one_ne_zero one_ne_zero
    simp only [mul_one, add_zero] at this
    linarith
  have hpow : ∀ (g : MvPolynomial (Fin (e + 1) × Fin n) K) (d : ℕ), g ≠ 0 → ∀ m : ℕ,
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (g ^ m) (m * d) = m * ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ g d := by
    intro g d hg m
    induction m with
    | zero => simpa using h1
    | succ m ih =>
      rw [pow_succ, Nat.succ_mul, hμ _ _ _ _ (pow_ne_zero _ hg) hg, ih]
      push_cast
      ring
  have key : ∀ s : Finset ι, (∀ i ∈ s, f i ≠ 0) →
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (∏ i ∈ s, f i ^ Z i) (∑ i ∈ s, Z i * δ i) =
        ∑ i ∈ s, (Z i : ℝ) * ReciprocityTheory.ChartRestriction.G.Geo.chowHt μ (f i) (δ i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using h1
    | insert a s ha ih =>
      intro hs
      have hfa := hs a (Finset.mem_insert_self a s)
      have hrest : ∀ i ∈ s, f i ≠ 0 := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
        hμ _ _ _ _ (pow_ne_zero _ hfa)
          (Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hrest i hi)),
        hpow _ _ hfa, ih hrest]
  exact key Z.support hf

def conjNorm (h : HermNorm n) : HermNorm n where
  mat := h.mat.map (starRingEnd ℂ)
  isUnit_det := by
    rw [show h.mat.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix h.mat from rfl,
      ← RingHom.map_det]
    exact h.isUnit_det.map _

open Matrix in
theorem conjNorm_norm_star (h : HermNorm n) (u : Fin n → ℂ) :
    (conjNorm h).norm (star u) = h.norm u := by
  unfold HermNorm.norm conjNorm
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have : ((h.mat.map (starRingEnd ℂ)) *ᵥ star u) i = starRingEnd ℂ ((h.mat *ᵥ u) i) := by
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [this, Complex.norm_conj]

open Classical in

def archOfPlaces {K : Type} [Field K] [NumberField K] (N : InfinitePlace K → HermNorm n)
    (hN : ∀ w : InfinitePlace K, w.IsReal → ∀ u, (N w).norm (star u) = (N w).norm u) :
    ArchData K n where
  normAt σ := if σ = (InfinitePlace.mk σ).embedding then N (InfinitePlace.mk σ)
    else conjNorm (N (InfinitePlace.mk σ))
  conj_norm σ u := by
    simp only [InfinitePlace.mk_conjugate_eq]
    have hreal : ComplexEmbedding.conjugate σ = σ → (InfinitePlace.mk σ).IsReal := fun h =>
      InfinitePlace.isReal_mk_iff.mpr (ComplexEmbedding.isReal_iff.mpr h)
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · by_cases hc : ComplexEmbedding.conjugate σ = (InfinitePlace.mk σ).embedding
      · rw [if_pos hc, if_pos h.symm]
        exact hN _ (hreal (hc.trans h)) u
      · rw [if_neg hc, if_pos h.symm]
        exact conjNorm_norm_star _ u
    · by_cases hs : σ = (InfinitePlace.mk σ).embedding
      · rw [if_pos h.symm, if_pos hs]
        exact hN _ (hreal (h.symm.trans hs.symm)) u
      · rw [if_pos h.symm, if_neg hs, ← conjNorm_norm_star (N _) (star u), star_star]

theorem archOfPlaces_embedding {K : Type} [Field K] [NumberField K]
    (N : InfinitePlace K → HermNorm n)
    (hN : ∀ w : InfinitePlace K, w.IsReal → ∀ u, (N w).norm (star u) = (N w).norm u)
    (w : InfinitePlace K) : (archOfPlaces N hN).normAt w.embedding = N w := by
  simp [archOfPlaces, InfinitePlace.mk_embedding]

theorem formNorm_one_star (u : Fin n → ℂ) :
    IndefiniteRowSideFullHecke.ArithBezout.formNorm (1 : Matrix (Fin n) (Fin n) ℂ) (star u) =
      IndefiniteRowSideFullHecke.ArithBezout.formNorm 1 u := by
  rw [← ObjectsHeight.ofPointMatrix_norm 1 isUnit_one, ← ObjectsHeight.ofPointMatrix_norm 1 isUnit_one,
    ← ObjectsHeight.std_eq_ofPointMatrix_one]
  exact (ArchData.std ℚ n).conj_norm (Rat.castHom ℂ) u

theorem additive_of_conjInv (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hT : ∀ w, IsUnit (T w))
    (hreal : ∀ w : InfinitePlace K, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) (f * g)
        (δ₁ + δ₂) =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) f δ₁ +
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) g δ₂ := by
  let H := archOfPlaces (fun w => ObjectsHeight.ofPointMatrix (T w) (hT w)) (fun w hw u => by
    rw [ObjectsHeight.ofPointMatrix_norm, ObjectsHeight.ofPointMatrix_norm]
    exact hreal w hw u)
  have hH : ∀ w u, (H.normAt w.embedding).norm u = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u :=
    fun w u => by rw [archOfPlaces_embedding, ObjectsHeight.ofPointMatrix_norm]
  rw [← ObjectsHeight.chowHt_eq_chowHt_places H T hT hH,
    ← ObjectsHeight.chowHt_eq_chowHt_places H T hT hH,
    ← ObjectsHeight.chowHt_eq_chowHt_places H T hT hH]
  exact hA K n H (e + 1) δ₁ δ₂ f g hf hg

def meanShift {K : Type} [Field K] (S : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    (P : MvPolynomial (Fin (e + 1) × Fin n) K) : ℝ :=
  ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (e + 1)) (map σ P) -
    ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw 1 (e + 1)) (map σ P)

theorem meanShift_mul_of_ext (hA : ChowHeightMul.Statement) {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] (j : K →+* L) (τ : L →+* ℂ) (hτ : ¬ ComplexEmbedding.IsReal τ)
    (σ : K →+* ℂ) (hσ : ComplexEmbedding.IsReal σ) (hτj : τ.comp j = σ)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0) :
    meanShift S σ (f * g) = meanShift S σ f + meanShift S σ g := by
  classical
  set w' := InfinitePlace.mk τ with hw'
  have hw'c : ¬ w'.IsReal := fun h => hτ (InfinitePlace.isReal_mk_iff.mp h)
  let T : InfinitePlace L → Matrix (Fin n) (Fin n) ℂ := fun w => if w = w' then S else 1
  have hT : ∀ w, IsUnit (T w) := by
    intro w
    by_cases h : w = w'
    · simp only [T, if_pos h]; exact hS
    · simp only [T, if_neg h]; exact isUnit_one
  have hTr : ∀ w : InfinitePlace L, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u := by
    intro w hw u
    have : w ≠ w' := fun h => hw'c (h ▸ hw)
    simp only [T, if_neg this]
    exact formNorm_one_star u
  have h1 : ∀ w : InfinitePlace L, IsUnit ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w) :=
    fun _ => isUnit_one
  have h1r : ∀ w : InfinitePlace L, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w) (star u) =
        IndefiniteRowSideFullHecke.ArithBezout.formNorm ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w) u :=
    fun _ _ u => formNorm_one_star u
  have hconj : (ComplexEmbedding.conjugate τ).comp j = σ := by
    ext x
    have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hσ) x
    rw [ComplexEmbedding.conjugate_coe_eq] at h2
    rw [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, ← RingHom.comp_apply τ j, hτj, h2]
  have hmap : ∀ P : MvPolynomial (Fin (e + 1) × Fin n) K,
      map w'.embedding (map j P) = map σ P := by
    intro P
    rw [map_map]
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [hw', h, hτj]
    · rw [hw', h, hconj]
  have hdiff : ∀ (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ),
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) (map j P) δ -
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt
          (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw ((fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) w)
            (e + 1)) (map j P) δ =
        (w'.mult : ℝ) * meanShift S σ P / Height.totalWeight L := by
    intro P δ
    rw [chowHt_sub, Finset.sum_eq_single w']
    · simp only [T, if_pos rfl, hmap]
      rfl
    · intro w _ hw
      simp only [T, if_neg hw, sub_self, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hinj : Function.Injective (map j : MvPolynomial (Fin (e + 1) × Fin n) K → _) :=
    map_injective j j.injective
  have hF : map j f ≠ 0 := fun h => hf (hinj (by rw [h, map_zero]))
  have hG : map j g ≠ 0 := fun h => hg (hinj (by rw [h, map_zero]))
  have addT := additive_of_conjInv hA T hT hTr (map j f) (map j g) 0 0 hF hG
  have add1 := additive_of_conjInv hA _ h1 h1r (map j f) (map j g) 0 0 hF hG
  have hd1 := hdiff (f * g) 0
  have hd2 := hdiff f 0
  have hd3 := hdiff g 0
  rw [map_mul] at hd1
  simp only [add_zero] at addT add1
  have htw : (Height.totalWeight L : ℝ) ≠ 0 := by
    rw [NumberField.totalWeight_eq_finrank]
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hc : (w'.mult : ℝ) / Height.totalWeight L ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr InfinitePlace.mult_pos.ne') htw
  apply mul_left_cancel₀ hc
  have e1 : ∀ x : ℝ, (w'.mult : ℝ) / Height.totalWeight L * x =
      (w'.mult : ℝ) * x / Height.totalWeight L := fun x => by ring
  rw [mul_add, e1, e1, e1, ← hd1, ← hd2, ← hd3, addT, add1]
  ring

theorem meanShift_mul (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (σ : K →+* ℂ) (hσ : ComplexEmbedding.IsReal σ)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (hf : f ≠ 0) (hg : g ≠ 0) :
    meanShift S σ (f * g) = meanShift S σ f + meanShift S σ g := by
  set p : Polynomial K := Polynomial.X ^ 2 + Polynomial.C 1 with hp
  have hroot : ∀ x : K, ¬ p.IsRoot x := by
    intro x hx
    have h1 : σ x ^ 2 + 1 = 0 := by
      have := congrArg σ hx
      simpa [hp] using this
    have him : (σ x).im = 0 := by
      have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp hσ) x
      rw [ComplexEmbedding.conjugate_coe_eq] at h2
      exact Complex.conj_eq_iff_im.mp h2
    have h3 := congrArg Complex.re h1
    simp [sq, him] at h3
    nlinarith [mul_self_nonneg (σ x).re]
  have hdeg : p.natDegree = 2 := by
    rw [hp]; compute_degree!
  have hirr : Irreducible p :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; decide) hroot
  have : Fact (Irreducible p) := ⟨hirr⟩
  have hmon : p.Monic := Polynomial.monic_X_pow_add_C 1 (by norm_num)
  have : Module.Finite K (AdjoinRoot p) := hmon.finite_adjoinRoot
  have : NumberField (AdjoinRoot p) := NumberField.of_module_finite K (AdjoinRoot p)
  have heval : p.eval₂ σ Complex.I = 0 := by simp [hp]
  let τ : AdjoinRoot p →+* ℂ := AdjoinRoot.lift σ Complex.I heval
  have hτj : τ.comp (AdjoinRoot.of p) = σ := by
    ext x
    exact AdjoinRoot.lift_of heval
  have hτ : ¬ ComplexEmbedding.IsReal τ := by
    intro h
    have h2 := RingHom.congr_fun (ComplexEmbedding.isReal_iff.mp h) (AdjoinRoot.root p)
    rw [ComplexEmbedding.conjugate_coe_eq] at h2
    have h3 : τ (AdjoinRoot.root p) = Complex.I := AdjoinRoot.lift_root heval
    rw [h3, Complex.conj_I] at h2
    have h4 := congrArg Complex.im h2
    simp at h4
    norm_num at h4
  exact meanShift_mul_of_ext hA (AdjoinRoot.of p) τ hτ σ hσ hτj S hS f g hf hg

theorem additive (hA : ChowHeightMul.Statement) {K : Type} [Field K] [NumberField K]
    (S : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hS : ∀ w, IsUnit (S w))
    (f g : MvPolynomial (Fin (e + 1) × Fin n) K) (δ₁ δ₂ : ℕ) (hf : f ≠ 0) (hg : g ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) (f * g)
        (δ₁ + δ₂) =
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) f δ₁ +
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) g δ₂ := by
  classical
  let T : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ := fun w => if w.IsReal then 1 else S w
  have hT : ∀ w, IsUnit (T w) := by
    intro w
    by_cases h : w.IsReal
    · simp only [T, if_pos h]; exact isUnit_one
    · simp only [T, if_neg h]; exact hS w
  have hTr : ∀ w : InfinitePlace K, w.IsReal → ∀ u,
      IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm (T w) u := by
    intro w hw u
    simp only [T, if_pos hw]
    exact formNorm_one_star u
  have hsplit : ∀ (P : MvPolynomial (Fin (e + 1) × Fin n) K) (δ : ℕ),
      ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1)) P δ =
        ReciprocityTheory.ChartRestriction.G.Geo.chowHt (fun w => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1)) P δ +
          (∑ w : InfinitePlace K, (w.mult : ℝ) *
            (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
                (map w.embedding P) -
              ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
                (map w.embedding P))) / Height.totalWeight K := by
    intro P δ
    rw [← chowHt_sub]
    ring
  have hterm : ∀ w : InfinitePlace K,
      (w.mult : ℝ) *
          (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
              (map w.embedding (f * g)) -
            ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
              (map w.embedding (f * g))) =
        (w.mult : ℝ) *
            (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
                (map w.embedding f) -
              ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
                (map w.embedding f)) +
          (w.mult : ℝ) *
            (ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (S w) (e + 1))
                (map w.embedding g) -
              ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw (T w) (e + 1))
                (map w.embedding g)) := by
    intro w
    by_cases hw : w.IsReal
    · have hm := meanShift_mul hA w.embedding (InfinitePlace.isReal_iff.mp hw) (S w) (hS w) f g hf hg
      simp only [T, if_pos hw]
      unfold meanShift at hm
      rw [hm]
      ring
    · simp only [T, if_neg hw, sub_self, mul_zero, add_zero]
  rw [hsplit (f * g), hsplit f, hsplit g, additive_of_conjInv hA T hT hTr f g δ₁ δ₂ hf hg,
    Finset.sum_congr rfl fun w _ => hterm w, Finset.sum_add_distrib]
  ring

theorem cycle_of_A (hA : ChowHeightMul.Statement) : IndefiniteRowSideFullHecke.ArithBezout.ChowHeightCycle.Statement := by
  intro K _ _ n e S hS ι Z f δ hf
  exact cycle_of_mul _ (fun f g δ₁ δ₂ hf hg => additive hA S hS f g δ₁ δ₂ hf hg) Z f δ hf

end ChowHeightCycleEq

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt)

namespace SectionChowHeight

variable {n : ℕ}

theorem logMean_C (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (k : ℕ) (z : ℂ) :
    ReciprocityTheory.ChartRestriction.G.Geo.logMean (IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (k + 1))
      (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ) = Real.log ‖z‖ := by
  have h := ObjectsHeight.mahler_eq_chowMean S hS (ObjectsHeight.ofPointMatrix S hS)
    (ObjectsHeight.ofPointMatrix_norm S hS) (C z : MvPolynomial (Fin (k + 1) × Fin n) ℂ)
  rw [mahler_C] at h
  exact h.symm

theorem chowHeight_C (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (e : ℕ) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0 = 0 := by
  have hsub := ChowHeightCycleEq.chowHt_sub (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw S (e + 1))
    (fun _ => IndefiniteRowSideFullHecke.ArithBezout.formSphereLaw 1 (e + 1)) (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) 0
  simp only [map_C, logMean_C S hS, logMean_C 1 isUnit_one, sub_self, mul_zero,
    Finset.sum_const_zero, zero_div] at hsub
  have hstd : ∀ (σ : ℚ →+* ℂ) (v : Fin n → ℂ),
      ((ArchData.std ℚ n).normAt σ).norm v = IndefiniteRowSideFullHecke.ArithBezout.formNorm 1 v := fun σ v => by
    simp only [ArchData.std]
    rw [ObjectsHeight.std_eq_ofPointMatrix_one, ObjectsHeight.ofPointMatrix_norm]
  have h1 := ObjectsHeight.chowHt_eq_chowHeight (ArchData.std ℚ n) 1 isUnit_one hstd
    (C a : MvPolynomial (Fin (e + 1) × Fin n) ℚ) (δ := 0)
  rw [chowHeightConst ℚ n (e + 1) _ a ha] at h1
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h1 ⊢
  linarith

theorem chowHeight_C_mul_cycle (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) {e : ℕ} {ι : Type}
    (Z : ι →₀ ℕ) (g : ι → MvPolynomial (Fin (e + 1) × Fin n) ℚ) (d : ι → ℕ)
    (hg : ∀ i ∈ Z.support, g i ≠ 0) {a : ℚ} (ha : a ≠ 0) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (C a * ∏ i ∈ Z.support, g i ^ Z i) (∑ i ∈ Z.support, Z i * d i) =
      ∑ i ∈ Z.support, (Z i : ℝ) * IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g i) (d i) := by
  have hMul : ChowHeightMul.Statement := chowHeightMul_of_mahlerMul mahlerMul
  have hne : ∏ i ∈ Z.support, g i ^ Z i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hg i hi)
  have hadd := ChowHeightCycleEq.additive hMul (fun _ : InfinitePlace ℚ => S) (fun _ => hS)
    (C a) (∏ i ∈ Z.support, g i ^ Z i) 0 (∑ i ∈ Z.support, Z i * d i) (C_ne_zero.mpr ha) hne
  have hcyc := ChowHeightCycleEq.cycle_of_A hMul ℚ n e (fun _ => S) (fun _ => hS) ι Z g d hg
  rw [zero_add] at hadd
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight
  rw [hadd]
  have h0 := chowHeight_C S hS e ha
  unfold IndefiniteRowSideFullHecke.ArithBezout.chowHeight at h0
  rw [h0, zero_add]
  exact hcyc

end SectionChowHeight

open Classical in

theorem SectionChowHeight.proof (hSec : ChowFormSection.Statement) : SectionChowHeight.Statement := by
  intro n e δ S P f u g d hS hP hf hu hg
  set s := IndefiniteRowSideFullHecke.ArithBezout.linForm u
  have hcyc : IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) (e + 1)
      (specFirst f fun j => (u j : ℚ)) :=
    hSec ℚ n (e + 1) (ObjectsChow.genericIdeal P) f _
      (VerticalPartGauss.isProjPrime_genericIdeal hP) (VerticalPartGauss.isChowForm_genericIdeal hP hf)
      (VerticalPartGauss.linForm_not_mem_genericIdeal hP hu)
  set Zh := (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).filter IsHorizontal with hZh
  have hmem : ∀ W ∈ Zh.support, W ∈ divSupp P s ∧ IsHorizontal W := by
    intro W hW
    rw [hZh, Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff,
      RecQOfRecursion.divCycle_apply] at hW
    exact ⟨by_contra fun h => hW.1 (if_neg h), hW.2⟩
  have hgA : ∀ W ∈ Zh.support, IsChowForm (ObjectsChow.genericIdeal W) (e + 1) (g W) := fun W hW =>
    VerticalPartGauss.isChowForm_genericIdeal
      (ObjectsChow.DivSuppHorizontalArithVar.proof n (e + 1) P u W hP hu (hmem W hW).1 (hmem W hW).2)
      (hg W (hmem W hW).1 (hmem W hW).2)
  have hsfne := RecQOfRecursion.ne_zero_of_isChowFormCycle hcyc
  obtain ⟨c, hc, g', hg', hsf⟩ := hcyc
  have hD := ObjectsChow.DivCycleGeneric.proof n (e + 1) P u hP hu
  rw [hD] at hsf hg'
  have hpos : ∀ W ∈ Zh.support,
      ObjectsChow.genericIdeal W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support := by
    intro W hW
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain, Finsupp.sum_apply]
    have h1 := Finset.single_le_sum (f := fun a => Finsupp.single (ObjectsChow.genericIdeal a) (Zh a)
      (ObjectsChow.genericIdeal W)) (fun _ _ => Nat.zero_le _) hW
    simp only [Finsupp.single_eq_same] at h1
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)) h1).ne'
  have hr : ∀ W ∈ Zh.support, ∃ r : ℚ, r ≠ 0 ∧ g' (ObjectsChow.genericIdeal W) = C r * g W :=
    fun W hW => RecQOfRecursion.exists_C_mul_of_isChowForm (hgA W hW) (hg' _ (hpos W hW))
  choose! r hr0 hr using hr
  have hsf' : specFirst f (fun j => (u j : ℚ)) =
      C (c * ∏ W ∈ Zh.support, r W ^ Zh W) * ∏ W ∈ Zh.support, g W ^ Zh W := by
    have hprod : ∏ W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support,
        g' W ^ (Zh.mapDomain ObjectsChow.genericIdeal) W =
          Zh.prod fun W m => g' (ObjectsChow.genericIdeal W) ^ m :=
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    rw [hsf, hprod, Finsupp.prod, Finset.prod_congr rfl (fun W hW =>
      show g' (ObjectsChow.genericIdeal W) ^ Zh W = C (r W ^ Zh W) * g W ^ Zh W by
        rw [hr W hW, mul_pow, map_pow]), Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]
  have hgne : ∀ W ∈ Zh.support, g W ≠ 0 := fun W hW => (hgA W hW).1
  have hgm : ∀ W ∈ Zh.support, IsMultiHomog (d W) (g W) := fun W hW =>
    ObjectsChow.isMultiHomog_of_isChowForm (hg W (hmem W hW).1 (hmem W hW).2)
  have hc' : c * ∏ W ∈ Zh.support, r W ^ Zh W ≠ 0 :=
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hr0 W hW))
  have hδ : δ = ∑ W ∈ Zh.support, Zh W * d W := by
    have h1 : IsMultiHomog δ (specFirst f fun j => (u j : ℚ)) :=
      (ObjectsChow.isMultiHomog_of_isChowForm hf).specFirst _
    have h2 : IsMultiHomog (∑ W ∈ Zh.support, Zh W * d W) (specFirst f fun j => (u j : ℚ)) := by
      rw [hsf']
      unfold IsMultiHomog
      have := (isWeightedHomogeneous_C (groupWeight (e + 1) n) (c * ∏ W ∈ Zh.support, r W ^ Zh W)).mul
        (IsWeightedHomogeneous.prod Zh.support (fun W => g W ^ Zh W)
          (fun W => Zh W • fun _ : Fin (e + 1) => d W) fun W hW => (hgm W hW).pow (Zh W))
      convert this using 1
      funext i
      simp [Finset.sum_apply]
    exact congrFun (IsWeightedHomogeneous.inj_right hsfne h1 h2) 0
  rw [← ObjectsChow.specFirst_eq, hsf', hδ,
    SectionChowHeight.chowHeight_C_mul_cycle S hS Zh g d hgne hc']
  rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
  refine (Finset.sum_subset (fun W hW => (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mpr
    (hmem W hW).1) ?_).trans (Finset.sum_congr rfl fun W hW => ?_)
  · intro W _ hW
    rw [Finsupp.mem_support_iff, not_not] at hW
    rw [hW, Nat.cast_zero, zero_mul]
  · have hWd : W ∈ divSupp P s := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mp hW
    rw [hZh, Finsupp.filter_apply, RecQOfRecursion.divCycle_apply, if_pos hWd]
    split_ifs <;> simp

end GroundTheory.Heights₂.Heights
end
end
