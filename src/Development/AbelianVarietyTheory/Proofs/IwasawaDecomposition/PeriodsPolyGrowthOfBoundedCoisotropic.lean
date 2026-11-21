import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodMatrixPolynomialGrowthPuncturedPolydiscStatement

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Module

theorem exists_lagrangian_dual_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  classical
  intro r M W hskew hdet hW
  set B : LinearMap.BilinForm ℝ (Fin r → ℝ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hrefl : B.IsRefl := fun x y h => by rw [hskewB, h, neg_zero]
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℝ (Fin r → ℝ), L ≤ W ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℝ L = n
  have P0 : P 0 := ⟨⊥, bot_le, by simp, finrank_bot ℝ _⟩
  obtain ⟨L, hLW, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hmax : ∀ v ∈ W, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvW hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℝ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℝ {v}, ∀ y ∈ L ⊔ Submodule.span ℝ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add, map_smul, h1, h2, h3, h4]
    have hle : L ⊔ Submodule.span ℝ {v} ≤ W :=
      sup_le hLW (by rw [Submodule.span_le]; simpa using hvW)
    have hP : P (finrank ℝ ↥(L ⊔ Submodule.span ℝ {v})) := ⟨_, hle, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℝ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hWo : B.orthogonal W ≤ L := by
    intro x hx
    have hxW : x ∈ W := hW x (fun w hw => by rw [← hB, hskewB, hx w hw, neg_zero])
    exact hmax x hxW (fun l hl => by rw [hskewB, hx l (hLW hl), neg_zero])
  let b := Module.finBasis ℝ L
  let e : Fin (finrank ℝ L) → Fin r → ℝ := fun i => ((b i : L) : Fin r → ℝ)
  have heL : ∀ i, e i ∈ L := fun i => (b i).2
  have hext : ∀ (φ : (Fin r → ℝ) →ₗ[ℝ] ℝ), (∀ j, φ (e j) = 0) → ∀ l ∈ L, φ l = 0 := by
    intro φ hφ l hl
    have : φ ∘ₗ L.subtype = 0 := b.ext (fun j => by simpa using hφ j)
    simpa using LinearMap.congr_fun this ⟨l, hl⟩
  let φ : (Fin r → ℝ) →ₗ[ℝ] (Fin (finrank ℝ L) → ℝ) := LinearMap.pi (fun j => B.flip (e j))
  have hφ : ∀ v j, φ v j = B v (e j) := fun v j => rfl
  have hker : LinearMap.ker φ = B.orthogonal L := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h l hl
      have h' := hext (B v) (fun j => by rw [← hφ, h]; rfl) l hl
      rw [hskewB, h', neg_zero]
    · intro h
      funext j
      rw [Pi.zero_apply, hφ, hskewB, h _ (heL j), neg_zero]
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    have h2 : finrank ℝ L ≤ r := by simpa using Submodule.finrank_le L
    simp only [Module.finrank_fin_fun] at h1 ⊢
    omega
  have hsurj : ∀ y, ∃ x, φ x = y := fun y => by
    have : y ∈ LinearMap.range φ := by rw [hrange]; trivial
    exact this
  choose f hf using fun i : Fin (finrank ℝ L) => hsurj (Pi.single i 1)
  have hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hφ, hf i, Pi.single_apply]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  refine ⟨finrank ℝ L, e, f, fun i => hLW (heL i),
    fun i j => by rw [← hB]; exact hLiso _ (heL i) _ (heL j),
    fun i j => by rw [← hB]; exact hfe i j, ?_⟩
  set U := Submodule.span ℝ (Set.range (Sum.elim e f)) with hU
  have hUo : B.orthogonal U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hve : ∀ j, B (e j) v = 0 := fun j => hv _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    have hvf : ∀ i, B (f i) v = 0 := fun i => hv _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
    have hvL : ∀ l ∈ L, B v l = 0 := hext (B v) (fun j => by rw [hskewB, hve j, neg_zero])
    have hvW : v ∈ W := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
      intro x hx
      rw [hskewB, hvL x (hWo hx), neg_zero]
    have hvL' : v ∈ L := hmax v hvW hvL
    have hv' : v = ∑ j, b.repr ⟨v, hvL'⟩ j • e j := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hvL'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hc : ∀ i, b.repr ⟨v, hvL'⟩ i = 0 := by
      intro i
      have h := hvf i
      rw [hv', map_sum] at h
      simpa [map_smul, hfe] using h
    have h0 : (⟨v, hvL'⟩ : L) = 0 := b.repr.injective (by ext i; simp [hc])
    simpa using congrArg Subtype.val h0
  have hdimU := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [hUo, finrank_bot] at hdimU
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le U
  simp only [Module.finrank_fin_fun] at hdimU this ⊢
  omega

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  first | exact @GlobalTheory.exists_lagrangian_dual_in_coisotropic | exact GlobalTheory.exists_lagrangian_dual_in_coisotropic | (intros; apply GlobalTheory.exists_lagrangian_dual_in_coisotropic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_periods_alternating_nondeg_rank_eq_two_mul : ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  first | exact @GlobalTheory.hermForm_periods_alternating_nondeg | exact GlobalTheory.hermForm_periods_alternating_nondeg | (intros; apply GlobalTheory.hermForm_periods_alternating_nondeg <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.familyIsotropicDual_linearIndependent_and_card : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  intro r d M e f hiso hdual hspan
  have hli : LinearIndependent ℝ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hb : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg
      simpa [add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual] using h
    have ha : ∀ k, g (Sum.inl k) = 0 := by
      intro k
      have hg' : ∑ i, g (Sum.inl i) • e i = 0 := by simpa [hb] using hg
      have h := congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual] using h
    rintro (k | k)
    · exact ha k
    · exact hb k
  refine ⟨hli, ?_⟩
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
  omega
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  first | exact @GlobalTheory.familyIsotropicDual_linearIndependent_and_card | exact GlobalTheory.familyIsotropicDual_linearIndependent_and_card | (intros; apply GlobalTheory.familyIsotropicDual_linearIndependent_and_card <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem det_ne_zero_of_real_indep_isotropic : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  intro g Hm E hpos hind him
  have hL : ∀ (a : Fin g → ℝ) (w : Fin g → ℂ), hermForm Hm (∑ i, (a i : ℂ) • E i) w
      = ∑ i, (a i : ℂ) * hermForm Hm (E i) w := by
    intro a w
    simp only [hermForm, sum_dotProduct, smul_dotProduct, smul_eq_mul]
  have hR : ∀ (b : Fin g → ℝ) (z : Fin g → ℂ), hermForm Hm z (∑ j, (b j : ℂ) • E j)
      = ∑ j, (b j : ℂ) * hermForm Hm z (E j) := by
    intro b z
    have hs : star (∑ j, (b j : ℂ) • E j) = ∑ j, (b j : ℂ) • star (E j) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext k
      simp
    simp only [hermForm, hs, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul]
  have him0 : ∀ a b : Fin g → ℝ,
      (hermForm Hm (∑ i, (a i : ℂ) • E i) (∑ j, (b j : ℂ) • E j)).im = 0 := by
    intro a b
    rw [hL]
    simp only [hR, Finset.mul_sum, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    simp [Complex.mul_im, him i j]
  have hsmulL : ∀ (c : ℂ) (z w : Fin g → ℂ), hermForm Hm (c • z) w = c * hermForm Hm z w := by
    intro c z w
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have hreal : ∀ a : Fin g → ℝ, (∑ i, (a i : ℂ) • E i) = 0 → a = 0 := by
    intro a h0
    have h1 : ∑ i, a i • E i = 0 := by
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      simp
    have := Fintype.linearIndependent_iff.mp hind a h1
    funext i
    exact this i
  have hC : LinearIndependent ℂ E := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hsplit : (∑ i, (((c i).re : ℝ) : ℂ) • E i) + Complex.I • (∑ i, (((c i).im : ℝ) : ℂ) • E i) = 0 := by
      rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← add_smul]
      congr 1
      exact (mul_comm Complex.I _ ▸ Complex.re_add_im (c i))
    set X := ∑ i, (((c i).re : ℝ) : ℂ) • E i with hX
    set Y := ∑ i, (((c i).im : ℝ) : ℂ) • E i with hY
    have hXY : X = (-Complex.I) • Y := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left hsplit
    have hY0 : Y = 0 := by
      by_contra hne
      have hp := hpos Y hne
      have h2 := him0 (fun i => (c i).re) (fun i => (c i).im)
      change (hermForm Hm X Y).im = 0 at h2
      rw [hXY, hsmulL] at h2
      simp [Complex.mul_im] at h2
      linarith
    have hX0 : X = 0 := by rw [hXY, hY0, smul_zero]
    have hre := hreal (fun i => (c i).re) hX0
    have him' := hreal (fun i => (c i).im) hY0
    intro i
    apply Complex.ext
    · simpa using congrFun hre i
    · simpa using congrFun him' i
  have hcol : LinearIndependent ℂ (Matrix.of fun k i => E i k : Matrix (Fin g) (Fin g) ℂ).col := hC
  have hu := Matrix.linearIndependent_cols_iff_isUnit.mp hcol
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

end GlobalTheory
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_ne_zero_of_real_independent_isotropic_hermitian : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E : Fin g → Fin g → ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → LinearIndependent ℝ E → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (Matrix.of fun k i => E i k).det ≠ 0 := by
  first | exact @GlobalTheory.det_ne_zero_of_real_indep_isotropic | exact GlobalTheory.det_ne_zero_of_real_indep_isotropic | (intros; apply GlobalTheory.det_ne_zero_of_real_indep_isotropic <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.riemann_relations_period_matrix : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  intro g d Hm E F τ hH hpos hF hA hFE
  have hexp : ∀ z w : Fin g → ℂ, hermForm Hm z w = ∑ x, ∑ y, z x * Hm x y * star (w y) := by
    intro z w; unfold hermForm; simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [Pi.star_apply]; ring
  have lin1 : ∀ (c : Fin d → ℂ) (w : Fin g → ℂ),
      hermForm Hm (∑ i, c i • E i) w = ∑ i, c i * hermForm Hm (E i) w := by
    intro c w
    unfold hermForm
    rw [sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
  have symm : ∀ z w : Fin g → ℂ, hermForm Hm w z = star (hermForm Hm z w) := by
    intro z w
    simp only [hexp, star_sum, star_mul', star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [show star (Hm x y) = Hm y x from hH.apply y x]; ring
  have lin2 : ∀ (c : Fin d → ℂ) (z : Fin g → ℂ),
      hermForm Hm z (∑ i, c i • E i) = ∑ i, star (c i) * hermForm Hm z (E i) := by
    intro c z
    rw [symm, lin1, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', ← symm]
  set a : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => (hermForm Hm (E i) (E k)).re with ha
  have hAr : ∀ i k, hermForm Hm (E i) (E k) = (a i k : ℂ) := fun i k =>
    Complex.ext (by simp [a]) (by simp [a, hA])
  have asymm : aᵀ = a := by
    ext i k; simp only [a, Matrix.transpose_apply, Matrix.of_apply]; rw [symm]; simp
  set Y : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).im with hY
  set X : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j => (τ i j).re with hX
  have hYA : Yᵀ * a = 1 := by
    ext j k
    have h := hFE j k
    rw [hF j, lin1] at h
    simp only [hAr, Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, add_zero] at h
    simpa [Matrix.mul_apply, Matrix.one_apply, Y] using h
  have hAY : a * Y = 1 := by
    have h := congrArg Matrix.transpose hYA
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, asymm, Matrix.transpose_one] at h
  have hYs : Yᵀ = Y := by
    calc Yᵀ = Yᵀ * (a * Y) := by rw [hAY, Matrix.mul_one]
    _ = (Yᵀ * a) * Y := by rw [Matrix.mul_assoc]
    _ = Y := by rw [hYA, Matrix.one_mul]
  have e1 : ∀ i m, ∑ p, Y p i * a p m = if i = m then 1 else 0 := fun i m => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hYA i) m
  have e2 : ∀ p j, ∑ m, a p m * Y m j = if p = j then 1 else 0 := fun p j => by
    simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun hAY p) j
  have ys : ∀ i j, Y i j = Y j i := fun i j => by
    simpa using (congrFun (congrFun hYs j) i)
  refine ⟨fun v hv => ?_, fun i j => ?_⟩
  · have him : (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im = v ⬝ᵥ (Y *ᵥ v) := by
      simp only [Complex.im_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Y, Complex.mul_im]; ring
    rw [him]
    set w := Y *ᵥ v with hw
    have hAw : a *ᵥ w = v := by rw [hw, Matrix.mulVec_mulVec, hAY, Matrix.one_mulVec]
    set Q : Fin g → ℂ := ∑ i, ((w i : ℝ) : ℂ) • E i with hQ
    have hQE : ∀ k, (hermForm Hm Q (E k)).re = v k := by
      intro k
      rw [hQ, lin1, ← hAw]
      simp only [hAr, Complex.re_sum, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Complex.mul_re]
      rw [show a k i = a i k from by simpa using congrFun (congrFun asymm i) k]; ring
    have hQQ : (hermForm Hm Q Q).re = v ⬝ᵥ w := by
      have hl := lin2 (fun i => (w i : ℂ)) Q
      rw [← hQ] at hl
      rw [hl]
      simp only [Complex.re_sum, dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hQE k]; simp [Complex.mul_re]; ring
    have hQ0 : Q ≠ 0 := by
      intro h; apply hv; funext k; rw [← hQE k, h]; simp [hermForm]
    rw [← hQQ]; exact hpos Q hQ0
  · have key : (hermForm Hm (F i) (F j)).im = X i j - X j i := by
      rw [hF i, lin1]
      simp only [hF j, lin2, hAr, Complex.im_sum, Finset.mul_sum]
      have h1 : ∀ p m, ((τ p i) * (star (τ m j) * (a p m : ℂ))).im
          = Y p i * a p m * X m j - X p i * (a p m * Y m j) := fun p m => by
        simp [Y, X, Complex.mul_im, Complex.mul_re]; ring
      simp only [h1, Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, ← Finset.mul_sum, e1, e2]
      simp [X]
    apply Complex.ext
    · simp [key, X]
    · simp [Y] at ys; simp [ys j i]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemann_relations_period_matrix_hermitian : ∀ (g d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (E F : Fin d → Fin g → ℂ) (τ : Fin d → Fin d → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ j, F j = ∑ i, τ i j • E i) → (∀ i j, (hermForm Hm (E i) (E j)).im = 0) → (∀ i j, (hermForm Hm (F i) (E j)).im = if i = j then 1 else 0) → (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ i j * (v j : ℂ)).im) ∧ ∀ i j, τ i j - τ j i = ((hermForm Hm (F i) (F j)).im : ℂ) := by
  first | exact @GlobalTheory.riemann_relations_period_matrix | exact GlobalTheory.riemann_relations_period_matrix | (intros; apply GlobalTheory.riemann_relations_period_matrix <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.hermForm_im_real_comb (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ i j, (hermForm Hm (x i) (x j)).im = M i j) (u v : Fin r → ℝ) :
    (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  have key : hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)
      = ∑ m, ∑ m', ((u m * v m' : ℝ) : ℂ) * hermForm Hm (x m) (x m') := by
    simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct,
      dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
    push_cast
    ring
  rw [key]
  simp only [Complex.im_sum, Complex.im_ofReal_mul, h, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => ?_
  ring
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct : ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → ∀ u v : Fin r → ℝ, (hermForm Hm (∑ m, (u m : ℂ) • x m) (∑ m, (v m : ℂ) • x m)).im = u ⬝ᵥ M *ᵥ v := by
  atlas_forward_decl GlobalTheory.hermForm_im_real_comb
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linearIndependent_real_combination (g r d : ℕ) (x : Fin r → Fin g → ℂ)
    (e : Fin d → Fin r → ℝ) (hx : LinearIndependent ℝ x) (he : LinearIndependent ℝ e) :
    LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  rw [Fintype.linearIndependent_iff] at hx he ⊢
  intro c hc
  have hreal : ∀ i, (∑ m, (e i m : ℂ) • x m) = ∑ m, e i m • x m := by
    intro i
    refine Finset.sum_congr rfl fun m _ => ?_
    funext k
    simp [Pi.smul_apply, Complex.real_smul]
  have h1 : ∑ m, (∑ i, c i * e i m) • x m = 0 := by
    have h0 : ∑ i, c i • ∑ m, e i m • x m = 0 := by
      simpa only [hreal] using hc
    rw [← h0]
    simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 := hx _ h1
  refine he c ?_
  funext m
  simpa [Finset.sum_apply, Pi.smul_apply] using h2 m

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_real_combinations_of_independent : ∀ (g r d : ℕ) (x : Fin r → Fin g → ℂ) (e : Fin d → Fin r → ℝ), LinearIndependent ℝ x → LinearIndependent ℝ e → LinearIndependent ℝ (fun i => ∑ m, (e i m : ℂ) • x m) := by
  atlas_forward_decl GlobalTheory.linearIndependent_real_combination
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem growth_bound_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g r J _ R x u hspan hb
  choose C k hC using hb
  have hsingle : ∀ m : Fin r, ∃ a : J → ℝ, ∑ i, a i • u i = Pi.single m 1 := by
    intro m
    have hmem : (Pi.single m (1:ℝ) : Fin r → ℝ) ∈ Submodule.span ℝ (Set.range u) := by
      rw [hspan]; trivial
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
  choose a ha using hsingle
  refine ⟨∑ m, ∑ i, |a m i| * max (C i) 0, ∑ i, k i, ?_⟩
  intro s hs
  have h1 : (1:ℝ) ≤ 1 + ‖s‖ := by linarith [norm_nonneg s]
  have hpow : ∀ i, (1 + ‖s‖) ^ (k i) ≤ (1 + ‖s‖) ^ (∑ j, k j) := fun i =>
    pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i))
  have hm : ∀ m, ‖x s m‖ ≤ (∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
    intro m
    have hid : x s m = ∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m' := by
      have e := congrFun (ha m)
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have hc : ∀ m', ∑ i, ((a m i : ℂ) * (u i m' : ℂ)) • x s m'
          = (((Pi.single m (1:ℝ) : Fin r → ℝ) m' : ℝ) : ℂ) • x s m' := by
        intro m'
        rw [← Finset.sum_smul]
        congr 1
        have h2 := e m'
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
        rw [← h2]; push_cast; rfl
      rw [Finset.sum_congr rfl (fun m' _ => hc m')]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb; simp [Pi.single_apply, hb]
      · intro h; exact absurd (Finset.mem_univ m) h
    rw [hid]
    calc ‖∑ i, (a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖
        ≤ ∑ i, ‖(a m i : ℂ) • ∑ m', (u i m' : ℂ) • x s m'‖ := norm_sum_le _ _
      _ ≤ ∑ i, |a m i| * (max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j)) := by
        apply Finset.sum_le_sum; intro i _
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        calc _ ≤ C i * (1 + ‖s‖) ^ (k i) := hC i s hs
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (k i) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
          _ ≤ max (C i) 0 * (1 + ‖s‖) ^ (∑ j, k j) :=
              mul_le_mul_of_nonneg_left (hpow i) (le_max_right _ _)
      _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (_root_.mul_assoc _ _ _).symm
  have hnn : ∀ m, 0 ≤ ∑ i, |a m i| * max (C i) 0 := fun m =>
    Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (le_max_right _ _)
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun m _ => hnn m) (by positivity))).2 fun m => ?_
  calc ‖x s m‖ ≤ _ := hm m
    _ ≤ (∑ m, ∑ i, |a m i| * max (C i) 0) * (1 + ‖s‖) ^ (∑ j, k j) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum (f := fun m => ∑ i, |a m i| * max (C i) 0)
        (fun j _ => hnn j) (Finset.mem_univ m)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_growth_of_spanning_combinations : ∀ (n g r : ℕ) (J : Type) [Fintype J] (R : Set (Fin n → ℂ)) (x : (Fin n → ℂ) → Fin r → Fin g → ℂ) (u : J → Fin r → ℝ), Submodule.span ℝ (Set.range u) = ⊤ → (∀ i, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ m, (u i m : ℂ) • x s m‖ ≤ C * (1 + ‖s‖) ^ k) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖x s‖ ≤ C * (1 + ‖s‖) ^ k := by
  atlas_forward_decl GlobalTheory.growth_bound_of_spanning_combinations
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem matrix_mul_bounded_poly_growth : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n g d R τ E ⟨C, k, hC⟩ hE j
  choose C' hC' using hE
  refine ⟨max C 0 * ∑ i, max (C' i) 0, k, fun s hs => ?_⟩
  have hp : (0:ℝ) ≤ (1 + ‖s‖) ^ k := pow_nonneg (by positivity) _
  have h1 : ∀ i, ‖τ s i j‖ ≤ max C 0 * (1 + ‖s‖) ^ k := fun i =>
    (norm_le_pi_norm (τ s i) j).trans ((norm_le_pi_norm (τ s) i).trans
      ((hC s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)))
  calc ‖∑ i, τ s i j • E s i‖ ≤ ∑ i, ‖τ s i j • E s i‖ := norm_sum_le _ _
    _ = ∑ i, ‖τ s i j‖ * ‖E s i‖ := by simp only [norm_smul]
    _ ≤ ∑ i, (max C 0 * (1 + ‖s‖) ^ k) * max (C' i) 0 :=
        Finset.sum_le_sum fun i _ => mul_le_mul (h1 i) (le_max_of_le_left (hC' i s hs))
          (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp)
    _ = max C 0 * (∑ i, max (C' i) 0) * (1 + ‖s‖) ^ k := by rw [← Finset.mul_sum]; ring

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors : ∀ (n g d : ℕ) (R : Set (Fin n → ℂ)) (τ : (Fin n → ℂ) → Fin d → Fin d → ℂ) (E : (Fin n → ℂ) → Fin d → Fin g → ℂ), (∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖τ s‖ ≤ C * (1 + ‖s‖) ^ k) → (∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C) → ∀ j, ∃ (C : ℝ) (k : ℕ), ∀ s ∈ R, ‖∑ i, τ s i j • E s i‖ ≤ C * (1 + ‖s‖) ^ k := by
  atlas_forward_decl GlobalTheory.matrix_mul_bounded_poly_growth
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerGrowth

theorem differentiableOn_matrix_det_of_entries_normedSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B) :
    DifferentiableOn ℂ (fun b => (A b).det) B := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => DifferentiableOn.const_mul ?_ _
  have key : ∀ t : Finset (Fin d), DifferentiableOn ℂ (fun b => ∏ i ∈ t, A b (σ i) i) B := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hA _ _).mul ih
  exact key _

theorem differentiableOn_matrix_inv_apply_of_entries {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V} {d : ℕ}
    {A : V → Matrix (Fin d) (Fin d) ℂ} (hA : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B)
    (hd : ∀ b ∈ B, (A b).det ≠ 0) (i j : Fin d) :
    DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) B := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  refine ((differentiableOn_matrix_det_of_entries_normedSpace hA).inv hd).mul (differentiableOn_matrix_det_of_entries_normedSpace fun a b => ?_)
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact differentiableOn_const _
  · exact hA _ _

theorem lam_polyGrowth_of_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  intro n a g r lam M W hd hs hW hb
  by_cases hne : (logDom n a).Nonempty
  swap
  · exact ⟨0, 0, fun s hs' => absurd ⟨s, hs'⟩ hne⟩
  obtain ⟨s0, hs0⟩ := hne
  obtain ⟨hli0, hsp0, Hm0, hH0, hP0, hM0⟩ := hs s0 hs0
  obtain ⟨hMa, hMd, hr⟩ := GlobalTheory.T.hermForm_periods_alternating_nondeg_rank_eq_two_mul g r (lam s0) M Hm0 hli0 hsp0 hH0 hP0 hM0
  obtain ⟨d, e, f, heW, hee, hfe, hsp⟩ := GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic r M W hMa hMd hW
  obtain ⟨hli, hrd⟩ := GlobalTheory.T.isotropicDual_family_linearIndependent_rank_eq_two_mul r d M e f hee hfe hsp
  obtain rfl : d = g := by omega
  obtain ⟨E, hE⟩ : ∃ E : (Fin n → ℂ) → Fin d → Fin d → ℂ, E = fun s i => ∑ m, (e i m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℂ) → Fin d → Fin d → ℂ, F = fun s j => ∑ m, (f j m : ℂ) • lam s m := ⟨_, rfl⟩
  obtain ⟨Em, hEm⟩ : ∃ Em : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Em = fun s => Matrix.of fun k i => E s i k :=
    ⟨_, rfl⟩
  obtain ⟨Fm, hFm⟩ : ∃ Fm : (Fin n → ℂ) → Matrix (Fin d) (Fin d) ℂ, Fm = fun s => Matrix.of fun k j => F s j k :=
    ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : (Fin n → ℂ) → Fin d → Fin d → ℂ, τ = fun s i j => ((Em s)⁻¹ * Fm s) i j := ⟨_, rfl⟩
  have hlinE : LinearIndependent ℝ e := hli.comp Sum.inl Sum.inl_injective

  have hpt : ∀ s ∈ logDom n a, (Em s).det ≠ 0 ∧ (∀ j, F s j = ∑ i, τ s i j • E s i) ∧
      (∀ v : Fin d → ℝ, v ≠ 0 → 0 < (∑ i, ∑ j, (v i : ℂ) * τ s i j * (v j : ℂ)).im) ∧
      ∀ i j, τ s i j - τ s j i = ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ) := by
    intro s hs'
    obtain ⟨hli1, -, Hm, hH, hP, hMs⟩ := hs s hs'
    have h6 := GlobalTheory.T.hermForm_im_real_combination_eq_dotProduct d r (lam s) M Hm hMs
    have hEE : ∀ i j, (hermForm Hm (E s i) (E s j)).im = 0 := fun i j => by
      rw [hE]; exact (h6 _ _).trans (hee i j)
    have hFE : ∀ i j, (hermForm Hm (F s i) (E s j)).im = if i = j then 1 else 0 := fun i j => by
      rw [hE, hF]; exact (h6 _ _).trans (hfe i j)
    have hFF : ∀ i j, (hermForm Hm (F s i) (F s j)).im = f i ⬝ᵥ M *ᵥ f j := fun i j => by
      rw [hF]; exact h6 _ _
    have hEli : LinearIndependent ℝ (E s) := by
      rw [hE]; exact GlobalTheory.T.linearIndependent_real_combinations_of_independent d r d (lam s) e hli1 hlinE
    have hdet : (Em s).det ≠ 0 := by rw [hEm]; exact GlobalTheory.T.det_ne_zero_of_real_independent_isotropic_hermitian d Hm (E s) hP hEli hEE
    have hFt : ∀ j, F s j = ∑ i, τ s i j • E s i := by
      intro j
      have hm := Matrix.mul_nonsing_inv_cancel_left (Em s) (Fm s) (Ne.isUnit hdet)
      funext k
      have := congrFun (congrFun hm k) j
      have hEmk : ∀ k i, Em s k i = E s i k := fun k i => by simp [hEm]
      have hFmk : ∀ k i, Fm s k i = F s i k := fun k i => by simp [hFm]
      rw [Matrix.mul_apply] at this
      simp only [hEmk, hFmk] at this
      rw [hτ]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    obtain ⟨h4a, h4b⟩ := GlobalTheory.T.riemann_relations_period_matrix_hermitian d d Hm (E s) (F s) (τ s) hH hP hFt hEE hFE
    exact ⟨hdet, hFt, h4a, fun i j => (h4b i j).trans (by rw [hFF])⟩

  have hlam : ∀ m k, DifferentiableOn ℂ (fun s => lam s m k) (logDom n a) := fun m k =>
    differentiableOn_pi.1 (differentiableOn_pi.1 hd m) k
  have hEmd : ∀ k i, DifferentiableOn ℂ (fun s => Em s k i) (logDom n a) := fun k i => by
    simp only [hEm, hE, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hFmd : ∀ k i, DifferentiableOn ℂ (fun s => Fm s k i) (logDom n a) := fun k i => by
    simp only [hFm, hF, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact DifferentiableOn.fun_sum fun m _ => (hlam m k).const_mul _
  have hτd : DifferentiableOn ℂ τ (logDom n a) := by
    refine differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => ?_
    simp only [hτ, Matrix.mul_apply]
    exact DifferentiableOn.fun_sum fun l _ =>
      (differentiableOn_matrix_inv_apply_of_entries hEmd (fun s hs' => (hpt s hs').1) i l).mul (hFmd l j)
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.periodMatrix_polynomialGrowth_puncturedPolydisc n a d τ (fun i j => ((f i ⬝ᵥ M *ᵥ f j : ℝ) : ℂ)) hτd (fun s hs' => (hpt s hs').2.2.1)
    (fun s hs' => (hpt s hs').2.2.2)
  set R : Set (Fin n → ℂ) := {s | s ∈ logDom n a ∧ ‖logExp a s‖ ≤ 1 / 2 ∧
    ∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi} with hR
  have hEb : ∀ i, ∃ C : ℝ, ∀ s ∈ R, ‖E s i‖ ≤ C := fun i => by
    obtain ⟨C, hC⟩ := hb (e i) (heW i)
    exact ⟨C, fun s hs' => by rw [hE]; exact hC s hs'.1 hs'.2.1⟩
  have h9 := GlobalTheory.T.polynomial_growth_matrix_mul_bounded_vectors n d d R τ E ⟨C, k, fun s hs' => hC s hs'.1 hs'.2.1 hs'.2.2⟩ hEb
  obtain ⟨C', k', h8⟩ := GlobalTheory.T.polynomial_growth_of_spanning_combinations n d r (Fin d ⊕ Fin d) R lam (Sum.elim e f) hsp (fun i => by
    rcases i with i | j
    · obtain ⟨C, hC⟩ := hEb i
      exact ⟨C, 0, fun s hs' => by simpa [hE] using hC s hs'⟩
    · obtain ⟨C, k, hC⟩ := h9 j
      refine ⟨C, k, fun s hs' => ?_⟩
      have := (hpt s hs'.1).2.1 j
      simp only [hF] at this
      simp only [Sum.elim_inr]
      rw [this]
      exact hC s hs')
  exact ⟨C', k', fun s hs' h1 h2 => h8 s ⟨hs', h1, h2⟩⟩

end GlobalTheory.ShFam.Hor.LogCh.PerGrowth
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_polyGrowth_of_bounded_coisotropic : ∀ (n a g r : ℕ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), DifferentiableOn ℂ lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℝ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → (∀ w ∈ W, ∃ C : ℝ, ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → ‖∑ j, (w j : ℂ) • lam s j‖ ≤ C) → ∃ (C : ℝ) (k : ℕ), ∀ s ∈ logDom n a, ‖logExp a s‖ ≤ 1 / 2 → (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k := by
  atlas_forward_decl GlobalTheory.ShFam.Hor.LogCh.PerGrowth.lam_polyGrowth_of_coisotropic
end
