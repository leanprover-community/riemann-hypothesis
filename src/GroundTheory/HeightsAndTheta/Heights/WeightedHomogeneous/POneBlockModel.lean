import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeModel

variable {K : Type} [Field K] [NumberField K]

theorem isAlgebraic_int (x : K) : IsAlgebraic ℤ x :=
  IsFractionRing.isAlgebraic_iff ℤ ℚ K |>.mpr (.of_finite ℚ x)

theorem exists_int_mul_integral (x : K) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = n * x := by
  obtain ⟨n, s, hn, h⟩ := (isAlgebraic_int x).exists_smul_eq (𝓞 K)
  exact ⟨n, hn, s, by rw [← h, zsmul_eq_mul]⟩

theorem exists_int_smul_mem_latticeDual {m : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} (hL : L.FG)
    (u : Fin m → K) : ∃ n : ℤ, n ≠ 0 ∧ (n : K) • u ∈ latticeDual L := by
  classical
  obtain ⟨s, rfl⟩ := hL
  choose n hn a ha using fun g : Fin m → K ↦ exists_int_mul_integral (u ⬝ᵥ g)
  refine ⟨∏ g ∈ s, n g, Finset.prod_ne_zero_iff.mpr fun g _ ↦ hn g, ?_⟩
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨((∏ g ∈ s.erase x, n g : ℤ) : 𝓞 K) * a x, ?_⟩
    rw [map_mul, map_intCast, ha x, smul_dotProduct, smul_eq_mul, ← Finset.mul_prod_erase s n hx]
    push_cast
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨b + c, by rw [map_add, hb, hc, dotProduct_add]⟩
  | smul c x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨c * b, by rw [map_mul, hb, dotProduct_smul, Algebra.smul_def c]⟩

variable {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)} {φ : Fin (N + 1) → Fin m → K}

theorem mem_dual_iff (hφ : IsDualBasis L φ) (u : Fin m → K) :
    u ∈ latticeDual L ↔ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = u := by
  rw [← Submodule.mem_span_range_iff_exists_fun ℤ, hφ.span_eq, Submodule.restrictScalars_mem]

theorem mem_dual (hφ : IsDualBasis L φ) (b : Fin (N + 1)) : φ b ∈ latticeDual L :=
  (mem_dual_iff hφ _).mpr ⟨Pi.single b 1, by simp [Pi.single_apply]⟩

theorem latticeForm_add (u v : Fin m → K) : latticeForm (u + v) = latticeForm u + latticeForm v := by
  simp [latticeForm, add_mul, Finset.sum_add_distrib]

theorem latticeForm_smul (c : K) (u : Fin m → K) : latticeForm (c • u) = C c * latticeForm u := by
  simp [latticeForm, Finset.mul_sum, mul_assoc]

theorem latticeForm_zero : latticeForm (0 : Fin m → K) = 0 := by
  simp [latticeForm]

theorem latticeForm_zsmul (c : ℤ) (u : Fin m → K) : latticeForm (c • u) = C (c : K) * latticeForm u := by
  rw [← latticeForm_smul]
  congr 1
  ext j
  simp

theorem latticeForm_sum {ι : Type*} (s : Finset ι) (u : ι → Fin m → K) :
    latticeForm (∑ i ∈ s, u i) = ∑ i ∈ s, latticeForm (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [latticeForm_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, latticeForm_add, ih]

theorem coeff_latticeForm (u : Fin m → K) (j : Fin m) :
    coeff (Finsupp.single j 1) (latticeForm u) = u j := by
  simp [latticeForm, coeff_sum, coeff_C_mul, coeff_X, Finsupp.single_left_inj]

theorem latticeForm_eq_zero_iff (u : Fin m → K) : latticeForm u = 0 ↔ u = 0 := by
  refine ⟨fun h ↦ funext fun j ↦ ?_, fun h ↦ h ▸ latticeForm_zero⟩
  rw [← coeff_latticeForm u j, h, coeff_zero, Pi.zero_apply]

theorem isHomogeneous_latticeForm (u : Fin m → K) : (latticeForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ ↦ isHomogeneous_C_mul_X _ _

theorem latticeMap_linear (φ : Fin (N + 1) → Fin m → K) (c : Fin (N + 1) → ℤ) :
    latticeMap φ (∑ b, C (c b) * X ⟨(), b⟩) = latticeForm (∑ b, c b • φ b) := by
  rw [latticeForm_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [latticeForm_zsmul, map_mul]
  simp [latticeMap]

theorem isHomogeneous_latticeMap (φ : Fin (N + 1) → Fin m → K) {f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ}
    {d : ℕ} (hf : f.IsHomogeneous d) : (latticeMap φ f).IsHomogeneous d := by
  have h := hf.eval₂ (Int.castRingHom _) (fun v ↦ latticeForm (φ v.2))
    (fun a ↦ by rw [eq_intCast, ← map_intCast (C : K →+* MvPolynomial (Fin m) K)]; exact isHomogeneous_C _ _)
    (fun v ↦ isHomogeneous_latticeForm _)
  rwa [one_mul] at h

section Degrees

variable {R : Type*} [CommSemiring R]

theorem weight_coordDeg (s : Coord (fun _ : Unit ↦ N) →₀ ℕ) :
    Finsupp.weight (coordDeg fun _ : Unit ↦ N) s = fun _ ↦ s.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finsupp.degree]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp [coordDeg]

theorem weight_one_eq_degree {σ : Type*} (s : σ →₀ ℕ) : Finsupp.weight (1 : σ → ℕ) s = s.degree := by
  rw [Finsupp.degree_eq_weight_one]
  rfl

theorem isWeightedHomogeneous_coordDeg_iff (f : MvPolynomial (Coord fun _ : Unit ↦ N) R) (μ : Unit → ℕ) :
    IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f μ ↔ f.IsHomogeneous (μ ()) := by
  constructor
  · intro h s hs
    have := congrFun (h hs) ()
    rw [weight_coordDeg] at this
    rw [weight_one_eq_degree]
    exact this
  · intro h s hs
    rw [weight_coordDeg]
    funext u
    have := h hs
    rw [weight_one_eq_degree] at this
    exact this

theorem weightedHomogeneousComponent_coordDeg (f : MvPolynomial (Coord fun _ : Unit ↦ N) R) (μ : Unit → ℕ) :
    weightedHomogeneousComponent (coordDeg fun _ : Unit ↦ N) μ f = homogeneousComponent (μ ()) f := by
  classical
  ext s
  rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, weight_coordDeg]
  by_cases h : s.degree = μ ()
  · rw [if_pos (funext fun _ ↦ h), if_pos h]
  · rw [if_neg (fun h' ↦ h (congrFun h' ())), if_neg h]

end Degrees

theorem latticeMap_homogeneousComponent (φ : Fin (N + 1) → Fin m → K)
    (f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) (d : ℕ) :
    latticeMap φ (homogeneousComponent d f) = homogeneousComponent d (latticeMap φ f) := by
  classical
  conv_rhs => rw [← sum_homogeneousComponent f]
  rw [map_sum, map_sum]
  simp_rw [homogeneousComponent_of_mem (isHomogeneous_latticeMap φ (homogeneousComponent_isHomogeneous _ f))]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [Finset.mem_range, not_lt] at h
    rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

def latticeVariety (φ : Fin (N + 1) → Fin m → K) (hφ : IsDualBasis L φ) :
    ArithVariety (fun _ : Unit ↦ N) where
  ideal := latticeIdeal φ
  isPrime := RingHom.ker_isPrime _
  homogeneous f hf μ := by
    rw [weightedHomogeneousComponent_coordDeg]
    refine RingHom.mem_ker.mpr ?_
    rw [latticeMap_homogeneousComponent, RingHom.mem_ker.mp hf, map_zero]
  relevant _ := ⟨0, fun h ↦ hφ.independent.ne_zero 0
    ((latticeForm_eq_zero_iff _).mp (by simpa [latticeMap] using RingHom.mem_ker.mp h))⟩
  horizontal a ha := by simpa [latticeMap] using RingHom.mem_ker.mp ha


variable {r : ℕ}

theorem algebraMap_C (a : K) :
    algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (C a) = algebraMap K (LatticeField K r) a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin r) K) (LatticeField K r), MvPolynomial.algebraMap_eq]

def genericVal (K : Type) [Field K] (r : ℕ) : Fin (r + 1) → LatticeField K r :=
  Fin.cases 1 fun j ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j)

def dehom (K : Type) [Field K] (r : ℕ) : MvPolynomial (Fin (r + 1)) K →+* LatticeField K r :=
  eval₂Hom (algebraMap K (LatticeField K r)) (genericVal K r)

theorem dehom_latticeForm (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) = algebraMap (MvPolynomial (Fin r) K) (LatticeField K r)
      (C (u 0) + ∑ j : Fin r, C (u j.succ) * X j) := by
  simp only [dehom, latticeForm, map_sum, map_mul, map_add, coe_eval₂Hom, eval₂_C, eval₂_X, algebraMap_C,
    Fin.sum_univ_succ, genericVal, Fin.cases_zero, Fin.cases_succ, mul_one]

theorem latticeCoord_eq (φ : Fin (N + 1) → Fin (r + 1) → K) (v : Coord fun _ : Unit ↦ N) :
    latticeCoord φ v = dehom K r (latticeForm (φ v.2)) :=
  (dehom_latticeForm _).symm


theorem mCoordIdeal_latticeCoord (φ : Fin (N + 1) → Fin (r + 1) → K) :
    Geo.mCoordIdeal (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) = latticeIdeal φ := by
  ext f
  rw [Geo.mCoordIdeal, RingHom.mem_ker, latticeIdeal, RingHom.mem_ker]
  constructor
  · intro hf
    have hw : ∀ w : Fin (r + 1) → K, w 0 ≠ 0 → eval w (latticeMap φ f) = 0 := by
      intro w hw0
      let χ : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* MvPolynomial (Fin r) K :=
        eval₂Hom (Int.castRingHom _) fun v ↦ C (w 0) * (C (φ v.2 0) + ∑ j : Fin r, C (φ v.2 j.succ) * X j)
      have h1 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
          eval (fun _ : Unit ↦ algebraMap K (LatticeField K r) (w 0))
            (Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) g) =
          algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (χ g) := by
        intro g
        induction g using MvPolynomial.induction_on with
        | C a => simp [Geo.mConeMap, χ]
        | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
        | mul_X p v hp =>
          rw [map_mul, map_mul, hp, map_mul, map_mul]
          congr 1
          simp only [Geo.mConeMap, aeval_X, map_mul, eval_C, eval_X, χ, coe_eval₂Hom, eval₂_X, algebraMap_C,
            latticeCoord]
          ring
      have h2 : χ f = 0 := by
        apply IsFractionRing.injective (MvPolynomial (Fin r) K) (LatticeField K r)
        rw [map_zero, ← h1, hf, map_zero]
      have h3 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
          eval (fun j : Fin r ↦ w j.succ / w 0) (χ g) = eval w (latticeMap φ g) := by
        intro g
        induction g using MvPolynomial.induction_on with
        | C a => simp [χ, latticeMap]
        | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
        | mul_X p v hp =>
          rw [map_mul, map_mul, hp, map_mul, map_mul]
          congr 1
          simp only [χ, latticeMap, coe_eval₂Hom, eval₂_X, latticeForm, map_mul, map_add, map_sum, eval_C, eval_X,
            Fin.sum_univ_succ]
          rw [mul_add, Finset.mul_sum]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro j _
            field_simp
      rw [← h3, h2, map_zero]
    have hX : (X 0 : MvPolynomial (Fin (r + 1)) K) * latticeMap φ f = 0 := by
      apply MvPolynomial.funext
      intro w
      by_cases h0 : w 0 = 0
      · simp [h0]
      · simp [hw w h0]
    exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)
  · intro hf
    let ψ : MvPolynomial (Fin (r + 1)) K →+* MvPolynomial Unit (LatticeField K r) :=
      eval₂Hom (C.comp (algebraMap K (LatticeField K r))) fun j ↦ C (genericVal K r j) * X ()
    have h1 : ∀ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ,
        Geo.mConeMap (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) g = ψ (latticeMap φ g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C a => simp [Geo.mConeMap, ψ, latticeMap]
      | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
      | mul_X p v hp =>
        rw [map_mul, map_mul, hp, map_mul]
        congr 1
        obtain ⟨⟨⟩, b⟩ := v
        simp only [Geo.mConeMap, aeval_X, latticeCoord_eq, dehom, latticeMap, ψ, coe_eval₂Hom, eval₂_X,
          latticeForm, map_sum, map_mul, eval₂_C, RingHom.comp_apply, Finset.sum_mul, mul_assoc]
    rw [h1, hf, map_zero]

end LatticeModel

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeModel

variable {K : Type} [Field K] [NumberField K] {m N : ℕ} {L : Submodule (𝓞 K) (Fin m → K)}

def prodSpan (L : Submodule (𝓞 K) (Fin m → K)) (d : ℕ) : Submodule (𝓞 K) (MvPolynomial (Fin m) K) :=
  Submodule.span (𝓞 K) {p | ∃ u : Fin d → Fin m → K, (∀ i, u i ∈ latticeDual L) ∧ p = ∏ i, latticeForm (u i)}

theorem one_mem_prodSpan_zero : (1 : MvPolynomial (Fin m) K) ∈ prodSpan L 0 :=
  Submodule.subset_span ⟨Fin.elim0, fun i ↦ i.elim0, by simp⟩

theorem latticeForm_mem_prodSpan_one {u : Fin m → K} (hu : u ∈ latticeDual L) :
    latticeForm u ∈ prodSpan L 1 :=
  Submodule.subset_span ⟨fun _ ↦ u, fun _ ↦ hu, by simp⟩

theorem mul_mem_prodSpan {a b : ℕ} {p q : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L a)
    (hq : q ∈ prodSpan L b) : p * q ∈ prodSpan L (a + b) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨v, hv, rfl⟩ := hy
      refine Submodule.subset_span ⟨Fin.append u v, fun i ↦ ?_, ?_⟩
      · refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i
        · rw [Fin.append_left]; exact hu i
        · rw [Fin.append_right]; exact hv i
      · rw [Fin.prod_univ_add]
        simp [Fin.append_left, Fin.append_right]
    | zero => rw [mul_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [← algebraMap_smul K c y, smul_eq_C_mul, mul_left_comm, ← smul_eq_C_mul, algebraMap_smul]
      exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul K c x, smul_eq_C_mul, mul_assoc, ← smul_eq_C_mul, algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem pow_mem_prodSpan {p : MvPolynomial (Fin m) K} (hp : p ∈ prodSpan L 1) (k : ℕ) :
    p ^ k ∈ prodSpan L k := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_prodSpan_zero
  | succ k ih => rw [pow_succ]; exact mul_mem_prodSpan ih hp

theorem prod_mem_prodSpan {ι : Type*} (t : Finset ι) (g : ι → MvPolynomial (Fin m) K) (e : ι → ℕ)
    (h : ∀ i ∈ t, g i ∈ prodSpan L (e i)) : ∏ i ∈ t, g i ∈ prodSpan L (∑ i ∈ t, e i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using one_mem_prodSpan_zero
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mul_mem_prodSpan (h i (Finset.mem_insert_self i t))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

theorem smul_mem_dual (c : 𝓞 K) {u : Fin m → K} (hu : u ∈ latticeDual L) :
    algebraMap (𝓞 K) K c • u ∈ latticeDual L := by
  intro v hv
  obtain ⟨b, hb⟩ := hu v hv
  exact ⟨c * b, by rw [map_mul, hb, smul_dotProduct, smul_eq_mul]⟩

variable {φ : Fin (N + 1) → Fin m → K}

theorem latticeMap_mem_prodSpan (hφ : IsDualBasis L φ) {d : ℕ}
    {f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ} (hf : f.IsHomogeneous d) : latticeMap φ f ∈ prodSpan L d := by
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s hs ↦ ?_
  have hdeg : s.degree = d := by
    have := hf (mem_support_iff.mp hs)
    rwa [weight_one_eq_degree] at this
  rw [latticeMap, coe_eval₂Hom, eval₂_monomial, eq_intCast, ← zsmul_eq_mul]
  refine zsmul_mem ?_ _
  rw [← hdeg, Finsupp.prod, Finsupp.degree]
  exact prod_mem_prodSpan _ _ _ fun v _ ↦ pow_mem_prodSpan (latticeForm_mem_prodSpan_one (mem_dual hφ v.2)) _

theorem prod_mem_latticeMap_image (hφ : IsDualBasis L φ) {d : ℕ} (u : Fin d → Fin m → K)
    (hu : ∀ i, u i ∈ latticeDual L) :
    ∃ f : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, f.IsHomogeneous d ∧ latticeMap φ f = ∏ i, latticeForm (u i) := by
  choose c hc using fun i ↦ (mem_dual_iff hφ (u i)).mp (hu i)
  refine ⟨∏ i, ∑ b, C (c i b) * X ⟨(), b⟩, ?_, ?_⟩
  · have h := IsHomogeneous.prod Finset.univ (fun i ↦ ∑ b, C (c i b) * X (⟨(), b⟩ : Coord fun _ : Unit ↦ N))
      (fun _ ↦ 1) fun i _ ↦ IsHomogeneous.sum _ _ _ fun b _ ↦ isHomogeneous_C_mul_X _ _
    simpa using h
  · rw [map_prod]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [latticeMap_linear, hc i]

theorem latticeMap_image_homogeneous (hφ : IsDualBasis L φ) {d : ℕ} (hd : 1 ≤ d) :
    latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ d)} =
      (prodSpan L d : Set (MvPolynomial (Fin m) K)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact latticeMap_mem_prodSpan hφ ((isWeightedHomogeneous_coordDeg_iff f _).mp hf)
  · intro p hp
    set Img := latticeMap φ '' {f | IsWeightedHomogeneous (coordDeg fun _ : Unit ↦ N) f (fun _ ↦ d)}
    have hadd : ∀ x ∈ Img, ∀ y ∈ Img, x + y ∈ Img := by
      rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
      exact ⟨f + g, hf.add hg, map_add _ _ _⟩
    have hprod : ∀ u : Fin d → Fin m → K, (∀ i, u i ∈ latticeDual L) → ∏ i, latticeForm (u i) ∈ Img := by
      intro u hu
      obtain ⟨f, hf, hfu⟩ := prod_mem_latticeMap_image hφ u hu
      exact ⟨f, (isWeightedHomogeneous_coordDeg_iff f _).mpr hf, hfu⟩
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    have key : ∀ x ∈ prodSpan L (k + 1), ∀ c : 𝓞 K, C (algebraMap (𝓞 K) K c) * x ∈ Img := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        intro c
        have hc : C (algebraMap (𝓞 K) K c) * ∏ i, latticeForm (u i) =
            ∏ i, latticeForm ((Fin.cons (algebraMap (𝓞 K) K c • u 0) (Fin.tail u) : Fin (k + 1) → Fin m → K) i) := by
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, ← mul_assoc, latticeForm_smul]
          rfl
        rw [hc]
        refine hprod _ fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i
        · rw [Fin.cons_zero]; exact smul_mem_dual c (hu 0)
        · rw [Fin.cons_succ]; exact hu j.succ
      | zero =>
        intro c
        exact ⟨0, isWeightedHomogeneous_zero _ _ _, by rw [mul_zero, map_zero]⟩
      | add x y _ _ hx hy =>
        intro c
        rw [mul_add]
        exact hadd _ (hx c) _ (hy c)
      | smul a x _ hx =>
        intro c
        rw [← algebraMap_smul K a x, smul_eq_C_mul, ← mul_assoc, ← map_mul, ← map_mul]
        exact hx (c * a)
    simpa using key p hp 1

section Birational

variable {r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)} {φ : Fin (N + 1) → Fin (r + 1) → K}

def yEval (φ : Fin (N + 1) → Fin (r + 1) → K) : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ →+* LatticeField K r :=
  eval₂Hom (Int.castRingHom _) (latticeCoord φ)

theorem yEval_eq (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) : yEval φ g = dehom K r (latticeMap φ g) := by
  have h : yEval φ = (dehom K r).comp (latticeMap φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [yEval, latticeMap]
    · intro v
      simp [yEval, latticeMap, latticeCoord_eq]
  rw [h, RingHom.comp_apply]

theorem dehom_latticeForm_apply (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) = ∑ j, algebraMap K (LatticeField K r) (u j) * genericVal K r j := by
  simp [dehom, latticeForm]

theorem dehom_latticeForm_ne_zero {u : Fin (r + 1) → K} (hu : u ≠ 0) : dehom K r (latticeForm u) ≠ 0 := by
  rw [dehom_latticeForm]
  intro h
  apply hu
  have h' := IsFractionRing.injective (MvPolynomial (Fin r) K) (LatticeField K r) (h.trans (map_zero _).symm)
  funext j
  refine Fin.cases ?_ (fun i ↦ ?_) j
  · have := congrArg (coeff 0) h'
    simpa [coeff_sum, coeff_C_mul, coeff_X, coeff_C] using this
  · have := congrArg (coeff (Finsupp.single i 1)) h'
    have h0 : (0 : Fin r →₀ ℕ) ≠ Finsupp.single i 1 := (Finsupp.single_ne_zero.mpr one_ne_zero).symm
    simpa [coeff_sum, coeff_C_mul, coeff_X, coeff_C, Finsupp.single_left_inj, h0] using this

theorem dehom_single_zero : dehom K r (latticeForm (Pi.single 0 1 : Fin (r + 1) → K)) = 1 := by
  simp [dehom, latticeForm, Pi.single_apply, genericVal]

theorem yEval_C_mul (k : ℤ) (g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ) :
    yEval φ (C k * g) = k * yEval φ g := by
  rw [yEval, coe_eval₂Hom, eval₂_mul, eval₂_C, eq_intCast]

theorem dehom_latticeForm_intSmul (k : ℤ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm ((k : K) • u)) = k * dehom K r (latticeForm u) := by
  rw [latticeForm_smul, map_mul]
  simp [dehom]

theorem exists_linear_of_mem {m : ℕ} {L' : Submodule (𝓞 K) (Fin m → K)} {φ' : Fin (N + 1) → Fin m → K}
    (hφ : IsDualBasis L' φ') {u : Fin m → K} (hu : u ∈ latticeDual L') :
    ∃ g : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ, g.IsHomogeneous 1 ∧ latticeMap φ' g = latticeForm u := by
  obtain ⟨c, hc⟩ := (mem_dual_iff hφ u).mp hu
  exact ⟨∑ b, C (c b) * X ⟨(), b⟩, IsHomogeneous.sum _ _ _ fun b _ ↦ isHomogeneous_C_mul_X _ _,
    by rw [latticeMap_linear, hc]⟩

def quotField (φ : Fin (N + 1) → Fin (r + 1) → K) : Subfield (LatticeField K r) where
  carrier := {s | ∃ (d : ℕ) (g h : MvPolynomial (Coord fun _ : Unit ↦ N) ℤ), g.IsHomogeneous d ∧ h.IsHomogeneous d ∧
    yEval φ h ≠ 0 ∧ yEval φ g = s * yEval φ h}
  mul_mem' := by
    rintro s s' ⟨d, g, h, hg, hh, hne, he⟩ ⟨d', g', h', hg', hh', hne', he'⟩
    exact ⟨d + d', g * g', h * h', hg.mul hg', hh.mul hh', by rw [map_mul]; exact mul_ne_zero hne hne',
      by rw [map_mul, map_mul, he, he']; ring⟩
  one_mem' := ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  add_mem' := by
    rintro s s' ⟨d, g, h, hg, hh, hne, he⟩ ⟨d', g', h', hg', hh', hne', he'⟩
    refine ⟨d + d', g * h' + h * g', h * h', (hg.mul hh').add (hh.mul hg'), hh.mul hh',
      by rw [map_mul]; exact mul_ne_zero hne hne', ?_⟩
    rw [map_add, map_mul, map_mul, map_mul, he, he']
    ring
  zero_mem' := ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
  neg_mem' := by
    rintro s ⟨d, g, h, hg, hh, hne, he⟩
    exact ⟨d, -g, h, hg.neg, hh, hne, by rw [map_neg, he]; ring⟩
  inv_mem' := by
    rintro s ⟨d, g, h, hg, hh, hne, he⟩
    by_cases hs : s = 0
    · subst hs
      rw [inv_zero]
      exact ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
    · refine ⟨d, h, g, hh, hg, by rw [he]; exact mul_ne_zero hs hne, ?_⟩
      rw [he]
      field_simp

theorem dehom_mem_quotField (hL : L.FG) (hφ : IsDualBasis L φ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) ∈ quotField φ := by
  obtain ⟨n, hn, hnu⟩ := exists_int_smul_mem_latticeDual hL u
  obtain ⟨n', hn', hne⟩ := exists_int_smul_mem_latticeDual hL (Pi.single 0 1 : Fin (r + 1) → K)
  obtain ⟨g, hg, hgu⟩ := exists_linear_of_mem (N := N) hφ hnu
  obtain ⟨h, hh, hhe⟩ := exists_linear_of_mem (N := N) hφ hne
  have hg' : yEval φ g = n * dehom K r (latticeForm u) := by
    rw [yEval_eq, hgu, dehom_latticeForm_intSmul]
  have hh' : yEval φ h = n' := by
    rw [yEval_eq, hhe, dehom_latticeForm_intSmul, dehom_single_zero, mul_one]
  refine ⟨1, C n' * g, C n * h, by simpa using (isHomogeneous_C _ _).mul hg,
    by simpa using (isHomogeneous_C _ _).mul hh, ?_, ?_⟩
  · rw [yEval_C_mul, hh']
    exact mul_ne_zero (Int.cast_ne_zero.mpr hn) (Int.cast_ne_zero.mpr hn')
  · rw [yEval_C_mul, yEval_C_mul, hg', hh']
    ring

theorem mem_quotField (hL : L.FG) (hφ : IsDualBasis L φ) (s : LatticeField K r) : s ∈ quotField φ := by
  have hpoly : ∀ p : MvPolynomial (Fin r) K, algebraMap _ (LatticeField K r) p ∈ quotField φ := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have e : algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (C a) = dehom K r (latticeForm (Pi.single 0 a)) := by
        simp [dehom, latticeForm, Pi.single_apply, genericVal, algebraMap_C, Fin.sum_univ_succ]
      rw [e]
      exact dehom_mem_quotField hL hφ _
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      have e : algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j) = dehom K r (latticeForm (Pi.single j.succ 1)) := by
        simp [dehom, latticeForm, Pi.single_apply, genericVal]
      rw [e]
      exact dehom_mem_quotField hL hφ _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (Fin r) K) s
  exact div_mem (hpoly a) (hpoly b)

theorem isMultiHomog_iff (g : Geo.MRing (blockIdx fun _ : Unit ↦ N)) (d : Unit → ℕ) :
    Geo.IsMultiHomog g d ↔ g.IsHomogeneous (d ()) := by
  have hdeg : ∀ s : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ, ∑ i : Fin (N + 1), s ⟨(), i⟩ = s.degree := by
    intro s
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
    simp
  constructor
  · intro h s hs
    rw [weight_one_eq_degree, ← hdeg]
    exact h s (mem_support_iff.mpr hs) ()
  · intro h s hs k
    have := h (mem_support_iff.mp hs)
    rw [weight_one_eq_degree, ← hdeg] at this
    exact this

theorem birational_latticeCoord (hL : L.FG) (hφ : IsDualBasis L φ) :
    Geo.Birational (ι := blockIdx fun _ : Unit ↦ N) (latticeCoord φ) := by
  intro s
  obtain ⟨d, g, h, hg, hh, hne, he⟩ := mem_quotField hL hφ s
  refine ⟨fun _ ↦ d, g, h, (isMultiHomog_iff g _).mpr hg, (isMultiHomog_iff h _).mpr hh, ?_, ?_⟩
  · simpa only [aeval_def, algebraMap_int_eq, yEval, coe_eval₂Hom] using hne
  · simpa only [aeval_def, algebraMap_int_eq, yEval, coe_eval₂Hom] using he

end Birational

end LatticeModel

end

end GroundTheory.Heights₂.Heights
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

noncomputable section

set_option linter.unusedSectionVars false

namespace LatticeModel

variable {K : Type} [Field K] [NumberField K] {N r : ℕ} {L : Submodule (𝓞 K) (Fin (r + 1) → K)}
  {φ : Fin (N + 1) → Fin (r + 1) → K}

def genericT (K : Type) [Field K] (r : ℕ) : Fin r → LatticeField K r :=
  fun j ↦ algebraMap (MvPolynomial (Fin r) K) (LatticeField K r) (X j)

theorem algebraicIndependent_genericT : AlgebraicIndependent ℚ (genericT K r) := by
  have h := (MvPolynomial.algebraicIndependent_X (Fin r) K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial (Fin r) K) (LatticeField K r)) (IsFractionRing.injective _ _)
  exact h.restrictScalars (algebraMap ℚ K).injective

theorem genericT_eq (j : Fin r) : genericT K r j = dehom K r (latticeForm (Pi.single j.succ 1)) := by
  simp [genericT, dehom, latticeForm, Pi.single_apply, genericVal]

theorem latticeCoord_ne_zero (hφ : IsDualBasis L φ) (b : Fin (N + 1)) : latticeCoord φ ⟨(), b⟩ ≠ 0 := by
  rw [latticeCoord_eq]
  exact dehom_latticeForm_ne_zero (hφ.independent.ne_zero b)

theorem dehom_latticeForm_sum (c : Fin (N + 1) → ℤ) :
    dehom K r (latticeForm (∑ b, c b • φ b)) = ∑ b, (c b : LatticeField K r) * latticeCoord φ ⟨(), b⟩ := by
  rw [latticeForm_sum, map_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [latticeForm_zsmul, map_mul, latticeCoord_eq]
  simp [dehom]

theorem dehom_div_mem_adjoin (hL : L.FG) (hφ : IsDualBasis L φ) (u : Fin (r + 1) → K) :
    dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ ∈
      IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1))) := by
  set E := IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1)))
  have hb : ∀ b, latticeCoord φ ⟨(), b⟩ / latticeCoord φ ⟨(), 0⟩ ∈ E := fun b ↦
    IntermediateField.subset_adjoin _ _ ⟨⟨(), b⟩, rfl⟩
  obtain ⟨n, hn, hnu⟩ := exists_int_smul_mem_latticeDual hL u
  obtain ⟨c, hc⟩ := (mem_dual_iff hφ _).mp hnu
  have h1 : (n : LatticeField K r) * dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ ∈ E := by
    rw [← dehom_latticeForm_intSmul, ← hc, dehom_latticeForm_sum, Finset.sum_div]
    refine sum_mem fun b _ ↦ ?_
    rw [mul_div_assoc]
    exact mul_mem (intCast_mem _ _) (hb b)
  have h2 : (n : LatticeField K r) ≠ 0 := Int.cast_ne_zero.mpr hn
  have h3 := div_mem h1 (intCast_mem E n)
  have e : (n : LatticeField K r) * dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ / n =
      dehom K r (latticeForm u) / latticeCoord φ ⟨(), 0⟩ := by
    field_simp
  rwa [e] at h3

theorem genericT_mem_adjoin (hL : L.FG) (hφ : IsDualBasis L φ) (j : Fin r) :
    genericT K r j ∈ IntermediateField.adjoin ℚ (coneRatios (latticeCoord φ) fun _ : Unit ↦ (0 : Fin (N + 1))) := by
  have h := div_mem (dehom_div_mem_adjoin hL hφ (Pi.single j.succ 1))
    (dehom_div_mem_adjoin hL hφ (Pi.single 0 1))
  have hy := latticeCoord_ne_zero hφ 0
  rw [dehom_single_zero, ← genericT_eq] at h
  have e : genericT K r j / latticeCoord φ ⟨(), 0⟩ / (1 / latticeCoord φ ⟨(), 0⟩) = genericT K r j := by
    field_simp
  rwa [e] at h

theorem isAlgebraic_dehom (u : Fin (r + 1) → K) :
    IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (genericT K r))) (dehom K r (latticeForm u)) := by
  set E := IntermediateField.adjoin ℚ (Set.range (genericT K r))
  rw [← Subalgebra.mem_algebraicClosure, dehom_latticeForm_apply]
  refine sum_mem fun j _ ↦ mul_mem ?_ ?_
  · rw [Subalgebra.mem_algebraicClosure]
    have h : IsAlgebraic ℚ (algebraMap K (LatticeField K r) (u j)) := by
      simpa using (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (u j)).algHom
        (IsScalarTower.toAlgHom ℚ K (LatticeField K r))
    exact h.tower_top E
  · rw [Subalgebra.mem_algebraicClosure]
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simpa [genericVal] using isAlgebraic_one (R := E) (A := LatticeField K r)
    · have hi : genericT K r i ∈ E := IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      simpa [genericVal, genericT] using isAlgebraic_algebraMap (R := E) (A := LatticeField K r) ⟨_, hi⟩

theorem ratios_isAlgebraic (s : LatticeField K r)
    (hs : s ∈ coneRatios (latticeCoord φ) (fun _ : Unit ↦ (0 : Fin (N + 1)))) :
    IsAlgebraic (IntermediateField.adjoin ℚ (Set.range (genericT K r))) s := by
  obtain ⟨p, rfl⟩ := hs
  have h0 := isAlgebraic_dehom (r := r) (φ 0)
  have hp := isAlgebraic_dehom (r := r) (φ p.2)
  have e : latticeCoord φ p / latticeCoord φ ⟨p.1, 0⟩ =
      dehom K r (latticeForm (φ p.2)) * (dehom K r (latticeForm (φ 0)))⁻¹ := by
    rw [latticeCoord_eq, latticeCoord_eq, div_eq_mul_inv]
  change IsAlgebraic _ (latticeCoord φ p / latticeCoord φ ⟨p.1, 0⟩)
  rw [e]
  exact hp.mul h0.inv

end LatticeModel

theorem OneBlockModel.proof (hCC : CoordConeArithVar.Statement) : OneBlockModel.Statement := by
  intro K _ _ r N F φ hφ
  refine ⟨⟨LatticeModel.latticeVariety φ hφ, rfl⟩, LatticeModel.mCoordIdeal_latticeCoord φ, ?_,
    LatticeModel.birational_latticeCoord F.fg hφ, fun m hm ↦ LatticeModel.latticeMap_image_homogeneous hφ hm⟩
  rw [← LatticeModel.mCoordIdeal_latticeCoord φ]
  exact hCC Unit (blockIdx fun _ : Unit ↦ N) (LatticeField K r) (latticeCoord φ) (fun _ ↦ 0) r
    (LatticeModel.genericT K r) ⟨()⟩ (fun _ ↦ LatticeModel.latticeCoord_ne_zero hφ 0)
    LatticeModel.algebraicIndependent_genericT (LatticeModel.genericT_mem_adjoin F.fg hφ)
    LatticeModel.ratios_isAlgebraic

end

end GroundTheory.Heights₂.Heights
end
