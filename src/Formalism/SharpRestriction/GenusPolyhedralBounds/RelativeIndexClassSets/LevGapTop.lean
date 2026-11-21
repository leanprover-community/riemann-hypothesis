import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc

noncomputable section
namespace Formalism.MainNotions.Gaps.LevGap
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct

section DefCong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

def CongAt (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (g : GL n (E ⊗[F] v.adicCompletion F)) : Prop :=
  ∀ i j, ∃ s ∈ intV E v, (g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
    (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j = (c : E ⊗[F] v.adicCompletion F) * s

end DefCong

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem rsmul_tmul (a : R) (e : E) (r : R) : a • (e ⊗ₜ[F] r) = e ⊗ₜ[F] (a * r) := by
  rw [Algebra.smul_def]
  show ((1 : E) ⊗ₜ[F] a) * (e ⊗ₜ[F] r) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def comb {ι : Type} [Fintype ι] (e : ι → E) : (ι → R) →ₗ[R] E ⊗[F] R :=
  Fintype.linearCombination R (fun i => e i ⊗ₜ[F] (1 : R))

theorem comb_apply {ι : Type} [Fintype ι] (e : ι → E) (a : ι → R) :
    comb (F := F) R e a = ∑ i, e i ⊗ₜ[F] a i := by
  unfold comb
  rw [Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rsmul_tmul, mul_one]

theorem comb_surj {ι : Type} [Fintype ι] (e : ι → E) (he : Submodule.span F (Set.range e) = ⊤) :
    Function.Surjective (comb (F := F) R e) := by
  intro x
  rw [← LinearMap.mem_range]
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a r =>
    have ha : a ∈ Submodule.span F (Set.range e) := by rw [he]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 ha
    refine ⟨fun i => c i • r, ?_⟩
    rw [comb_apply, ← hc, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul]

def crd {ι : Type} (b : Module.Basis ι F E) (i : ι) : E ⊗[F] R →ₗ[R] R where
  toFun x := TensorProduct.lid F R ((b.coord i).rTensor R x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add, map_add, smul_add]
    | tmul e r =>
      rw [rsmul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        TensorProduct.lid_tmul, RingHom.id_apply, smul_eq_mul, mul_smul_comm]

theorem crd_tmul {ι : Type} (b : Module.Basis ι F E) (i : ι) (e : E) (r : R) :
    crd R b i (e ⊗ₜ[F] r) = b.repr e i • r := by
  show TensorProduct.lid F R ((b.coord i).rTensor R (e ⊗ₜ[F] r)) = _
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply]


variable [TopologicalSpace R] [IsTopologicalRing R]

local instance topT : TopologicalSpace (E ⊗[F] R) := tensTopL (F := F) (E := E) R

local instance modT : IsModuleTopology R (E ⊗[F] R) := ⟨rfl⟩

variable [FiniteDimensional F E]

theorem finT : Module.Finite R (E ⊗[F] R) :=
  Module.Finite.of_surjective (comb (F := F) R (Module.finBasis F E))
    (comb_surj R _ (Module.finBasis F E).span_eq)

theorem ringT : IsTopologicalRing (E ⊗[F] R) :=
  haveI := finT (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (E ⊗[F] R)




theorem sigR_cont (σ : E →ₐ[F] E) : Continuous (sigR σ R) := by
  have := ringT (F := F) (E := E) R
  refine IsModuleTopology.continuous_of_ringHom (R := R) (sigR σ R) ?_
  have h : (sigR σ R).comp (algebraMap R (E ⊗[F] R)) = algebraMap R (E ⊗[F] R) := by
    ext a
    show (Algebra.TensorProduct.map σ (AlgHom.id F R)) ((1 : E) ⊗ₜ[F] a) = (1 : E) ⊗ₜ[F] a
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rw [h]
  exact continuous_algebraMap R (E ⊗[F] R)


end Gen

section GLc

variable {M : Type} [CommRing M] [TopologicalSpace M] [IsTopologicalRing M] [T2Space M]
  {n : Type} [Fintype n] [DecidableEq n]


end GLc

section Dec

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
variable {R : Type} [CommRing R] [Algebra F R] (O : Subring R)


def QD {m : ℕ} (b : Fin m → 𝓞 E) (s : E ⊗[F] R) : Prop :=
  ∃ r : Fin m → R, (∀ j, r j ∈ O) ∧ s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j

theorem QD_zero {m : ℕ} (b : Fin m → 𝓞 E) : QD (F := F) O b 0 :=
  ⟨0, fun _ => zero_mem _, by simp⟩

theorem QD_add {m : ℕ} (b : Fin m → 𝓞 E) {x y : E ⊗[F] R} (hx : QD O b x) (hy : QD O b y) :
    QD O b (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  refine ⟨r + r', fun j => add_mem (hr j) (hr' j), ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_add _ _ _).symm

theorem QD_neg {m : ℕ} (b : Fin m → 𝓞 E) {x : E ⊗[F] R} (hx : QD O b x) : QD O b (-x) := by
  obtain ⟨r, hr, rfl⟩ := hx
  refine ⟨-r, fun j => neg_mem (hr j), ?_⟩
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => (TensorProduct.tmul_neg _ _).symm

theorem QD_sum {m : ℕ} (b : Fin m → 𝓞 E) {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] R)
    (h : ∀ i ∈ s, QD O b (f i)) : QD O b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (QD O b) (fun _ _ hx hy => QD_add O b hx hy) (QD_zero O b) h

theorem QD_tmul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    (e : 𝓞 E) {y : R} (hy : y ∈ O) : QD (F := F) O b (algebraMap (𝓞 E) E e ⊗ₜ[F] y) := by
  have he : e ∈ Submodule.span ℤ (Set.range b) := by rw [hb]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 he
  refine ⟨fun j => c j • y, fun j => zsmul_mem hy _, ?_⟩
  rw [← hc, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, TensorProduct.smul_tmul]

theorem QD_mul {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {x y : E ⊗[F] R} (hx : QD O b x) (hy : QD O b y) : QD O b (x * y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨r', hr', rfl⟩ := hy
  rw [Finset.sum_mul_sum]
  refine QD_sum O b _ _ fun j _ => QD_sum O b _ _ fun k _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, ← map_mul]
  exact QD_tmul O b hb _ (mul_mem (hr j) (hr' k))

theorem QD_of_mem {m : ℕ} (b : Fin m → 𝓞 E) (hb : Submodule.span ℤ (Set.range b) = ⊤)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) O) : QD O b s := by
  refine Subring.closure_induction (p := fun s _ => QD O b s) ?_ ?_ ?_ ?_ ?_ ?_ hs
  · rintro x (⟨⟨e, ⟨e', rfl⟩⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · exact QD_tmul O b hb e' (one_mem _)
    · have := QD_tmul (F := F) O b hb 1 hy
      rwa [map_one] at this
  · exact QD_zero O b
  · have := QD_tmul (F := F) O b hb 1 (one_mem O)
    rwa [map_one, ← Algebra.TensorProduct.one_def] at this
  · intro x y _ _ hx hy; exact QD_add O b hx hy
  · intro x _ hx; exact QD_neg O b hx
  · intro x y _ _ hx hy; exact QD_mul O b hb hx hy

variable [NumberField F]

theorem crd_int (hO : ∀ t : 𝓞 F, algebraMap F R (algebraMap (𝓞 F) F t) ∈ O)
    {ι : Type} (b : Module.Basis ι F E) {m : ℕ} (β : Fin m → 𝓞 E)
    (hβ : Submodule.span ℤ (Set.range β) = ⊤) (N1 : F)
    (hN1 : ∀ j l, ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = N1 * b.repr (algebraMap (𝓞 E) E (β j)) l)
    {s : E ⊗[F] R} (hs : s ∈ tensInt (F := F) R (intOE E) O) (l : ι) :
    algebraMap F R N1 * crd R b l s ∈ O := by
  obtain ⟨r, hr, rfl⟩ := QD_of_mem O β hβ hs
  rw [map_sum, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  obtain ⟨t, ht⟩ := hN1 j l
  rw [crd_tmul, Algebra.smul_def, ← mul_assoc, ← map_mul, ← ht]
  exact mul_mem (hO t) (hr j)

theorem crd_natCast_mul {ι : Type} (b : Module.Basis ι F E) (l : ι) (k : ℕ) (x : E ⊗[F] R) :
    crd R b l ((k : E ⊗[F] R) * x) = (k : R) * crd R b l x := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

variable {n : Type} [Fintype n] [DecidableEq n]

theorem latS_den (Λ : Submodule (𝓞 E) (n → E)) (N' : ℕ)
    (h2 : ∀ x ∈ Λ, ∀ i, (N' : E) * x i ∈ intOE E) {y : n → E ⊗[F] R}
    (hy : y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ) (i : n) :
    (N' : E ⊗[F] R) * y i ∈ tensInt (F := F) R (intOE E) O := by
  unfold latS at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x0, hx0, rfl⟩ := hx
    have : (N' : E ⊗[F] R) * inclE (F := F) R (x0 i) = inclE (F := F) R ((N' : E) * x0 i) := by
      rw [map_mul, map_natCast]
    show (N' : E ⊗[F] R) * inclE (F := F) R (x0 i) ∈ _
    rw [this]
    exact Subring.subset_closure (Or.inl ⟨⟨_, h2 x0 hx0 i⟩, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [Pi.add_apply, mul_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have : (N' : E ⊗[F] R) * (a • x) i = (a : E ⊗[F] R) * ((N' : E ⊗[F] R) * x i) := by
      rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
    rw [this]
    exact mul_mem a.2 hx

theorem stab_entry (Λ : Submodule (𝓞 E) (n → E)) (N : ℕ)
    (h1 : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (g : GL n (E ⊗[F] R))
    (hg : g ∈ stabGL (latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ)) (j : n) :
    ∃ y ∈ latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ,
      ∀ i, y i = (N : E ⊗[F] R) * (g : Matrix n n (E ⊗[F] R)) i j := by
  refine ⟨_, (hg _).1 (Submodule.subset_span ⟨_, h1 j, rfl⟩), fun i => ?_⟩
  show ∑ k, (g : Matrix n n (E ⊗[F] R)) i k *
    inclE (F := F) R (((N : E) • (Pi.single j 1 : n → E)) k) = _
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro k _ hk; simp [hk]
  · simp

theorem entry_bd (hO : ∀ t : 𝓞 F, algebraMap F R (algebraMap (𝓞 F) F t) ∈ O)
    {ι : Type} (b : Module.Basis ι F E) {m : ℕ} (β : Fin m → 𝓞 E)
    (hβ : Submodule.span ℤ (Set.range β) = ⊤) (N1 : F)
    (hN1 : ∀ j l, ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = N1 * b.repr (algebraMap (𝓞 E) E (β j)) l)
    (Λ : Submodule (𝓞 E) (n → E)) (N N' : ℕ)
    (h1 : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ)
    (h2 : ∀ x ∈ Λ, ∀ i, (N' : E) * x i ∈ intOE E) (g : GL n (E ⊗[F] R))
    (hg : g ∈ stabGL (latS (F := F) R (tensInt (F := F) R (intOE E) O) Λ)) (i j : n) (l : ι) :
    algebraMap F R (N1 * N' * N) * crd R b l ((g : Matrix n n (E ⊗[F] R)) i j) ∈ O := by
  obtain ⟨y, hy, hyi⟩ := stab_entry O Λ N h1 g hg j
  have h := crd_int O hO b β hβ N1 hN1 (latS_den O Λ N' h2 hy i) l
  rw [hyi, crd_natCast_mul, crd_natCast_mul] at h
  have e : algebraMap F R (N1 * N' * N) * crd R b l ((g : Matrix n n (E ⊗[F] R)) i j) =
      algebraMap F R N1 * ((N' : R) * ((N : R) * crd R b l ((g : Matrix n n (E ⊗[F] R)) i j))) := by
    rw [map_mul, map_mul, map_natCast, map_natCast]; ring
  rw [e]; exact h

end Dec

section Adele

variable {F : Type} [Field F] [NumberField F]

theorem compact_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) := by
  have h1 : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have h2 : IsClosed ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    Valued.isClosed_valuationSubring _
  have h3 : CompleteSpace (v.adicCompletionIntegers F) := h2.completeSpace_coe
  exact Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
    ⟨h3, (inferInstance : IsDiscreteValuationRing (v.adicCompletionIntegers F)), h1⟩

theorem isCompact_intAd : IsCompact (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F) := compact_Ov
  have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

theorem isOpen_intAd : IsOpen (intAd F : Set (FiniteAdeleRing (𝓞 F) F)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

open scoped RestrictedProduct in
theorem t2Space_adeleRing_numberField : T2Space 𝔸 :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem isCompact_scaled (c : F) (hc : c ≠ 0) :
    IsCompact {a : 𝔸 | algebraMap F 𝔸 c * a ∈ intAd F} := by
  have e : {a : 𝔸 | algebraMap F 𝔸 c * a ∈ intAd F} =
      (fun y => algebraMap F 𝔸 c⁻¹ * y) '' (intAd F : Set 𝔸) := by
    ext a
    constructor
    · intro h
      refine ⟨_, h, ?_⟩
      show algebraMap F 𝔸 c⁻¹ * (algebraMap F 𝔸 c * a) = a
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    · rintro ⟨y, hy, rfl⟩
      show algebraMap F 𝔸 c * (algebraMap F 𝔸 c⁻¹ * y) ∈ intAd F
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
      exact hy
  rw [e]
  exact isCompact_intAd.image (continuous_const.mul continuous_id)

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem crd_prV {ι : Type} (b : Module.Basis ι F E) (l : ι) (v : HeightOneSpectrum (𝓞 F))
    (x : E ⊗[F] 𝔸) : crd (v.adicCompletion F) b l (prV (E := E) v x) = (crd 𝔸 b l x) v := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; rfl
  | tmul e a =>
    rw [Formalism.UG.P.afsplit_prV_tmul, crd_tmul, crd_tmul, Formalism.UG.P.afsplit_smul_apply]


theorem exists_int_span : ∃ e : Fin (Module.finrank F E) → 𝓞 E,
    Submodule.span F (Set.range fun l => algebraMap (𝓞 E) E (e l)) = ⊤ := by
  set b := Module.finBasis F E
  obtain ⟨d, hd, -, hdi⟩ := Formalism.UG.P.sf_den (fun l => b l)
  refine ⟨fun l => ⟨d * b l, hdi l⟩, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ l, b.repr (d⁻¹ * x) l • (d * b l) := by
    simp_rw [← mul_smul_comm]
    rw [← Finset.mul_sum, b.sum_repr, mul_inv_cancel_left₀ hd]
  rw [hx]
  exact sum_mem fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)


theorem exists_den {ι : Type} [Finite ι] (b : Module.Basis ι F E) {m : ℕ} (β : Fin m → 𝓞 E) :
    ∃ N1 : F, N1 ≠ 0 ∧
      ∀ j l, ∃ t : 𝓞 F, algebraMap (𝓞 F) F t = N1 * b.repr (algebraMap (𝓞 E) E (β j)) l := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 F))
    (fun p : Fin m × ι => b.repr (algebraMap (𝓞 E) E (β p.1)) p.2)
  refine ⟨algebraMap (𝓞 F) F d, ?_, fun j l => ?_⟩
  · intro h
    apply nonZeroDivisors.coe_ne_zero d
    exact (IsFractionRing.injective (𝓞 F) F) (by simp at h)
  · obtain ⟨t, ht⟩ := hd (j, l)
    exact ⟨t, by rw [ht, Algebra.smul_def]⟩

end Adele

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance topT' (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    TopologicalSpace (E ⊗[F] R) := tensTopL (F := F) (E := E) R

theorem bc_apply {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (g : GL n A) (i j : n) :
    (bc φ g : Matrix n n B) i j = φ ((g : Matrix n n A) i j) := rfl




end Main

section Bridge

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_nat_smul_mem (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ := by
  obtain ⟨m, hm0, hm⟩ := Formalism.UG.P.csGlob_single Λ hspan
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, fun j => ?_⟩
  have h1 : ((m.natAbs : ℕ) : E) • (Pi.single j 1 : n → E) = Pi.single j ((m.natAbs : ℤ) : E) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one, Int.cast_natCast]
  rw [h1]
  rcases Int.natAbs_eq m with h | h
  · rw [← h]; exact hm j
  · have h2 : ((m.natAbs : ℤ) : E) = -(m : E) := by
      have h3 : (m.natAbs : ℤ) = -m := by omega
      rw [h3, Int.cast_neg]
    rw [h2, Pi.single_neg]; exact neg_mem (hm j)

theorem mem_stabGL_of {A R : Type} [CommRing A] [CommRing R] [Algebra R A] (Λ : Submodule R (n → A))
    (g : GL n A) (h1 : ∀ y ∈ Λ, (g : Matrix n n A) *ᵥ y ∈ Λ)
    (h2 : ∀ y ∈ Λ, ((g⁻¹ : GL n A) : Matrix n n A) *ᵥ y ∈ Λ) : g ∈ stabGL Λ := by
  change ∀ x : n → A, x ∈ Λ ↔ (g : Matrix n n A) *ᵥ x ∈ Λ
  intro x
  refine ⟨h1 x, fun h => ?_⟩
  have := h2 _ h
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

section Loc

variable (v : HeightOneSpectrum (𝓞 F))

theorem incl_mem_intV {e : E} (he : e ∈ intOE E) :
    inclE (F := F) (v.adicCompletion F) e ∈ intV E v :=
  Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

theorem smul_mem_lat (L : Submodule (intV E v) (n → E ⊗[F] v.adicCompletion F))
    {a : E ⊗[F] v.adicCompletion F} (ha : a ∈ intV E v) {z : n → E ⊗[F] v.adicCompletion F}
    (hz : z ∈ L) : a • z ∈ L := L.smul_mem ⟨a, ha⟩ hz

theorem CongAt.mono {c c' : ℕ} (h : c' ∣ c) {g : GL n (E ⊗[F] v.adicCompletion F)}
    (hg : CongAt v c g) : CongAt v c' g := by
  obtain ⟨e, rfl⟩ := h
  intro i j
  obtain ⟨s, hs, he⟩ := hg i j
  exact ⟨(e : E ⊗[F] v.adicCompletion F) * s, mul_mem (natCast_mem _ e) hs, by
    rw [he, Nat.cast_mul, mul_assoc]⟩

theorem latS_int (Λ : Submodule (𝓞 E) (n → E)) (hint : ∀ x ∈ Λ, ∀ i, x i ∈ intOE E)
    {y : n → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ) (i : n) : y i ∈ intV E v := by
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨x, hx, rfl⟩ := hy; exact incl_mem_intV v (hint x hx i)
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul s a _ ha => exact mul_mem s.2 ha

theorem latS_of_int (Λ : Submodule (𝓞 E) (n → E)) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (z : n → E ⊗[F] v.adicCompletion F)
    (hz : ∀ i, z i ∈ intV E v) :
    (N : E ⊗[F] v.adicCompletion F) • z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ := by
  have h : (N : E ⊗[F] v.adicCompletion F) • z = ∑ j, (⟨z j, hz j⟩ : intV E v) •
      (fun i => inclE (F := F) (v.adicCompletion F) (((N : E) • (Pi.single j 1 : n → E)) i)) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · show (N : E ⊗[F] v.adicCompletion F) * z i =
        z i * inclE (F := F) (v.adicCompletion F) (((N : E) • (Pi.single i 1 : n → E)) i)
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, map_natCast, mul_comm]
    · intro j _ hj
      show z j * inclE (F := F) (v.adicCompletion F) (((N : E) • (Pi.single j 1 : n → E)) i) = 0
      rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero, map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [h]
  exact sum_mem fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hN j, rfl⟩)

theorem cong_sub (Λ : Submodule (𝓞 E) (n → E)) (N c1 : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (hint : ∀ x ∈ Λ, ∀ i, x i ∈ intOE E)
    (g : GL n (E ⊗[F] v.adicCompletion F)) (hg : CongAt v (N * c1) g)
    {y : n → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ) :
    ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ,
      (g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (c1 : E ⊗[F] v.adicCompletion F) • z := by
  choose s hs he using hg
  refine ⟨(N : E ⊗[F] v.adicCompletion F) • (fun i => ∑ j, s i j * y j),
    latS_of_int v Λ N hN _ (fun i => sum_mem fun j _ => mul_mem (hs i j) (latS_int v Λ hint hy j)), ?_⟩
  ext i
  have h : ((g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y - y) i =
      ∑ j, ((g : Matrix n n (E ⊗[F] v.adicCompletion F)) i j -
        (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) * y j := by
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp [Matrix.one_apply]
  rw [h]
  simp only [he, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Nat.cast_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cong_map (Λ : Submodule (𝓞 E) (n → E)) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : n → E) ∈ Λ) (hint : ∀ x ∈ Λ, ∀ i, x i ∈ intOE E)
    (g : GL n (E ⊗[F] v.adicCompletion F)) (hg : CongAt v N g)
    {y : n → E ⊗[F] v.adicCompletion F}
    (hy : y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Λ) :
    (g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Λ := by
  obtain ⟨z, hz, he⟩ := cong_sub v Λ N 1 hN hint g (by rwa [mul_one]) hy
  have h : (g : Matrix n n (E ⊗[F] v.adicCompletion F)) *ᵥ y =
      y + ((1 : ℕ) : E ⊗[F] v.adicCompletion F) • z := by rw [← he]; abel
  rw [h]
  exact add_mem hy (smul_mem_lat v _ (natCast_mem _ 1) hz)


theorem isUnit_natCast {T : ℕ} (hT : T ≠ 0) : IsUnit ((T : ℕ) : E ⊗[F] v.adicCompletion F) := by
  have h : ((T : ℕ) : E ⊗[F] v.adicCompletion F) =
      algebraMap F (E ⊗[F] v.adicCompletion F) (T : F) := (map_natCast _ _).symm
  rw [h]
  exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hT)).map _

end Loc

section ParSec

variable {k : ℕ} (P : Par F E k) (v : HeightOneSpectrum (𝓞 F))

theorem lb_int : ∀ x ∈ P.Lb, ∀ i, x i ∈ intOE E := by
  intro x hx i
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    unfold lbVec
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same]
      split_ifs
      · exact ⟨P.pz, rfl⟩
      · exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul r a _ ha => exact mul_mem ⟨r, rfl⟩ ha


theorem lbV_le_ldV {d : ℕ} (hL : P.LbOK d) : P.LbV v ≤ P.LdV v :=
  Submodule.span_mono (Set.image_mono fun x hx => Submodule.subset_span (hL.int x hx))

theorem T_smul_mem_dual_lattice {d : ℕ} (hL : P.LbOK d) {x : Fin k → E} (hx : x ∈ P.Ld) : (P.T : E) • x ∈ P.Lb := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hL.dual x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul r a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ r ha

theorem T_smul_mem_local_dual_lattice {d : ℕ} (hL : P.LbOK d) {y : Fin k → E ⊗[F] v.adicCompletion F} (hy : y ∈ P.LdV v) :
    (P.T : E ⊗[F] v.adicCompletion F) • y ∈ P.LbV v := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    refine Submodule.subset_span ⟨_, T_smul_mem_dual_lattice P hL hx, ?_⟩
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul s a _ ha =>
    have h : (P.T : E ⊗[F] v.adicCompletion F) • s • a = s • (P.T : E ⊗[F] v.adicCompletion F) • a := by
      ext i
      show (P.T : E ⊗[F] v.adicCompletion F) * ((s : E ⊗[F] v.adicCompletion F) * a i) =
        (s : E ⊗[F] v.adicCompletion F) * ((P.T : E ⊗[F] v.adicCompletion F) * a i)
      ring
    rw [h]; exact Submodule.smul_mem _ s ha

theorem ld_sub {d : ℕ} (hL : P.LbOK d) (hT : P.T ≠ 0) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : Fin k → E) ∈ P.Lb)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (hg : CongAt v (N * P.T) g)
    {y : Fin k → E ⊗[F] v.adicCompletion F} (hy : y ∈ P.LdV v) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ P.LbV v := by
  obtain ⟨z, hz, he⟩ := cong_sub v P.Lb N P.T hN (lb_int P) g hg (T_smul_mem_local_dual_lattice P v hL hy)
  have h : (P.T : E ⊗[F] v.adicCompletion F) •
      ((g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y) =
      (P.T : E ⊗[F] v.adicCompletion F) • z := by
    rw [smul_sub, ← Matrix.mulVec_smul, he]
  rw [(isUnit_natCast (E := E) v hT).smul_left_cancel.1 h]
  exact hz

theorem ld_map {d : ℕ} (hL : P.LbOK d) (hT : P.T ≠ 0) (N : ℕ)
    (hN : ∀ j, (N : E) • (Pi.single j 1 : Fin k → E) ∈ P.Lb)
    (g : GL (Fin k) (E ⊗[F] v.adicCompletion F)) (hg : CongAt v (N * P.T) g)
    {y : Fin k → E ⊗[F] v.adicCompletion F} (hy : y ∈ P.LdV v) :
    (g : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ P.LdV v := by
  have h := add_mem (lbV_le_ldV P v hL (ld_sub P v hL hT N hN g hg hy)) hy
  rwa [sub_add_cancel] at h



theorem natCast_mem_max {p : ℕ} (hp : (p : 𝓞 F) ∈ v.asIdeal) :
    ((p : ℕ) : v.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 hp
  rw [← Formalism.UG.P.levelaf_valued_algebraMap] at h
  have e : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) =
      (p : v.adicCompletion F) := by rw [map_natCast, map_natCast]
  replace h : Valued.v ((p : ℕ) : v.adicCompletion F) < 1 := by rw [← e]; exact h
  intro h1
  rw [show (((p : ℕ) : v.adicCompletionIntegers F) : v.adicCompletion F) = (p : v.adicCompletion F) from
    by push_cast; rfl] at h1
  exact absurd h1 h.ne

theorem map_one_apply {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (i j : Fin k) :
    f ((1 : Matrix (Fin k) (Fin k) A) i j) = (1 : Matrix (Fin k) (Fin k) B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp



end ParSec

end Bridge

section Facts

open Formalism.MainNotions.Gaps.LG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}






end Facts

end Formalism.MainNotions.Gaps.LevGap
