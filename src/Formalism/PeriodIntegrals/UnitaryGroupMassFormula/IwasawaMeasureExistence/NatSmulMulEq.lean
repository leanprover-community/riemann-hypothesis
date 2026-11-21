import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwaStmt

section
noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology

variable {F : Type} [Field F] [NumberField F]

theorem val_algebraMap_F (v : HeightOneSpectrum (𝓞 F)) (t : F) :
    Valued.v (algebraMap F (v.adicCompletion F) t) = v.valuation F t := by
  rw [algebraMap_adicCompletion]
  simp [valuedAdicCompletion_eq_valuation']

theorem exists_int_near (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
  have hnhds : {y : v.adicCompletion F | Valued.v (y - x) < 1} ∈ 𝓝 x := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨_, hy, ⟨k, rfl⟩⟩ :=
    mem_closure_iff_nhds.mp ((denseRange_algebraMap (K := F) (v := v)) x) _ hnhds
  simp only [Set.mem_ofPred_eq] at hy
  have hk : v.valuation F k ≤ 1 := by
    rw [← val_algebraMap_F]
    calc Valued.v (algebraMap F (v.adicCompletion F) k)
        = Valued.v ((algebraMap F (v.adicCompletion F) k - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap F (v.adicCompletion F) k - x)) (Valued.v x) :=
          Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk 1
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) k -
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) < 1 := by
    rw [← map_sub, val_algebraMap_F, ← Valuation.map_neg, neg_sub]
    simpa using ha
  calc Valued.v (x - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))
      = Valued.v ((x - algebraMap F (v.adicCompletion F) k) + (algebraMap F (v.adicCompletion F) k -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a))) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < 1 := by
      refine max_lt ?_ h2
      rw [← Valuation.map_neg, neg_sub]; exact hy

def toOv (v : HeightOneSpectrum (𝓞 F)) : 𝓞 F →+* Valued.integer (v.adicCompletion F) :=
  ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)).codRestrict _ (fun a => by
    show Valued.v (_ : v.adicCompletion F) ≤ 1
    simp only [RingHom.comp_apply]
    rw [val_algebraMap_F, valuation_of_algebraMap]
    exact intValuation_le_one v a)

theorem toOv_coe (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) :
    ((toOv v a : Valued.integer (v.adicCompletion F)) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem isUnit_integer_iff (v : HeightOneSpectrum (𝓞 F)) (x : Valued.integer (v.adicCompletion F)) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 :=
  (Valuation.integer.integers (Valued.v : Valuation (v.adicCompletion F) _)).isUnit_iff_valuation_eq_one

theorem finite_residue (v : HeightOneSpectrum (𝓞 F)) :
    Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F))) := by
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (Valued.integer (v.adicCompletion F)) :=
    (IsLocalRing.residue _).comp (toOv v)
  have hker : ∀ a ∈ v.asIdeal, φ a = 0 := by
    intro a ha
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, isUnit_integer_iff, toOv_coe, val_algebraMap_F, valuation_of_algebraMap]
    exact ((intValuation_lt_one_iff_mem v a).mpr ha).ne
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  refine Finite.of_surjective ψ ?_
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_int_near v (x : v.adicCompletion F) x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  simp only [ψ, Ideal.Quotient.lift_mk, φ, RingHom.comp_apply]
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, isUnit_integer_iff]
  push_cast [toOv_coe]
  exact ha.ne

theorem compactSpace_integer (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (Valued.integer (v.adicCompletion F)) := by
  rw [Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField]
  refine ⟨?_, ?_, finite_residue v⟩
  · exact (Valued.isClosed_integer (R := v.adicCompletion F)).completeSpace_coe
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))

theorem isCompact_Ov (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have := compactSpace_integer v
  exact isCompact_iff_compactSpace.mpr this

instance compactSpace_Ov (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

def Ohat (F : Type) [Field F] [NumberField F] : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem isOpen_Ohat : IsOpen (Ohat F) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

instance compactSpace_Ov' (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  isCompact_iff_compactSpace.mp (isCompact_Ov v)

theorem isCompact_Ohat : IsCompact (Ohat F) := by
  have hc : Continuous (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have : Ohat F = Set.range (RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v
      exact (x v).2
  rw [this]
  exact isCompact_range hc

instance t2Space_finiteAdeleRing_alt : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open scoped TensorProduct

variable {F E B : Type} [Field F] [Field E] [Algebra F E] [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

def coord : E ⊗[F] B →ₗ[F] (ι → B) :=
  TensorProduct.lift (LinearMap.mk₂ F (fun (e : E) (a : B) => fun k => b.repr e k • a)
    (fun e₁ e₂ a => by funext k; simp [add_smul])
    (fun c e a => by funext k; simp [smul_smul])
    (fun e a₁ a₂ => by funext k; simp [smul_add])
    (fun c e a => by funext k; simp [smul_comm c]))

theorem coord_tmul (e : E) (a : B) : coord b (e ⊗ₜ[F] a) = fun k => b.repr e k • a := by
  simp [coord]

def emb (c : ι → B) : E ⊗[F] B := ∑ i, b i ⊗ₜ[F] c i

theorem coord_emb (c : ι → B) : coord b (emb b c) = c := by
  funext k
  simp only [emb, map_sum, coord_tmul, Finset.sum_apply, Module.Basis.repr_self]
  simp [Finsupp.single_apply]

theorem emb_coord (x : E ⊗[F] B) : emb b (coord b x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [emb]
  | tmul e a =>
    simp only [emb, coord_tmul]
    conv_rhs => rw [← b.sum_repr e]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul]
  | add x y hx hy =>
    have : emb b (coord b (x + y)) = emb b (coord b x) + emb b (coord b y) := by
      simp [emb, map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [this, hx, hy]

theorem coord_injective : Function.Injective (coord b : E ⊗[F] B → ι → B) :=
  Function.LeftInverse.injective (emb_coord b)

theorem coord_mul (x y : E ⊗[F] B) :
    coord b (x * y) = fun k => ∑ i, ∑ j, b.repr (b i * b j) k • (coord b x i * coord b y j) := by
  conv_lhs => rw [← emb_coord b x, ← emb_coord b y]
  simp only [emb, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, coord_tmul]
  funext k
  simp [Finset.sum_apply]

theorem coord_smul (c : F) (x : E ⊗[F] B) : coord b (c • x) = c • coord b x := map_smul _ _ _

theorem coord_tmul_one_mul (a : B) (x : E ⊗[F] B) :
    coord b ((1 ⊗ₜ[F] a) * x) = fun k => a * coord b x k := by
  conv_lhs => rw [← emb_coord b x]
  simp only [emb, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_sum, coord_tmul]
  funext k
  simp [Finset.sum_apply, Module.Basis.repr_self, Finsupp.single_apply]

theorem coord_incl (e : E) :
    coord b (Algebra.TensorProduct.includeLeftRingHom (R := F) (B := B) e) = fun k => algebraMap F B (b.repr e k) := by
  funext k
  simp [Algebra.TensorProduct.includeLeftRingHom_apply, coord_tmul, Algebra.algebraMap_eq_smul_one]

theorem coord_map (σ : E →ₐ[F] E) (x : E ⊗[F] B) :
    coord b (Algebra.TensorProduct.map σ (AlgHom.id F B) x) =
      fun k => ∑ i, b.repr (σ (b i)) k • coord b x i := by
  conv_lhs => rw [← emb_coord b x]
  simp only [emb, map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coord_tmul]
  funext k
  simp [Finset.sum_apply]

section Topology

variable [TopologicalSpace B] [IsTopologicalRing B]

theorem cont_smul {X : Type*} [TopologicalSpace X] (c : F) {h : X → B} (hh : Continuous h) :
    Continuous (fun x => c • h x) := by
  simp_rw [Algebra.smul_def]
  exact continuous_const.mul hh

def CtsA {X : Type*} [TopologicalSpace X] (f : X → E ⊗[F] B) : Prop :=
  Continuous (fun x => coord b (f x))

variable {b}
variable {X : Type*} [TopologicalSpace X]

theorem ctsA_const (y : E ⊗[F] B) : CtsA b (fun _ : X => y) := continuous_const

theorem ctsA_emb {g : X → ι → B} (hg : Continuous g) : CtsA b (fun x => emb b (g x)) := by
  simpa [CtsA, coord_emb] using hg



theorem ctsA_sum {κ : Type*} (s : Finset κ) {f : κ → X → E ⊗[F] B} (hf : ∀ i ∈ s, CtsA b (f i)) :
    CtsA b (fun x => ∑ i ∈ s, f i x) := by
  unfold CtsA
  simp only [map_sum]
  exact continuous_finset_sum _ hf

theorem ctsA_mul {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : CtsA b (fun x => f x * g x) := by
  unfold CtsA
  simp only [coord_mul]
  refine continuous_pi fun k => continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact cont_smul _ (((continuous_apply i).comp hf).mul ((continuous_apply j).comp hg))

theorem ctsA_map (σ : E →ₐ[F] E) {f : X → E ⊗[F] B} (hf : CtsA b f) :
    CtsA b (fun x => Algebra.TensorProduct.map σ (AlgHom.id F B) (f x)) := by
  unfold CtsA
  simp only [coord_map]
  exact continuous_pi fun k => continuous_finset_sum _ fun i _ => cont_smul _ ((continuous_apply i).comp hf)

end Topology

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped TensorProduct

theorem exists_den {K : Type} [Field K] [NumberField K] (x : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, (m : K) * x = algebraMap (𝓞 K) K a := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hN0 : Ideal.absNorm (Ideal.span {s}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hs0
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {s}))
  refine ⟨Ideal.absNorm (Ideal.span {s}), Nat.pos_of_ne_zero hN0, t * a, ?_⟩
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
  have : ((Ideal.absNorm (Ideal.span {s}) : ℕ) : K) = algebraMap (𝓞 K) K t * algebraMap (𝓞 K) K s := by
    rw [← map_mul, ht, map_natCast]
  rw [this, map_mul]
  field_simp

variable {F : Type} [Field F] [NumberField F]

def IntF (f : F) : Prop := algebraMap F (FiniteAdeleRing (𝓞 F) F) f ∈ Ohat F

theorem ohat_mul {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a * c ∈ Ohat F :=
  fun v => by
    show a v * c v ∈ _
    exact mul_mem (ha v) (hc v)

theorem ohat_add {a c : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (hc : c ∈ Ohat F) : a + c ∈ Ohat F :=
  fun v => by
    show a v + c v ∈ _
    exact add_mem (ha v) (hc v)

theorem ohat_neg {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) : -a ∈ Ohat F :=
  fun v => by
    show -(a v) ∈ _
    exact neg_mem (ha v)

theorem ohat_zero : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F :=
  fun v => by
    show (0 : v.adicCompletion F) ∈ _
    exact zero_mem _

theorem ohat_one : (1 : FiniteAdeleRing (𝓞 F) F) ∈ Ohat F :=
  fun v => by
    show (1 : v.adicCompletion F) ∈ _
    exact one_mem _

theorem ohat_sum {κ : Type*} (s : Finset κ) {f : κ → FiniteAdeleRing (𝓞 F) F} (hf : ∀ i ∈ s, f i ∈ Ohat F) :
    ∑ i ∈ s, f i ∈ Ohat F := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ohat_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact ohat_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem ohat_nsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℕ) : m • a ∈ Ohat F := by
  induction m with
  | zero => simpa using ohat_zero
  | succ m ih => rw [succ_nsmul]; exact ohat_add ih ha

theorem ohat_zsmul {a : FiniteAdeleRing (𝓞 F) F} (ha : a ∈ Ohat F) (m : ℤ) : m • a ∈ Ohat F := by
  rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
  · simpa using ohat_nsmul ha k
  · rw [neg_smul]; exact ohat_neg (by simpa using ohat_nsmul ha k)

theorem intF_of_int (a : 𝓞 F) : IntF (algebraMap (𝓞 F) F a) := fun v => by
  show ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) ∈ _
  exact coe_algebraMap_mem (𝓞 F) F v a

theorem exists_den_fin {κ : Type} [Fintype κ] (f : κ → F) :
    ∃ m : ℕ, 0 < m ∧ ∀ i, IntF ((m : F) * f i) := by
  classical
  choose m hm a ha using fun i => exists_den (f i)
  refine ⟨∏ i, m i, Finset.prod_pos fun i _ => hm i, fun i => ?_⟩
  obtain ⟨q, hq⟩ : m i ∣ ∏ j, m j := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  have : ((∏ j, m j : ℕ) : F) * f i = algebraMap (𝓞 F) F ((q : 𝓞 F) * a i) := by
    rw [hq, map_mul, ← ha i]; push_cast; ring
  rw [this]; exact intF_of_int _

section Coord

variable {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def IntC (x : E ⊗[F] Af) : Prop := ∀ k, coord b x k ∈ Ohat F

variable {b}

theorem intC_add {x y : E ⊗[F] Af} (hx : IntC b x) (hy : IntC b y) : IntC b (x + y) := fun k => by
  rw [map_add]; exact ohat_add (hx k) (hy k)


theorem intC_sum {κ : Type*} (s : Finset κ) {f : κ → E ⊗[F] Af} (hf : ∀ i ∈ s, IntC b (f i)) :
    IntC b (∑ i ∈ s, f i) := fun k => by
  rw [map_sum, Finset.sum_apply]
  exact ohat_sum s fun i hi => hf i hi k

theorem smul_eq_algebraMap_mul (c : F) (a : Af) : c • a = algebraMap F Af c * a := Algebra.smul_def c a

theorem exists_den_mul (b : Module.Basis ι F E) :
    ∃ m : ℕ, 0 < m ∧ ∀ x y : E ⊗[F] Af, IntC b x → IntC b y → IntC b (m • (x * y)) := by
  obtain ⟨m, hm, h⟩ := exists_den_fin (fun p : ι × ι × ι => b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨m, hm, fun x y hx hy k => ?_⟩
  rw [map_nsmul, coord_mul]
  simp only [Pi.smul_apply, Finset.smul_sum]
  refine ohat_sum _ fun i _ => ohat_sum _ fun j _ => ?_
  rw [smul_eq_algebraMap_mul, nsmul_eq_mul, ← mul_assoc]
  have h1 : (m : Af) * algebraMap F Af (b.repr (b i * b j) k) = algebraMap F Af ((m : F) * b.repr (b i * b j) k) := by
    simp
  rw [h1]
  exact ohat_mul (h (i, j, k)) (ohat_mul (hx i) (hy j))


end Coord

end PI.IwaMeasEx.Wau

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

abbrev inclV (w : Fin n → E) : Fin n → E ⊗[F] Af := fun i => Formalism.UG.inclE (F := F) Af (w i)

theorem inclV_mem {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E} (hw : w ∈ L) :
    inclV (F := F) w ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨w, hw⟩, rfl⟩

theorem one_tmul_mem_intAf {c : Af} (hc : c ∈ Ohat F) : ((1 : E) ⊗ₜ[F] c) ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)

theorem exists_nat_smul_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℕ, 0 < m ∧ m • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simpa using L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, h1, hx⟩ := hx
    obtain ⟨m2, h2, hy⟩ := hy
    refine ⟨m1 * m2, Nat.mul_pos h1 h2, ?_⟩
    have : (m1 * m2) • (x + y) = m2 • (m1 • x) + m1 • (m2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m2 m1]
    rw [this]
    exact L.add_mem (nsmul_mem hx m2) (nsmul_mem hy m1)
  | smul e x _ hx =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨t, ht, a, ha⟩ := exists_den e
    refine ⟨t * m, Nat.mul_pos ht hm, ?_⟩
    have : (t * m) • (e • x) = a • (m • x) := by
      rw [← algebraMap_smul E a (m • x), ← ha, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, smul_smul]
      congr 1
      push_cast; ring
    rw [this]
    exact L.smul_mem a hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_lower (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ d : ℕ, 0 < d ∧ ∀ y : Fin n → E ⊗[F] Af, (∀ j, IntC b (y j)) → d • y ∈ lamAf (F := F) L := by
  classical
  choose m hm hmL using fun p : Fin n × ι => exists_nat_smul_mem L hL (Pi.single p.1 (b p.2))
  refine ⟨∏ p, m p, Finset.prod_pos fun p _ => hm p, fun y hy => ?_⟩
  have key : ∀ (j : Fin n) (k : ι) (c : Af), c ∈ Ohat F →
      (∏ p, m p) • Pi.single j (b k ⊗ₜ[F] c) ∈ lamAf (F := F) L := by
    intro j k c hc
    obtain ⟨q, hq⟩ : m (j, k) ∣ ∏ p, m p := Finset.dvd_prod_of_mem m (Finset.mem_univ (j, k))
    have hw : (∏ p, m p) • (Pi.single j (b k) : Fin n → E) ∈ L := by
      rw [hq, mul_comm, mul_smul]; exact nsmul_mem (hmL (j, k)) q
    have heq : (∏ p, m p) • (Pi.single j (b k ⊗ₜ[F] c) : Fin n → E ⊗[F] Af) =
        (⟨(1 : E) ⊗ₜ[F] c, one_tmul_mem_intAf hc⟩ : IntAf F E) •
          inclV (F := F) ((∏ p, m p) • (Pi.single j (b k) : Fin n → E)) := by
      funext i
      by_cases hij : i = j
      · subst hij
        simp only [Pi.smul_apply, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one]
        rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.smul_tmul']
        simp only [inclV, Pi.smul_apply, Pi.single_eq_same, Formalism.UG.inclE,
          Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      · simp [Pi.single_eq_of_ne hij, Subring.smul_def, Formalism.UG.inclE, inclV]
    rw [heq]
    exact Submodule.smul_mem _ _ (inclV_mem hw)
  have hy' : y = ∑ j, ∑ k, (Pi.single j (b k ⊗ₜ[F] coord b (y j) k) : Fin n → E ⊗[F] Af) := by
    conv_lhs => rw [← Finset.univ_sum_single y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := emb_coord b (y j)
    simp only [emb] at h1
    conv_lhs => rw [← h1]
    exact map_sum (AddMonoidHom.single (fun _ : Fin n => E ⊗[F] Af) j) _ _
  rw [hy', Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Finset.smul_sum]
  exact Submodule.sum_mem _ fun k _ => key j k _ (hy j k)

theorem exists_den_lattice (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ l ∈ L, ∀ j k, IntF ((D : F) * b.repr (l j) k) := by
  classical
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨p, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  obtain ⟨D, hD, h⟩ := exists_den_fin (fun q : Fin p × Fin n × ι => b.repr ((s q.1 : Fin n → E) q.2.1) q.2.2)
  refine ⟨D, hD, fun l hl j k => ?_⟩
  have hmem : (⟨l, hl⟩ : L) ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hmem
  have hl' : l = ∑ t, c t • (s t : Fin n → E) := by
    have := congrArg Subtype.val hc
    simpa [Submodule.coe_sum] using this.symm
  have : (D : F) * b.repr (l j) k = ∑ t, c t • ((D : F) * b.repr ((s t : Fin n → E) j) k) := by
    rw [hl']
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [← b.coord_apply, map_sum]
    simp only [map_zsmul, b.coord_apply, Finset.mul_sum, mul_smul_comm, Finsupp.smul_apply]
  unfold IntF
  rw [this, map_sum]
  exact ohat_sum _ fun t _ => by rw [map_zsmul]; exact ohat_zsmul (h (t, j, k)) _

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Formalism.MainNotions.S
open scoped TensorProduct

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

local notation "Af" => FiniteAdeleRing (𝓞 F) F

def ohatL (L : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → E ⊗[F] Af) :=
  AddSubgroup.closure {y | ∃ c ∈ Ohat F, ∃ l ∈ L, y = ((1 : E) ⊗ₜ[F] c) • fun i => Formalism.UG.inclE (F := F) Af (l i)}

theorem smul_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {a : E ⊗[F] Af} (ha : a ∈ IntAf F E) :
    ∀ y ∈ ohatL (F := F) L, a • y ∈ ohatL (F := F) L := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    intro y hy
    rcases hx with ⟨⟨o, ho⟩, rfl⟩ | ⟨⟨c', hc'⟩, rfl⟩
    · obtain ⟨o', rfl⟩ := ho
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨c, hc, o' • l, L.smul_mem o' hl, ?_⟩
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply,
          Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← algebraMap_smul E o' (l i)]
      | zero => rw [smul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
      | neg y _ hy => rw [smul_neg]; exact neg_mem hy
    · induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, hc, l, hl, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨c' * c, ohat_mul hc' hc, l, hl, ?_⟩
        rw [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
      | neg y _ hy => rw [smul_neg]; exact neg_mem hy
  | zero => intro y _; rw [zero_smul]; exact zero_mem _
  | one => intro y hy; rwa [one_smul]
  | add x x' _ _ hx hx' => intro y hy; rw [add_smul]; exact add_mem (hx y hy) (hx' y hy)
  | neg x _ hx => intro y hy; rw [neg_smul]; exact neg_mem (hx y hy)
  | mul x x' _ _ hx hx' => intro y hy; rw [mul_smul]; exact hx _ (hx' y hy)

theorem lamAf_le_ohatL (L : Submodule (𝓞 E) (Fin n → E)) {y : Fin n → E ⊗[F] Af}
    (hy : y ∈ lamAf (F := F) L) : y ∈ ohatL (F := F) L := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨1, ohat_one, l, hl, ?_⟩
    rw [← Algebra.TensorProduct.one_def, one_smul]
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => rw [Subring.smul_def]; exact smul_ohatL L a.2 x hx

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem intC_zero {b : Module.Basis ι F E} : IntC b (0 : E ⊗[F] Af) := fun k => by
  rw [map_zero]; exact ohat_zero

theorem intC_neg {b : Module.Basis ι F E} {x : E ⊗[F] Af} (hx : IntC b x) : IntC b (-x) := fun k => by
  rw [map_neg]; exact ohat_neg (hx k)

theorem exists_upper (b : Module.Basis ι F E) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) :
    ∃ D : ℕ, 0 < D ∧ ∀ y ∈ lamAf (F := F) L, ∀ j, IntC b (D • y j) := by
  obtain ⟨D, hD, h⟩ := exists_den_lattice b L hfg
  refine ⟨D, hD, fun y hy => ?_⟩
  let G : AddSubgroup (Fin n → E ⊗[F] Af) :=
    { carrier := {y | ∀ j, IntC b (D • y j)}
      add_mem' := fun {y z} hy hz j => by
        simp only [Set.mem_ofPred_eq, Pi.add_apply, smul_add] at *
        exact intC_add (hy j) (hz j)
      zero_mem' := fun j => by simpa using intC_zero
      neg_mem' := fun {y} hy j => by
        simp only [Set.mem_ofPred_eq, Pi.neg_apply, smul_neg] at *
        exact intC_neg (hy j) }
  have hle : ohatL (F := F) L ≤ G := by
    unfold ohatL
    rw [AddSubgroup.closure_le]
    rintro y ⟨c, hc, l, hl, rfl⟩ j k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [map_nsmul, coord_tmul_one_mul]
    simp only [Formalism.UG.inclE]
    rw [coord_incl]
    simp only [Pi.smul_apply]
    have : D • (c * algebraMap F Af (b.repr (l j) k)) = c * algebraMap F Af ((D : F) * b.repr (l j) k) := by
      rw [nsmul_eq_mul, map_mul, map_natCast]; ring
    rw [this]
    exact ohat_mul hc (h l hl j k)
  exact hle (lamAf_le_ohatL L hy)

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {B : Type} [CommRing B] [Algebra F B]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)

theorem emb_add (c c' : ι → B) : emb b (c + c') = emb b c + emb b c' := by
  apply coord_injective b; rw [map_add, coord_emb, coord_emb, coord_emb]

theorem emb_zero : emb b (0 : ι → B) = 0 := by
  apply coord_injective b; rw [map_zero, coord_emb]

theorem emb_neg (c : ι → B) : emb b (-c) = -emb b c := by
  apply coord_injective b; rw [map_neg, coord_emb, coord_emb]

theorem emb_sub (c c' : ι → B) : emb b (c - c') = emb b c - emb b c' := by
  apply coord_injective b; rw [map_sub, coord_emb, coord_emb, coord_emb]

theorem emb_nsmul (N : ℕ) (c : ι → B) : emb b (N • c) = N • emb b c := by
  apply coord_injective b; rw [map_nsmul, coord_emb, coord_emb]

theorem isClosed_eqA [TopologicalSpace B] [IsTopologicalRing B] [T2Space B] {X : Type*} [TopologicalSpace X]
    {f g : X → E ⊗[F] B} (hf : CtsA b f) (hg : CtsA b g) : IsClosed {p | f p = g p} := by
  have : {p | f p = g p} = {p | coord b (f p) = coord b (g p)} := by
    ext p; exact (coord_injective b).eq_iff.symm
  rw [this]; exact isClosed_eq hf hg

end General

theorem stab_mem {I : AutInst} {x : I.Gf} (hx : x ∈ I.Kset) {w : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hw : w ∈ I.Lf) : I.fmat x *ᵥ w ∈ I.Lf := (hx w).mp hw

namespace Cpt

variable (I : AutInst)

abbrev ιb : Type := Fin (Module.finrank I.F I.E)

abbrev bs : Module.Basis (ιb I) I.F I.E := Module.finBasis I.F I.E

abbrev Co : Type := Fin I.n → Fin I.n → ιb I → Af I.F

def matOf (P : Co I) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun i j => emb (bs I) (P i j)

theorem mulVec_mem_Lf (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ l ∈ I.L, M *ᵥ inclV (F := I.F) l ∈ I.Lf) : ∀ y ∈ I.Lf, M *ᵥ y ∈ I.Lf := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨⟨l, hl⟩, rfl⟩ := hx; exact hM l hl
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul a x _ hx =>
    rw [Subring.smul_def, Matrix.mulVec_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ a hx

theorem isClosed_LfC (d : ℕ) (hd : 0 < d)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf) :
    IsClosed {w : Fin I.n → ιb I → Af I.F | (fun j => emb (bs I) (w j)) ∈ I.Lf} := by
  let S : AddSubgroup (Fin I.n → ιb I → Af I.F) :=
    { carrier := {w | (fun j => emb (bs I) (w j)) ∈ I.Lf}
      add_mem' := fun {w w'} hw hw' => by
        have : (fun j => emb (bs I) ((w + w') j)) = (fun j => emb (bs I) (w j)) + fun j => emb (bs I) (w' j) := by
          funext j; simp [emb_add]
        show (fun j => emb (bs I) ((w + w') j)) ∈ I.Lf
        rw [this]; exact I.Lf.add_mem hw hw'
      zero_mem' := by
        show (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) ∈ I.Lf
        have : (fun j => emb (bs I) ((0 : Fin I.n → ιb I → Af I.F) j)) = 0 := by
          funext j; simp [emb_zero]
        rw [this]; exact I.Lf.zero_mem
      neg_mem' := fun {w} hw => by
        have : (fun j => emb (bs I) ((-w) j)) = -fun j => emb (bs I) (w j) := by
          funext j; simp [emb_neg]
        show (fun j => emb (bs I) ((-w) j)) ∈ I.Lf
        rw [this]; exact I.Lf.neg_mem hw }
  have hnhds : (S : Set (Fin I.n → ιb I → Af I.F)) ∈ 𝓝 0 := by
    let U := {w : Fin I.n → ιb I → Af I.F | ∀ j k, algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k ∈ Ohat I.F}
    have hU : IsOpen U := by
      have : U = ⋂ j, ⋂ k, (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) ⁻¹' Ohat I.F := by
        ext w; simp [U]
      rw [this]
      refine isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun k => ?_
      have hc : Continuous (fun w : Fin I.n → ιb I → Af I.F => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k) :=
        continuous_const.mul ((continuous_apply k).comp (continuous_apply j))
      exact hc.isOpen_preimage _ isOpen_Ohat
    have h0 : (0 : Fin I.n → ιb I → Af I.F) ∈ U := fun j k => by simpa using ohat_zero
    refine Filter.mem_of_superset (hU.mem_nhds h0) fun w hw => ?_
    have hd0 : (d : I.F) ≠ 0 := by exact_mod_cast hd.ne'
    have := hlow (fun j => emb (bs I) (fun k => algebraMap I.F (Af I.F) ((d : I.F)⁻¹) * w j k))
      (fun j k => by rw [coord_emb]; exact hw j k)
    show (fun j => emb (bs I) (w j)) ∈ I.Lf
    convert this using 1
    funext j
    rw [Pi.smul_apply, ← emb_nsmul]
    congr 1; funext k
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul,
      mul_inv_cancel₀ hd0, map_one, one_mul]
  exact AddSubgroup.isClosed_of_isOpen S (S.isOpen_of_mem_nhds hnhds)

theorem intC_single (D1 : ℕ) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F))) (j : Fin I.n) :
    ∀ i, IntC (bs I) ((Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F) i) := by
  intro i
  by_cases hij : i = j
  · subst hij; rw [Pi.single_eq_same]; exact h1
  · rw [Pi.single_eq_of_ne hij]; exact intC_zero

theorem bound_K (d D D1 : ℕ)
    (hlow : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ j, IntC (bs I) (y j)) → d • y ∈ I.Lf)
    (hup : ∀ y ∈ I.Lf, ∀ j, IntC (bs I) (D • y j)) (h1 : IntC (bs I) (D1 • (1 : I.E ⊗[I.F] Af I.F)))
    {x : I.Gf} (hx : x ∈ I.Kset) (i j : Fin I.n) : IntC (bs I) ((D * (d * D1)) • I.fmat x i j) := by
  have hl := hlow _ (intC_single I D1 h1 j)
  have hxl := stab_mem hx hl
  have := hup _ hxl i
  have e : (I.fmat x *ᵥ (d • (Pi.single j (D1 • (1 : I.E ⊗[I.F] Af I.F)) : Fin I.n → I.E ⊗[I.F] Af I.F))) i =
      (d * D1) • I.fmat x i j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_smul_comm, smul_smul, mul_comm]
    ring
  rw [e, smul_smul] at this
  exact this

end Cpt

end PI.IwaMeasEx.Wau

end
end

section
noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

abbrev Jf : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

theorem mem_Bx {N : ℕ} (hN : 0 < N) {a : Af I.F} (ha : N • a ∈ Ohat I.F) : a ∈ Bx I N := by
  refine ⟨N • a, ha, ?_⟩
  have hN0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
  simp only
  rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, inv_mul_cancel₀ hN0,
    map_one, one_mul]

def Cset (N : ℕ) : Set (Co I × Co I) :=
  {p | (∀ i j k, p.1 i j k ∈ Bx I N ∧ p.2 i j k ∈ Bx I N) ∧
    matOf I p.1 * matOf I p.2 = 1 ∧ matOf I p.2 * matOf I p.1 = 1 ∧
    Formalism.UG.cT (sg I) (matOf I p.1) * Jf I * matOf I p.1 = Jf I ∧
    (∀ l ∈ I.L, matOf I p.1 *ᵥ inclV (F := I.F) l ∈ I.Lf) ∧
    (∀ l ∈ I.L, matOf I p.2 *ᵥ inclV (F := I.F) l ∈ I.Lf)}

def psi (N : ℕ) (p : Cset I N) : I.Gf :=
  ⟨⟨matOf I p.1.1, matOf I p.1.2, p.2.2.1, p.2.2.2.1⟩, p.2.2.2.2.1⟩

end Cpt

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

end Cpt

end PI.IwaMeasEx.Wau

end
end
