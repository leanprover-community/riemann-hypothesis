import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CycleListPermInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderTensorPadicIsAzumayaAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem one_tmul_mem_locOrder_of_nsmul_mem : ∀ {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) (b : B) (m : ℕ),
    0 < m → (m : B) * b ∈ OB → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ m →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b ∈ locOrder ℓ OB := by
  intro B _ _ OB b m hm hmb ℓ _ hℓ
  have hunit : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).mpr hℓ)
  obtain ⟨u, hu⟩ := hunit
  have hgen : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b) ∈ locOrder ℓ OB :=
    Algebra.subset_adjoin ⟨_, hmb, rfl⟩
  have key : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b)) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have : ((m : B) * b) = (m : ℚ) • b := by rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    have h1 : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = (m : ℚ_[ℓ]) := by rw [hu]; simp
    have h2 : (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = 1 := by
      rw [← PadicInt.coe_mul]; simp
    rw [h1] at h2
    rw [Algebra.smul_def]
    simp only [map_natCast]
    rw [PadicInt.algebraMap_apply]
    linear_combination h2.symm
  rw [key]
  exact Subalgebra.smul_mem _ hgen _

end GlobalTheory
end

section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem cenOrder_finite : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := by
  intro F _ _ ℓ _
  classical
  let f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F := fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top
  have hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x := by
    rintro _ ⟨a, -, rfl⟩
    have h1 : IsIntegral ℤ ((a : F)) := NumberField.RingOfIntegers.isIntegral_coe a
    have h2 : IsIntegral ℤ (f a) := by
      have := h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)
      simpa [f] using this
    exact h2.tower_top
  have hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint
  have heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      let A := Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))
      let N : Submodule ℤ (NumberField.RingOfIntegers F) :=
        { carrier := {x | f x ∈ A}
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq, f, map_add, TensorProduct.tmul_add] at hx hy ⊢
            exact A.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]
            exact A.zero_mem
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢
            have : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F)) := by
              rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
            rw [this]
            exact A.toSubring.zsmul_mem hx c }
      have hsN : (s : Set _) ⊆ N := fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have : a ∈ N := by
        have := Submodule.span_le.mpr hsN
        rw [hs] at this
        exact this Submodule.mem_top
      exact this
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
  rw [heq]
  exact hfin

end GlobalTheory
end

section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_order_integers_mul_finite_index (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] (OB : Subring B) (hfin : Module.Finite ℤ OB)
    (hsat : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) :
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  classical
  let f : NumberField.RingOfIntegers F →ₐ[ℤ] B :=
    ((algebraMap F B).comp (algebraMap (NumberField.RingOfIntegers F) F)).toIntAlgHom
  let g : OB →ₐ[ℤ] B := OB.subtype.toIntAlgHom
  have hc : ∀ a b, Commute (f a) (g b) := fun a b => Algebra.commutes _ _
  let L := Algebra.TensorProduct.lift f g hc
  have hL : ∀ a b, L (a ⊗ₜ b) = f a * g b := fun a b => Algebra.TensorProduct.lift_tmul f g hc a b

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (NumberField.RingOfIntegers F)).FG)
  choose m hm0 hm using fun a : NumberField.RingOfIntegers F => hsat (f a)
  let N : ℕ := ∏ a ∈ s, m a
  have hN0 : 0 < N := Finset.prod_pos fun a _ => hm0 a
  have hnat : ∀ (k : ℕ) (y : B), y ∈ OB → (k : B) * y ∈ OB := fun k y hy =>
    OB.mul_mem (natCast_mem OB k) hy
  let P : Submodule ℤ (NumberField.RingOfIntegers F) :=
    { carrier := {a | (N : B) * f a ∈ OB}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, map_add, mul_add] at *
        exact OB.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro n a ha
        simp only [Set.mem_setOf_eq, map_zsmul, mul_smul_comm] at *
        exact OB.zsmul_mem ha n }
  have hsP : (s : Set (NumberField.RingOfIntegers F)) ⊆ SetLike.coe P := by
    intro a ha
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
    show (N : B) * f a ∈ OB
    have : (N : B) = (k : B) * (m a : B) := by
      rw [show N = m a * k from hk, Nat.cast_mul, (Nat.cast_commute _ _).eq]
    rw [this, mul_assoc]
    exact hnat k _ (hm a)
  have hP : ∀ a, (N : B) * f a ∈ OB := by
    intro a
    have : a ∈ Submodule.span ℤ (s : Set _) := by rw [hs]; trivial
    exact (Submodule.span_le.mpr hsP) this
  refine ⟨L.toRingHom.range, ?_, ?_, ?_, N, hN0, ?_⟩
  · intro b hb
    refine ⟨1 ⊗ₜ ⟨b, hb⟩, ?_⟩
    show L _ = b
    rw [hL]; simp [f, g]
  · intro a
    refine ⟨a ⊗ₜ 1, ?_⟩
    show L _ = _
    rw [hL]; simp [f, g]
  · haveI : Module.Finite ℤ OB := hfin
    haveI : Module.Finite ℤ (NumberField.RingOfIntegers F ⊗[ℤ] OB) := Module.Finite.tensorProduct _ _ _
    exact Module.Finite.of_surjective (L.toRingHom.rangeRestrict.toIntAlgHom.toLinearMap)
      (RingHom.rangeRestrict_surjective _)
  · rintro x ⟨t, rfl⟩
    show (N : B) * L t ∈ OB
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hL, ← mul_assoc]
      exact OB.mul_mem (hP a) b.2
    | add t u ht hu =>
      rw [map_add, mul_add]
      exact OB.add_mem ht hu

end GlobalTheory
end

section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_order_containing_integers : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ Λ : Subring B, OB ≤ Λ ∧ (∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ) ∧
      Module.Finite ℤ Λ ∧ ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Λ, (N : B) * x ∈ OB := by
  first | (exact @GlobalTheory.exists_order_integers_mul_finite_index) | (exact GlobalTheory.exists_order_integers_mul_finite_index) | (intros; apply GlobalTheory.exists_order_integers_mul_finite_index  <;> assumption)
end

section
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem tmul_smul_eq_cenMap_mul {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ_[ℓ]) (c : F) (v : B) :
    q ⊗ₜ[ℚ] (c • v) = cenMap ℓ F B (q ⊗ₜ c) * ((1 : ℚ_[ℓ]) ⊗ₜ v) := by
  rw [cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]

def combMap {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B) :
    (Fin d → ℚ_[ℓ] ⊗[ℚ] F) →ₗ[ℚ_[ℓ]] ℚ_[ℓ] ⊗[ℚ] B where
  toFun c := ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)
  map_add' c c' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_mul_assoc]

theorem combMap_apply {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Fin d → B)
    (c : Fin d → ℚ_[ℓ] ⊗[ℚ] F) :
    combMap ℓ v c = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := rfl

theorem combMap_surjective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ} (v : Module.Basis (Fin d) F B) :
    Function.Surjective (combMap (F := F) ℓ v) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul q b =>
    rw [← v.sum_repr b, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ⟨Pi.single i (q ⊗ₜ[ℚ] v.repr b i), ?_⟩
    rw [combMap_apply, Finset.sum_eq_single i
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]) (by simp),
      Pi.single_eq_same, ← tmul_smul_eq_cenMap_mul]
  | add x y hx hy => exact add_mem hx hy

theorem combMap_injective {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B] (ℓ : ℕ) [Fact ℓ.Prime] {d : ℕ}
    (v : Module.Basis (Fin d) F B) : Function.Injective (combMap (F := F) ℓ v) := by
  haveI : FiniteDimensional ℚ B := Module.Finite.trans F B
  have hdim : Module.finrank ℚ_[ℓ] (Fin d → ℚ_[ℓ] ⊗[ℚ] F) = Module.finrank ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) := by
    rw [Module.finrank_pi_fintype, Module.finrank_baseChange, Module.finrank_baseChange,
      ← Module.finrank_mul_finrank ℚ F B, Module.finrank_eq_card_basis v]
    simp [mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 (combMap_surjective ℓ v)

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

theorem exists_basis_mem {F B : Type} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (Λ : Subring B) (hspan : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) :
    ∃ v : Module.Basis (Fin (Module.finrank F B)) F B, ∀ i, v i ∈ Λ := by
  let e := Module.finBasis F B
  choose m hm hmΛ using hspan
  let u : Fin (Module.finrank F B) → Fˣ := fun i =>
    Units.mk0 (m (e i) : F) (Nat.cast_ne_zero.2 (hm (e i)).ne')
  refine ⟨e.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply, Units.smul_def]
  have h : (u i : F) • e i = (m (e i) : B) * e i := by
    simp [u, Algebra.smul_def]
  rw [h]
  exact hmΛ _

theorem exists_den {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    (Λ : Subring B) (hfin : Module.Finite ℤ Λ) {ι : Type} [Fintype ι] (v : Module.Basis ι F B) :
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i) := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨D, hD, hDs⟩ := GlobalTheory.SepModel.exists_nat_integral
    (Finset.univ.image fun p : s × ι => v.repr ((p.1 : Λ) : B) p.2)
  refine ⟨D, hD, fun x hx => ?_⟩
  let P : Submodule ℤ Λ :=
    { carrier := {y | ∀ i, IsIntegral ℤ ((D : F) * v.repr (y : B) i)}
      add_mem' := by
        intro y z hy hz i
        simp only [Set.mem_setOf_eq, Subring.coe_add, map_add, Finsupp.add_apply, mul_add] at hy hz ⊢
        exact (hy i).add (hz i)
      zero_mem' := by
        intro i
        simp
        exact isIntegral_zero
      smul_mem' := by
        intro c y hy i
        simp only [Set.mem_setOf_eq] at hy ⊢
        have h2 : v.repr ((c • y : Λ) : B) i = (c : F) * v.repr (y : B) i := by
          rw [show ((c • y : Λ) : B) = c • (y : B) from rfl, map_zsmul, Finsupp.smul_apply,
            zsmul_eq_mul]
        have hc : IsIntegral ℤ (c : F) := by
          simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := c))
        rw [h2, mul_left_comm]
        exact hc.mul (hy i) }
  have hsP : (s : Set Λ) ⊆ P := fun y hy i =>
    hDs _ (Finset.mem_image.2 ⟨(⟨y, hy⟩, i), Finset.mem_univ _, rfl⟩)
  have hmem : (⟨x, hx⟩ : Λ) ∈ P := by
    have h := Submodule.span_le.mpr hsP
    rw [hs] at h
    exact h Submodule.mem_top
  exact hmem

end GlobalTheory.LocMatrix

namespace GlobalTheory.LocMatrix

theorem exists_coeffs {F B : Type} [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] (ℓ : ℕ) [Fact ℓ.Prime] (Λ : Subring B) {d : ℕ}
    (v : Module.Basis (Fin d) F B) (D : ℕ)
    (hD : ∀ x ∈ Λ, ∀ i, IsIntegral ℤ ((D : F) * v.repr x i)) (hℓ : ¬ ℓ ∣ D)
    (z : ℚ_[ℓ] ⊗[ℚ] B) (hz : z ∈ locOrder ℓ Λ) :
    ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i) := by
  let S : Submodule ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) :=
    { carrier := {z | ∃ c : Fin d → cenOrder ℓ F, z = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ v i)}
      add_mem' := by
        rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
        exact ⟨c + c', by simp [add_mul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r _ ⟨c, rfl⟩
        refine ⟨r • c, ?_⟩
        simp only [Pi.smul_apply, Subalgebra.coe_smul, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul ℚ_[ℓ] r ((c i : cenOrder ℓ F) : ℚ_[ℓ] ⊗[ℚ] F), map_smul, smul_mul_assoc,
          algebraMap_smul] }
  have gen : ∀ x ∈ Λ, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x ∈ S := by
    intro x hx
    refine ⟨fun i => ⟨_, GlobalTheory.SepModel.tmul_mem_cenOrder ℓ hℓ (hD x hx i)⟩, ?_⟩
    conv_lhs => rw [← v.sum_repr x, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact tmul_smul_eq_cenMap_mul ℓ 1 _ _
  have hz' : z ∈ Subalgebra.toSubmodule (locOrder ℓ Λ) := hz
  rw [locOrder, Algebra.adjoin_eq_span] at hz'
  have hcl : (Submonoid.closure ((fun b : B => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' (Λ : Set B)) :
      Set (ℚ_[ℓ] ⊗[ℚ] B)) ⊆ S := by
    intro y hy
    have hy' : y ∈ Λ.toSubmonoid.map
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] B) := by
      refine (Submonoid.closure_le.2 ?_) hy
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hy'
    exact gen x hx
  exact Submodule.span_le.2 hcl hz'

theorem locOrder_free : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  intro F B _ _ _ _ _ _ _ Λ hΛ hfin hspan
  obtain ⟨v, hvΛ⟩ := exists_basis_mem (F := F) Λ hspan
  obtain ⟨D, hD, hDΛ⟩ := exists_den Λ hfin v
  refine ⟨D, hD, fun ℓ _ hℓ => ?_⟩
  letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
  let w : Fin (Module.finrank F B) → locOrder ℓ Λ := fun i =>
    ⟨(1 : ℚ_[ℓ]) ⊗ₜ v i, Algebra.subset_adjoin ⟨_, hvΛ i, rfl⟩⟩
  have hsmul : ∀ (c : cenOrder ℓ F) (x : locOrder ℓ Λ),
      ((c • x : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) = cenMap ℓ F B c * x := fun c x => rfl
  have hsum : ∀ c : Fin (Module.finrank F B) → cenOrder ℓ F,
      ((∑ i, c i • w i : locOrder ℓ Λ) : ℚ_[ℓ] ⊗[ℚ] B) =
        combMap (F := F) ℓ v (fun i => (c i : ℚ_[ℓ] ⊗[ℚ] F)) := by
    intro c
    rw [AddSubmonoidClass.coe_finset_sum, combMap_apply]
    exact Finset.sum_congr rfl fun i _ => hsmul _ _
  have hli : LinearIndependent (cenOrder ℓ F) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 : combMap (F := F) ℓ v (fun i => (g i : ℚ_[ℓ] ⊗[ℚ] F)) = combMap (F := F) ℓ v 0 := by
      rw [← hsum, hg, map_zero]
      rfl
    exact Subtype.ext (congrFun (combMap_injective ℓ v h0) i)
  have hsp : ⊤ ≤ Submodule.span (cenOrder ℓ F) (Set.range w) := by
    rintro ⟨z, hz⟩ -
    obtain ⟨c, hc⟩ := exists_coeffs ℓ Λ v D hDΛ hℓ z hz
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hsum c).trans hc.symm)⟩
  haveI : Nontrivial (ℚ_[ℓ] ⊗[ℚ] F) := by
    apply Module.nontrivial_of_finrank_pos (R := ℚ_[ℓ])
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  let bas := Module.Basis.mk hli hsp
  exact ⟨Module.Free.of_basis bas, by rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]⟩

end GlobalTheory.LocMatrix
end
end

section
open scoped TensorProduct
open GlobalTheory.LKInvGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderTensorPadic_free_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [FiniteDimensional F B] (Λ : Subring B)
    (hΛ : ∀ a : NumberField.RingOfIntegers F, algebraMap F B (a : F) ∈ Λ),
    Module.Finite ℤ Λ → (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      letI := GlobalTheory.LocMatrix.cenAlgebra ℓ F B Λ hΛ
      Module.Free (cenOrder ℓ F) (locOrder ℓ Λ) ∧
        Module.finrank (cenOrder ℓ F) (locOrder ℓ Λ) = Module.finrank F B := by
  first | (exact @GlobalTheory.LocMatrix.locOrder_free) | (exact GlobalTheory.LocMatrix.locOrder_free) | (intros; apply GlobalTheory.LocMatrix.locOrder_free  <;> assumption)
end

section
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_base_change : ∀ (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ], IsAzumaya S (S ⊗[A] Λ) := by
  first | (exact @GlobalTheory.isAzumaya_baseChange) | (exact GlobalTheory.isAzumaya_baseChange) | (intros; apply GlobalTheory.isAzumaya_baseChange <;> assumption)
end

section
open scoped TensorProduct
open Function

namespace GlobalTheory

theorem exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A],
      ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A),
        (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  intro ℓ _ A _ _ _
  classical
  have : HenselianLocalRing ℤ_[ℓ] := henselianLocalRing_of_henselianRing ℤ_[ℓ]
  have := finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[ℓ] A
  letI := Fintype.ofFinite (MaximalSpectrum A)
  obtain ⟨e, he, H⟩ := exists_completeOrthogonalIdempotents_of_henselian ℤ_[ℓ] A
  refine ⟨MaximalSpectrum A, inferInstance, fun q ↦ Ideal.span {1 - e q}, fun q ↦ ?_, ?_, ?_⟩
  · have := q.isMaximal
    exact isLocalRing_quotient_one_sub (he.idem q) q.asIdeal (H q)
  · intro i j hij
    change IsCoprime (Ideal.span {1 - e i}) (Ideal.span {1 - e j})
    rw [Ideal.isCoprime_span_singleton_iff]
    have h0 : e i * e j = 0 := he.ortho hij
    exact ⟨1, e i, by linear_combination (-1 : A) * h0⟩
  · refine eq_bot_iff.2 fun x hx ↦ ?_
    rw [Submodule.mem_iInf] at hx
    rw [Ideal.mem_bot, ← one_mul x, ← he.complete, Finset.sum_mul]
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (hx q)
    rw [← hw]
    linear_combination (-w) * (he.idem q).eq

end GlobalTheory
end

section
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], ∃ (ι : Type) (_ : Fintype ι) (I : ι → Ideal A), (∀ i, IsLocalRing (A ⧸ I i)) ∧ Pairwise (IsCoprime on I) ∧ ⨅ i, I i = ⊥ := by
  first | (exact @GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (exact GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt) | (intros; apply GlobalTheory.exists_isLocalRing_quotient_pairwise_isCoprime_iInf_eq_bot_padicInt  <;> assumption)
end

section
open scoped TensorProduct
open Function

namespace GlobalTheory

noncomputable def crtAlgEquiv (A : Type) [CommRing A] (ι : Type) [Fintype ι] (I : ι → Ideal A)
    (hI : Pairwise (IsCoprime on I)) (hbot : ⨅ i, I i = ⊥) : A ≃ₐ[A] (Π i, A ⧸ I i) :=
  AlgEquiv.ofRingEquiv (f := (RingEquiv.quotientBot A).symm.trans
    ((Ideal.quotEquivOfEq hbot.symm).trans (Ideal.quotientInfRingEquivPiQuotient I hI)))
    (fun x => by ext i; rfl)

theorem matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A Λ _ _ _ ι _ I hI hbot n he
  classical
  let c := crtAlgEquiv A ι I hI hbot
  let e : ∀ i, (A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i) := fun i => (he i).some
  exact ⟨(Algebra.TensorProduct.rid A A Λ).symm
    |>.trans (Algebra.TensorProduct.congr AlgEquiv.refl c)
    |>.trans (Algebra.TensorProduct.piRight A A Λ (fun i => A ⧸ I i))
    |>.trans (AlgEquiv.piCongrRight (fun i => (Algebra.TensorProduct.comm A Λ (A ⧸ I i)).trans ((e i).restrictScalars A)))
    |>.trans (Matrix.piAlgEquiv A).symm
    |>.trans (AlgEquiv.mapMatrix c.symm)⟩

end GlobalTheory
end

section
open scoped TensorProduct
open Function
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algEquiv_matrix_glue_crt : ∀ (A Λ : Type) [CommRing A] [Ring Λ] [Algebra A Λ] (ι : Type) [Fintype ι] (I : ι → Ideal A), Pairwise (IsCoprime on I) → ⨅ i, I i = ⊥ → ∀ (n : ℕ), (∀ i, Nonempty ((A ⧸ I i) ⊗[A] Λ ≃ₐ[A ⧸ I i] Matrix (Fin n) (Fin n) (A ⧸ I i))) → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.matrix_glue_crt) | (exact GlobalTheory.matrix_glue_crt) | (intros; apply GlobalTheory.matrix_glue_crt  <;> assumption)
end

section
open scoped TensorProduct
open Function

namespace GlobalTheory.AzumayaMatrixReduction

theorem of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro hloc ℓ _ A _ _ _ Λ _ _ _ _ n hn
  obtain ⟨ι, _, I, hlocI, hcop, hbot⟩ := GlobalTheory.T.exists_localRing_quotients_coprime_iInf_eq_bot ℓ A
  refine GlobalTheory.T.algEquiv_matrix_glue_crt A Λ ι I hcop hbot n fun i => ?_
  haveI := hlocI i
  haveI : IsAzumaya (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) := GlobalTheory.T.azumaya_base_change A (A ⧸ I i) Λ
  haveI : Module.Finite ℤ_[ℓ] (A ⧸ I i) :=
    Module.Finite.of_surjective ((IsScalarTower.toAlgHom ℤ_[ℓ] A (A ⧸ I i)).toLinearMap)
      Ideal.Quotient.mk_surjective
  refine hloc ℓ (A ⧸ I i) ((A ⧸ I i) ⊗[A] Λ) n ?_
  haveI : Nontrivial A := (Ideal.Quotient.mk (I i)).domain_nontrivial
  rw [Module.finrank_baseChange, hn]

end GlobalTheory.AzumayaMatrixReduction
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local : (∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A)) →
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaMatrixReduction.of_local) | (exact GlobalTheory.AzumayaMatrixReduction.of_local) | (intros; apply GlobalTheory.AzumayaMatrixReduction.of_local <;> assumption)
end

section
noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory.LocMatrix

theorem locOrder_eq_of_le {B : Type} [Ring B] [Algebra ℚ B] (OB Λ : Subring B) (hle : OB ≤ Λ)
    (N : ℕ) (hN : 0 < N) (hNΛ : ∀ x ∈ Λ, (N : B) * x ∈ OB) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    locOrder ℓ OB = locOrder ℓ Λ := by
  apply le_antisymm
  · exact Algebra.adjoin_mono (Set.image_mono hle)
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact GlobalTheory.one_tmul_mem_locOrder_of_nsmul_mem OB x N hN (hNΛ x hx) ℓ hℓ

theorem locOrder_matrix : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  intro F B _ _ _ _ _ _ _ _ _ n hn OB hfin hspan
  obtain ⟨Λ, hle, hΛ, hΛfin, N₁, hN₁, hN₁Λ⟩ := GlobalTheory.T.exists_order_containing_integers F B OB hfin hspan
  have hspanΛ : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ := fun b => by
    obtain ⟨m, hm, hmb⟩ := hspan b; exact ⟨m, hm, hle hmb⟩
  obtain ⟨N₂, hN₂, hfree⟩ := GlobalTheory.T.localOrderTensorPadic_free_almost_all F B Λ hΛ hΛfin hspanΛ
  obtain ⟨N₃, hN₃, hazu⟩ := GlobalTheory.T.localOrderTensorPadic_isAzumaya_almost_all F B Λ hΛ hΛfin hspanΛ
  refine ⟨N₁ * N₂ * N₃, by positivity, fun ℓ _ hℓ => ?_⟩
  have h₁ : ¬ ℓ ∣ N₁ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
  have h₂ : ¬ ℓ ∣ N₂ := fun h => hℓ (Dvd.dvd.mul_right (Dvd.dvd.mul_left h _) _)
  have h₃ : ¬ ℓ ∣ N₃ := fun h => hℓ (Dvd.dvd.mul_left h _)
  have heq := locOrder_eq_of_le OB Λ hle N₁ hN₁ hN₁Λ ℓ h₁
  letI := cenAlgebra ℓ F B Λ hΛ
  haveI := isScalarTower_cenAlgebra ℓ F B Λ hΛ
  haveI : Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := GlobalTheory.cenOrder_finite F ℓ
  obtain ⟨hF, hrank⟩ := hfree ℓ h₂
  haveI := hF
  haveI := hazu ℓ h₃
  obtain ⟨φ⟩ := GlobalTheory.T.azumaya_matrix_of_finite_padic_algebra_of_local GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local ℓ (cenOrder ℓ F) (locOrder ℓ Λ) n (hrank.trans hn)
  refine ⟨(Subalgebra.equivOfEq _ _ heq).trans (φ.restrictScalars ℤ_[ℓ]), fun a => ?_⟩
  refine ⟨heq ▸ cenMap_mem ℓ F B Λ hΛ a.2, ?_⟩
  have h2 : (Subalgebra.equivOfEq _ _ heq) ⟨cenMap ℓ F B a, heq ▸ cenMap_mem ℓ F B Λ hΛ a.2⟩ =
      algebraMap (cenOrder ℓ F) (locOrder ℓ Λ) a := Subtype.ext rfl
  rw [AlgEquiv.trans_apply, h2, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  ext i j
  simp [Matrix.algebraMap_matrix_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

end GlobalTheory.LocMatrix
end
end

section
open scoped TensorProduct
open GlobalTheory.LKInvGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] [Algebra.IsCentral F B] [IsSimpleRing B] [FiniteDimensional F B] (n : ℕ),
    Module.finrank F B = n ^ 2 → ∀ (OB : Subring B), Module.Finite ℤ OB →
    (∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ OB) →
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ N →
      ∃ ψ : locOrder ℓ OB ≃ₐ[ℤ_[ℓ]] Matrix (Fin n) (Fin n) (cenOrder ℓ F), CentreCompat ℓ OB ψ := by
  first | (exact @GlobalTheory.LocMatrix.locOrder_matrix) | (exact GlobalTheory.LocMatrix.locOrder_matrix) | (intros; apply GlobalTheory.LocMatrix.locOrder_matrix  <;> assumption)
end
