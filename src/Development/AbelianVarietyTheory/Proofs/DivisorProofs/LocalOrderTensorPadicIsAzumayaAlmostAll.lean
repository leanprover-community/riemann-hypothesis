module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsScalarTowerCenAlgebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CycleListPermInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveIffIsUnitDet
public import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv

@[expose] public section

noncomputable section
open scoped TensorProduct
open GlobalTheory.LKInvGood Module

namespace GlobalTheory.LocAzumaya

theorem exists_den_coords : ∀ (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] (Λ : Subring B),
    Module.Finite ℤ Λ → ∀ (ι : Type) [Fintype ι] (e : Module.Basis ι F B),
    ∃ D : ℕ, 0 < D ∧ ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((D : F) * e.repr x k) := by
  intro F B _ _ _ _ Λ hfin ι _ e
  classical
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  obtain ⟨D, hD, hDi⟩ := GlobalTheory.SepModel.exists_nat_integral
    (Finset.univ.image fun p : Fin n × ι => e.repr (s p.1 : B) p.2)
  refine ⟨D, hD, fun x hx => ?_⟩
  have key : ∀ y : Λ, y ∈ Submodule.span ℤ (Set.range s) →
      ∀ k, IsIntegral ℤ ((D : F) * e.repr (y : B) k) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro k
      exact hDi _ (Finset.mem_image.2 ⟨(j, k), Finset.mem_univ _, rfl⟩)
    | zero => intro k; simpa using isIntegral_zero
    | add y z _ _ hy hz =>
      intro k
      simpa [mul_add] using (hy k).add (hz k)
    | smul a y _ hy =>
      intro k
      have : (D : F) * e.repr ((a • y : Λ) : B) k = (a : F) * ((D : F) * e.repr (y : B) k) := by
        have hc : ((a • y : Λ) : B) = (a : F) • (y : B) := by
          have h0 : ((a • y : Λ) : B) = a • (y : B) := rfl
          rw [h0, zsmul_eq_mul, Algebra.smul_def, map_intCast]
        rw [hc]
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
        ring
      rw [this]
      have ha : IsIntegral ℤ (a : F) := by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ F a))
      exact ha.mul (hy k)
  intro k
  exact key ⟨x, hx⟩ (by rw [hs]; trivial) k
theorem exists_coords_of_mem_locOrder : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B] [Algebra ℚ B]
    [IsScalarTower ℚ F B] (Λ : Subring B) (ι : Type) [Fintype ι] (e : Module.Basis ι F B),
    (∀ i, e i ∈ Λ) → (∀ x ∈ Λ, ∀ k, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x k ∈ cenOrder ℓ F) →
    ∀ y ∈ locOrder ℓ Λ, ∃ c : ι → ℚ_[ℓ] ⊗[ℚ] F, (∀ i, c i ∈ cenOrder ℓ F) ∧
      y = ∑ i, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
  intro ℓ _ F B _ _ _ _ _ _ Λ ι _ e he hco
  classical
  have hexp : ∀ x : B, (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] x =
      ∑ i, cenMap ℓ F B ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) := by
    intro x
    conv_lhs => rw [← e.sum_repr x]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.LocMatrix.cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
  intro y hy
  induction hy using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨fun i => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr x i, fun i => hco x hx i, hexp x⟩
  | algebraMap r =>
    refine ⟨fun i => algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) r * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr 1 i),
      fun i => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) (hco 1 Λ.one_mem i), ?_⟩
    have h1 : ∀ a : ℚ_[ℓ] ⊗[ℚ] F, cenMap ℓ F B (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F) r * a) =
        algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B) r * cenMap ℓ F B a := by
      intro a
      rw [map_mul, IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] F),
        IsScalarTower.algebraMap_apply ℤ_[ℓ] ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] B), AlgHom.commutes]
    simp only [h1, mul_assoc]
    rw [← Finset.mul_sum, ← hexp 1, Algebra.TensorProduct.one_def.symm, mul_one]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hz
    refine ⟨fun i => c i + c' i, fun i => Subalgebra.add_mem _ (hc i) (hc' i), ?_⟩
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
  | mul y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨c', hc', rfl⟩ := hz
    refine ⟨fun k => ∑ i, ∑ j, c i * c' j * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr (e i * e j) k), fun k => ?_, ?_⟩
    · exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
        Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (hc i) (hc' j)) (hco _ (Λ.mul_mem (he i) (he j)) k)
    · have hprod : ∀ i j, cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) *
            (cenMap ℓ F B (c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e j)) =
          ∑ k, cenMap ℓ F B (c i * c' j * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr (e i * e j) k)) *
            ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e k) := by
        intro i j
        have hcomm := (GlobalTheory.LocMatrix.cenMap_commute ℓ F B (c' j) ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i)).eq
        have h1 : cenMap ℓ F B (c i) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i) *
            (cenMap ℓ F B (c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e j)) =
            cenMap ℓ F B (c i * c' j) * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (e i * e j)) := by
          rw [map_mul, ← one_mul (1 : ℚ_[ℓ]), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            mul_assoc, ← mul_assoc ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i), ← hcomm]
          simp only [mul_assoc]
        rw [h1, hexp (e i * e j), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul]
      rw [Finset.sum_mul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hprod, map_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]

theorem exists_coordProj (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B]
    [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] {ι : Type} [DecidableEq ι] (e : Basis ι F B)
    (k : ι) : ∃ π : ℚ_[ℓ] ⊗[ℚ] B →ₗ[ℚ] ℚ_[ℓ] ⊗[ℚ] F,
      (∀ b : B, π ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e.repr b k) ∧
      ∀ (a : ℚ_[ℓ] ⊗[ℚ] F) (i : ι),
        π (cenMap ℓ F B a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] e i)) = if i = k then a else 0 := by
  refine ⟨LinearMap.lTensor ℚ_[ℓ] ((e.coord k).restrictScalars ℚ), fun b => by simp, fun a i => ?_⟩
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul q x =>
    rw [GlobalTheory.LocMatrix.cenMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Algebra.smul_def]
    simp only [LinearMap.lTensor_tmul, LinearMap.coe_restrictScalars, map_smul, Basis.coord_apply,
      Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    split_ifs <;> simp
  | add a a' ha ha' =>
    rw [map_add (f := _), add_mul, map_add (f := _), ha, ha']
    split_ifs <;> simp

end GlobalTheory.LocAzumaya

namespace GlobalTheory.LocAzumaya

theorem exists_basis_mem {F B : Type} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (Λ : Subring B) (hspan : ∀ b : B, ∃ m : ℕ, 0 < m ∧ (m : B) * b ∈ Λ) :
    ∃ e : Basis (Fin (Module.finrank F B)) F B, ∀ i, e i ∈ Λ := by
  let b := Module.finBasis F B
  choose m hm hmb using fun i => hspan (b i)
  let u : Fin (Module.finrank F B) → Fˣ := fun i => Units.mk0 (m i : F) (by exact_mod_cast (hm i).ne')
  refine ⟨b.unitsSMul u, fun i => ?_⟩
  rw [Basis.unitsSMul_apply]
  convert hmb i using 1
  simp [u, Algebra.smul_def]

theorem cenMap_injective (ℓ : ℕ) [Fact ℓ.Prime] (F B : Type) [Field F] [NumberField F] [Ring B] [Algebra F B]
    [Algebra ℚ B] [IsScalarTower ℚ F B] [Nontrivial B] : Function.Injective (cenMap ℓ F B) := by
  let g : F →ₗ[ℚ] B := ((Algebra.ofId F B).restrictScalars ℚ).toLinearMap
  have hg : Function.Injective g := (algebraMap F B).injective
  have heq : ⇑(cenMap ℓ F B) = ⇑(LinearMap.lTensor ℚ_[ℓ] g) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul q f => simp [cenMap, g]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [heq]
  exact Module.Flat.lTensor_preserves_injective_linearMap g hg

end GlobalTheory.LocAzumaya

namespace GlobalTheory.LocAzumaya

end GlobalTheory.LocAzumaya
