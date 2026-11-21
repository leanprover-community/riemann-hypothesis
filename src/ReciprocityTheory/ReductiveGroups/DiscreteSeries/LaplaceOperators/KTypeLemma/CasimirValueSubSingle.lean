import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.QuotientHighestWeightTensorStandard
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KhwWeightEqOfIrr
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsCommutingProjectionImage
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.CasimirTensVd
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SingleSmulFin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K1V
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K2V
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.SchmidCas
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ConeNorm

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem root_cone_functional_natural (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, ℓ (root a b) = N)
    {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, ℓ β = N := by
  classical
  obtain ⟨m, rfl⟩ := hβ
  choose! N hN using hℓ
  refine ⟨∑ a, ∑ b, if a < b then m a b * N a b else 0, ?_⟩
  simp only [map_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [map_smul, hN a b h, smul_eq_mul]
  · simp

def weightPowerSumFunctional (k : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ a ∈ univ.filter (fun a : Fin n => a.val < k), LinearMap.proj a

theorem k3vdPs_apply (k : ℕ) (μ : Fin n → ℝ) : weightPowerSumFunctional k μ = kirrPs k μ := by
  simp [weightPowerSumFunctional, kirrPs, LinearMap.sum_apply]

theorem partial_sum_of_basis_vector (k : ℕ) (a : Fin n) :
    kirrPs k (Pi.single a (1 : ℝ)) = if a.val < k then 1 else 0 := by
  simp [kirrPs, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_filter]

theorem partial_sum_of_root (k : ℕ) (a b : Fin n) :
    kirrPs k (root a b) = (if a.val < k then 1 else 0) - (if b.val < k then 1 else 0) := by
  rw [← partial_sum_of_basis_vector, ← partial_sum_of_basis_vector]
  simp [kirrPs, root, Finset.sum_sub_distrib]

theorem root_cone_partial_sum_natural {β : Fin n → ℝ} (hβ : InRootCone β) (k : ℕ) : ∃ N : ℕ, kirrPs k β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightPowerSumFunctional k (root a b) = N := by
    intro a b hab
    have hv := Fin.lt_def.1 hab
    rw [k3vdPs_apply, partial_sum_of_root]
    by_cases ha : a.val < k <;> by_cases hb : b.val < k
    · exact ⟨0, by simp [ha, hb]⟩
    · exact ⟨1, by simp [ha, hb]⟩
    · omega
    · exact ⟨0, by simp [ha, hb]⟩
  obtain ⟨N, hN⟩ := root_cone_functional_natural (weightPowerSumFunctional k) hℓ hβ
  exact ⟨N, by rw [← k3vdPs_apply]; exact hN⟩

def weightHeightFunctional : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ c : Fin n, ((n : ℝ) - (c : ℕ)) • LinearMap.proj c

theorem k3vdHt_root (a b : Fin n) : weightHeightFunctional (root a b) = ((b : ℕ) : ℝ) - (a : ℕ) := by
  simp only [weightHeightFunctional, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    root, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem root_cone_height_natural {β : Fin n → ℝ} (hβ : InRootCone β) : ∃ N : ℕ, weightHeightFunctional β = N := by
  have hℓ : ∀ a b : Fin n, a < b → ∃ N : ℕ, weightHeightFunctional (root a b) = N := by
    intro a b hab
    refine ⟨b.val - a.val, ?_⟩
    rw [k3vdHt_root, Nat.cast_sub (le_of_lt (Fin.lt_def.1 hab))]
  exact root_cone_functional_natural weightHeightFunctional hℓ hβ

theorem coordinate_eq_partial_sum_difference (γ : Fin n → ℝ) (a : Fin n) :
    γ a = kirrPs ((a : ℕ) + 1) γ - kirrPs (a : ℕ) γ := by
  unfold kirrPs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp
  · intro c _ hc
    have : c.val ≠ a.val := fun h => hc (Fin.ext h)
    by_cases h1 : c.val < a.val
    · simp [h1, show c.val < a.val + 1 by omega]
    · simp [h1, show ¬ c.val < a.val + 1 by omega]
  · simp

theorem coordinate_difference_le_two (γ : Fin n → ℝ) (hγ : ∀ k, -1 ≤ kirrPs k γ ∧ kirrPs k γ ≤ 0) (a b : Fin n) :
    |γ a - γ b| ≤ 2 := by
  have h1 := coordinate_eq_partial_sum_difference γ a
  have h2 := coordinate_eq_partial_sum_difference γ b
  have a1 := hγ ((a : ℕ) + 1)
  have a0 := hγ (a : ℕ)
  have b1 := hγ ((b : ℕ) + 1)
  have b0 := hγ (b : ℕ)
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a0.1, a0.2, b1.1, b1.2, b0.1, b0.2]

theorem strictAnti_of_consecutive_lt {f : Fin n → ℝ} (h : ∀ a b : Fin n, b.val = a.val + 1 → f b < f a) :
    StrictAnti f := by
  intro a b hab
  have key : ∀ d : ℕ, ∀ b : Fin n, b.val = a.val + d + 1 → f b < f a := by
    intro d
    induction d with
    | zero => intro b hb; exact h a b (by omega)
    | succ d ih =>
      intro b hb
      have hc : a.val + d + 1 < n := by have := b.isLt; omega
      exact lt_trans (h ⟨a.val + d + 1, hc⟩ b (by show b.val = a.val + d + 1 + 1; omega))
        (ih ⟨a.val + d + 1, hc⟩ rfl)
  exact key (b.val - a.val - 1) b (by have := Fin.lt_def.1 hab; omega)

theorem rho_consecutive_compact_pair (ε : Fin n → Bool) (a b : Fin n) (hb : b.val = a.val + 1) (he : ε a = ε b) :
    rhoC ε a = rhoC ε b + 1 ∧ rhoN ε a = rhoN ε b := by
  have hab : ∀ c : Fin n, a < c ↔ c = b ∨ b < c := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have hba : ∀ c : Fin n, c < b ↔ c = a ∨ c < a := by
    intro c; rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]; omega
  have e1 : (univ.filter fun c => a < c ∧ ε c = ε a) =
      insert b (univ.filter fun c => b < c ∧ ε c = ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr h1, h2⟩
  have e2 : (univ.filter fun c => c < b ∧ ε c = ε b) =
      insert a (univ.filter fun c => c < a ∧ ε c = ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_insert, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, he⟩
      · exact ⟨Or.inr h1, h2⟩
  have e3 : (univ.filter fun c => a < c ∧ ε c ≠ ε a) = (univ.filter fun c => b < c ∧ ε c ≠ ε b) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hab c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ rfl) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have e4 : (univ.filter fun c => c < b ∧ ε c ≠ ε b) = (univ.filter fun c => c < a ∧ ε c ≠ ε a) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, hba c, he]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ he) h2
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, h2⟩
  have nb : b ∉ univ.filter fun c => b < c ∧ ε c = ε b := by simp
  have na : a ∉ univ.filter fun c => c < a ∧ ε c = ε a := by simp
  refine ⟨?_, ?_⟩
  · unfold rhoC
    rw [e1, e2, card_insert_of_notMem nb, card_insert_of_notMem na]
    push_cast
    ring
  · unfold rhoN
    rw [e3, e4]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sub (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := A.submatrix Fin.revPerm Fin.revPerm

theorem sub_apply (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) : sub A a b = A (Fin.rev a) (Fin.rev b) := rfl

theorem sub_mul (A B : Matrix (Fin n) (Fin n) ℂ) : sub (A * B) = sub A * sub B := by
  simp only [sub]
  exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

theorem sub_one : sub (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp only [sub]
  exact Matrix.submatrix_one_equiv _

theorem sub_H (A : Matrix (Fin n) (Fin n) ℂ) : (sub A)ᴴ = sub Aᴴ := by
  simp [sub, Matrix.conjTranspose_submatrix]

theorem sub_add (A B : Matrix (Fin n) (Fin n) ℂ) : sub (A + B) = sub A + sub B := rfl

theorem sub_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : sub (c • A) = c • sub A := rfl

theorem sub_zero : sub (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := rfl

def Pr (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => if i = Fin.rev j then 1 else 0

theorem Pr_mul (A : Matrix (Fin n) (Fin n) ℂ) : Pr n * A = A.submatrix Fin.rev id := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [Pr]
  · intro k _ hk
    simp only [Pr, Matrix.of_apply]
    rw [if_neg (fun h => hk (by rw [h, Fin.rev_rev]))]
    ring
  · simp

theorem mul_Pr (A : Matrix (Fin n) (Fin n) ℂ) : A * Pr n = A.submatrix id Fin.rev := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [Pr]
  · intro k _ hk
    simp only [Pr, Matrix.of_apply]
    rw [if_neg hk]
    ring
  · simp

theorem Pr_conj (A : Matrix (Fin n) (Fin n) ℂ) : Pr n * A * Pr n = sub A := by
  rw [Pr_mul, mul_Pr]
  ext i j
  simp [sub]

theorem Pr_Pr : Pr n * Pr n = 1 := by
  rw [Pr_mul]
  ext i j
  simp [Pr, Matrix.one_apply]

theorem Pr_inv : (Pr n)⁻¹ = Pr n := by
  exact Matrix.inv_eq_left_inv Pr_Pr

theorem exp_sub (A : Matrix (Fin n) (Fin n) ℂ) : NormedSpace.exp (sub A) = sub (NormedSpace.exp A) := by
  have hu : IsUnit (Pr n) := ⟨⟨Pr n, Pr n, Pr_Pr, Pr_Pr⟩, rfl⟩
  rw [← Pr_conj, ← Pr_conj (NormedSpace.exp A)]
  have h1 : Pr n * A * Pr n = Pr n * A * (Pr n)⁻¹ := by rw [Pr_inv]
  rw [h1, Matrix.exp_conj _ _ hu, Pr_inv]

theorem Jm_rev (ε : Fin n → Bool) : sub (Jm (ε ∘ Fin.rev)) = Jm ε := by
  ext a b
  simp [sub, Jm, Matrix.diagonal_apply]

theorem inUJ_sub {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset (ε ∘ Fin.rev)) :
    sub g ∈ UJset ε := by
  show (sub g)ᴴ * Jm ε * sub g = Jm ε
  have hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev) := hg
  rw [← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, hg']

theorem inG_sub {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    inG ε (sub X) := by
  unfold inG at *
  rw [← Jm_rev ε, sub_H, ← sub_mul, ← sub_mul, ← sub_add, hX, sub_zero]

theorem K_sub {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset (ε ∘ Fin.rev)) :
    sub k ∈ Kset ε := by
  simp only [Kset, Set.mem_setOf_eq] at hk ⊢
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hu ⊢
    rw [Matrix.star_eq_conjTranspose] at hu ⊢
    rw [sub_H, ← sub_mul, hu, sub_one]
  · rw [← Jm_rev ε, ← sub_mul, ← sub_mul, hc]

theorem inG_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (a b : Fin n) :
    X b a = (if ε a = ε b then -1 else 1) * conj (X a b) := by
  have h := congrFun (congrFun hX b) a
  rw [Matrix.add_apply, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  cases hεa : ε a <;> cases hεb : ε b <;> simp [hεa, hεb, Complex.star_def] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

section Conj

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def cjSub (S : Submodule ℂ H) : Submodule ℂ (Cj H) where
  carrier := {x | ofCj x ∈ S}
  add_mem' hx hy := S.add_mem hx hy
  zero_mem' := S.zero_mem
  smul_mem' c _ hx := S.smul_mem (conj c) hx

variable {D : Submodule ℂ H}

def toD (x : cjSub D) : D := ⟨ofCj (x : Cj H), x.2⟩

def ofD (u : D) : cjSub D := ⟨toCj (u : H), u.2⟩

@[simp] theorem toD_ofD (u : D) : toD (ofD u) = u := rfl

@[simp] theorem ofD_toD (x : cjSub D) : ofD (toD x) = x := rfl

theorem ofD_add (u v : D) : ofD (u + v) = ofD u + ofD v := rfl

theorem ofD_sub (u v : D) : ofD (u - v) = ofD u - ofD v := rfl

theorem ofD_neg (u : D) : ofD (-u) = -ofD u := rfl

theorem ofD_zero : ofD (0 : D) = 0 := rfl

theorem toD_add (x y : cjSub D) : toD (x + y) = toD x + toD y := rfl

theorem toD_smul (c : ℂ) (x : cjSub D) : toD (c • x) = conj c • toD x := rfl

theorem ofD_smul (c : ℂ) (u : D) : ofD (c • u) = conj c • ofD u := by
  have h := toD_smul (conj c) (ofD u)
  rw [toD_ofD, Complex.conj_conj] at h
  rw [← h, ofD_toD]

theorem ofD_injective : Function.Injective (ofD : D → cjSub D) := by
  intro u v h
  have := congrArg toD h
  simpa using this

def ofDh : D →+ cjSub D where
  toFun := ofD
  map_zero' := rfl
  map_add' := ofD_add

theorem ofD_sum {ι : Type*} (s : Finset ι) (f : ι → D) : ofD (∑ i ∈ s, f i) = ∑ i ∈ s, ofD (f i) := by
  exact map_sum ofDh f s

def ofDL : D →ₛₗ[starRingEnd ℂ] cjSub D where
  toFun := ofD
  map_add' := ofD_add
  map_smul' := ofD_smul

def cjEnd (A : Module.End ℂ D) : Module.End ℂ (cjSub D) where
  toFun x := ofD (A (toD x))
  map_add' x y := by rw [toD_add, map_add, ofD_add]
  map_smul' c x := by
    show ofD (A (toD (c • x))) = c • ofD (A (toD x))
    rw [toD_smul, A.map_smul, ofD_smul]
    simp

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε (Fin.rev a) then 1 else -1

theorem sg_sq (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg
  split_ifs <;> norm_num

theorem conj_sg (ε : Fin n → Bool) (a : Fin n) : conj (sg ε a) = sg ε a := by
  unfold sg
  split_ifs <;> simp

theorem sg_ne (ε : Fin n → Bool) (a : Fin n) : sg ε a ≠ 0 := by
  unfold sg
  split_ifs <;> norm_num

def Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (cjSub D) :=
  cjEnd ((-(sg ε a * sg ε b)) • E (Fin.rev b) (Fin.rev a))

theorem Edd_ofD (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (u : D) :
    Edd ε E a b (ofD u) = ofD ((-(sg ε a * sg ε b)) • E (Fin.rev b) (Fin.rev a) u) := rfl

theorem glRep_Edd (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ D} (hE : IsGlRep E) :
    IsGlRep (Edd ε E) := by
  intro a b c d
  apply LinearMap.ext
  intro x
  obtain ⟨u, rfl⟩ : ∃ u, x = ofD u := ⟨toD x, (ofD_toD x).symm⟩
  have key := congrArg (fun T : Module.End ℂ D => T u) (hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Fin.rev_inj] at key
  have lhs : (Edd ε E a b * Edd ε E c d - Edd ε E c d * Edd ε E a b) (ofD u) =
      ofD ((sg ε a * sg ε b * (sg ε c * sg ε d)) • (E (Fin.rev b) (Fin.rev a) (E (Fin.rev d) (Fin.rev c) u) -
        E (Fin.rev d) (Fin.rev c) (E (Fin.rev b) (Fin.rev a) u))) := by
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Edd_ofD, LinearMap.map_smul]
    rw [← ofD_sub]
    congr 1
    module
  rw [lhs, key, LinearMap.sub_apply]
  by_cases hbc : b = c <;> by_cases hda : d = a
  · subst c
    subst d
    simp only [eq_self_iff_true, if_true, Edd_ofD]
    rw [← ofD_sub]
    congr 1
    unfold sg
    split_ifs <;> module
  · subst c
    have hda' : ¬ Fin.rev a = Fin.rev d := fun h => hda (Fin.rev_injective h).symm
    simp only [eq_self_iff_true, if_true, if_neg hda, if_neg (Ne.symm hda), if_neg hda', LinearMap.zero_apply, Edd_ofD,
      sub_zero, zero_sub]
    first
    | (congr 1; unfold sg; split_ifs <;> module)
    | (rw [← ofD_neg]; congr 1; unfold sg; split_ifs <;> module)
    | (apply ofD_injective; unfold sg; split_ifs <;> module)
    | (simp only [← ofD_neg, ← ofD_sub, ← ofD_zero]; congr 1; unfold sg; split_ifs <;> module)
  · subst d
    have hbc' : ¬ Fin.rev c = Fin.rev b := fun h => hbc (Fin.rev_injective h).symm
    simp only [eq_self_iff_true, if_true, if_neg hbc, if_neg (Ne.symm hbc), if_neg hbc', LinearMap.zero_apply, Edd_ofD,
      sub_zero, zero_sub]
    simp only [sub_zero, zero_sub, LinearMap.zero_apply, ← ofD_neg, ← ofD_sub]
    congr 1
    unfold sg
    split_ifs <;> module
  · have hda' : ¬ Fin.rev a = Fin.rev d := fun h => hda (Fin.rev_injective h).symm
    have hbc' : ¬ Fin.rev c = Fin.rev b := fun h => hbc (Fin.rev_injective h).symm
    simp only [if_neg hbc, if_neg (Ne.symm hbc), if_neg hda, if_neg (Ne.symm hda), if_neg hda', if_neg hbc', LinearMap.zero_apply,
      sub_zero, smul_zero]
    simp [ofD_zero]

end Conj

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
end
end

section
noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool}

def sdd (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : Cj H →L[ℂ] Cj H :=
  opCj (σ (sub g))

theorem urep_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) :
    IsURepOn (UJset (ε ∘ Fin.rev)) (sdd σ) := by
  obtain ⟨⟨h1, hm⟩, hn, hc⟩ := hσ
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · unfold sdd; rw [sub_one, h1]; rfl
  · intro a ha b hb; unfold sdd; rw [sub_mul, hm _ (inUJ_sub ha) _ (inUJ_sub hb)]; rfl
  · intro g hg v; exact hn _ (inUJ_sub hg) (ofCj v)
  · intro v
    have hcs : Continuous (sub : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      continuous_id.matrix_submatrix _ _
    exact (hc (ofCj v)).comp hcs.continuousOn (fun g hg => inUJ_sub hg)

theorem smul_ofD (c : ℂ) (u : D) : c • ofD u = ofD (conj c • u) := by
  rw [ofD_smul]; simp

theorem sum_rev_swap {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, ∑ b, F (Fin.rev b) (Fin.rev a) := by
  rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Equiv.sum_comp Fin.revPerm]
  rfl

theorem actM_Edd {E : Fin n → Fin n → Module.End ℂ D} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG (ε ∘ Fin.rev) X) (u : D) : actM (Edd ε E) X (ofD u) = ofD (actM E (sub X) u) := by
  unfold actM
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Edd_ofD, smul_ofD, ofD_sum]
  rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev, sub_apply, smul_smul]
  congr 2
  have he := inG_entry hX (Fin.rev b) (Fin.rev a)
  simp only [Function.comp_apply, Fin.rev_rev] at he
  rw [he]
  unfold sg
  simp only [Fin.rev_rev]
  cases ε a <;> cases ε b <;> simp

theorem real_smul_cj (r : ℝ) (x : Cj H) : r • x = toCj (r • ofCj x) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ) r (ofCj x),
    ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace.smul_def, RCLike.conj_ofReal]

def toCjR : H →L[ℝ] Cj H where
  toFun := toCj
  map_add' _ _ := rfl
  map_smul' r x := (real_smul_cj r (toCj x)).symm
  cont := continuous_id

theorem derived_sdd {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
    (hD : IsDerivedOn ε σ D E) : IsDerivedOn (ε ∘ Fin.rev) (sdd σ) (cjSub D) (Edd ε E) where
  glRep := glRep_Edd ε hD.glRep
  kStable k hk v hv := hD.kStable (sub k) (K_sub hk) (ofCj v) hv
  deriv X hX v := by
    have h3 := hD.deriv (sub X) (inG_sub hX) (toD v)
    have h4 := (toCjR (H := H)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3
    have hv : v = ofD (toD v) := rfl
    rw [hv, actM_Edd hX]
    convert h4 using 1
    · funext t
      simp only [sdd, Function.comp_apply, ← exp_sub, sub_smul]
      rfl
    · rfl

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
end
end

section
noncomputable section

open Finset Matrix ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lamd (lam : Fin n → ℝ) : Fin n → ℝ := fun a => -lam (Fin.rev a)

theorem card_eq_of_rev (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ b, P b ↔ Q (Fin.rev b)) : (univ.filter P).card = (univ.filter Q).card := by
  apply Finset.card_bij' (fun b _ => Fin.rev b) (fun b _ => Fin.rev b) <;> simp [h]

theorem rhoN_rev (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b ≠ (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoN
  rw [h1, h2]
  ring

theorem rhoC_rev (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ Fin.rev) b = (ε ∘ Fin.rev) a).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card :=
    card_eq_of_rev _ _ fun b => by simp [Fin.rev_lt_rev]
  unfold rhoC
  rw [h1, h2]
  ring

theorem lowK_rev (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK (ε ∘ Fin.rev) (lamd lam) a = -lowK ε lam (Fin.rev a) := by
  simp only [lowK, Pi.add_apply, Pi.sub_apply, lamd, rhoN_rev, rhoC_rev]
  ring

theorem casVal_rev (lam : Fin n → ℝ) : casVal (lamd lam) = casVal lam := by
  unfold casVal nsq dot
  simp only [lamd, neg_mul_neg]
  congr 1
  exact Equiv.sum_comp Fin.revPerm (fun a => lam a * lam a)

theorem pOf_rev (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε :=
  card_eq_of_rev _ _ fun b => by simp

theorem qOf_rev (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε :=
  card_eq_of_rev _ _ fun b => by simp

theorem hNeed_rev (ε : Fin n → Bool) : hNeed (ε ∘ Fin.rev) = hNeed ε := by
  unfold hNeed; rw [pOf_rev, qOf_rev]

theorem gapLap_rev {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (lamd lam) h := by
  obtain ⟨hanti, hgap, hh⟩ := hg
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a b hab => ?_, by rwa [hNeed_rev]⟩
  have := hgap (Fin.rev a) (Fin.rev b) hab
  rw [show lamd lam a - lamd lam b = -(lam (Fin.rev a) - lam (Fin.rev b)) by simp only [lamd]; ring, abs_neg]
  exact this

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def cjV (V : Submodule ℂ D) : Submodule ℂ (cjSub D) := V.map (ofDL (D := D))

theorem mem_cjV {V : Submodule ℂ D} (x : cjSub D) : x ∈ cjV V ↔ toD x ∈ V := by
  constructor
  · rintro ⟨u, hu, rfl⟩; exact hu
  · intro h; exact ⟨toD x, h, rfl⟩

theorem ofD_E (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (u : D) :
    ofD (E a b u) = (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) • Edd ε E (Fin.rev b) (Fin.rev a) (ofD u) := by
  rw [Edd_ofD, smul_ofD, Fin.rev_rev, Fin.rev_rev, smul_smul]
  have h1 : conj (-(sg ε (Fin.rev b) * sg ε (Fin.rev a))) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) = 1 := by
    simp only [map_neg, map_mul, conj_sg]
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

theorem kirr_cjV {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ D}
    {V : Submodule ℂ D} (hV : IsKIrrHW ε E (lowK ε lam) V) :
    IsKIrrHW (ε ∘ Fin.rev) (Edd ε E) (lowK (ε ∘ Fin.rev) (lamd lam)) (cjV V) := by
  obtain ⟨hfin, hst, hirr, w, hwV, hw0, hwa, hwb⟩ := hV
  refine ⟨?_, ?_, ?_, ofD w, (mem_cjV _).2 hwV, ?_, ?_, ?_⟩
  · have hfg : V.FG := Module.Finite.iff_fg.mp hfin
    exact Module.Finite.iff_fg.mpr (hfg.map _)
  · intro a b hab v hv
    rw [mem_cjV] at hv ⊢
    exact V.smul_mem _ (hst (Fin.rev b) (Fin.rev a) hab.symm _ hv)
  · intro S' hle hS'
    have hSle : S'.comap (ofDL (D := D)) ≤ V := fun u hu => (mem_cjV (ofD u)).1 (hle hu)
    have hSst : IsKStableSub ε E (S'.comap (ofDL (D := D))) := by
      intro a b hab u hu
      show ofD (E a b u) ∈ S'
      rw [ofD_E ε E a b u]
      refine S'.smul_mem _ (hS' _ _ ?_ _ hu)
      simp [hab]
    rcases hirr _ hSle hSst with h0 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : toD x ∈ S'.comap (ofDL (D := D)) := hx
      rw [h0, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← ofD_toD x, this]
      rfl
    · right
      refine le_antisymm hle fun x hx => ?_
      have : toD x ∈ S'.comap (ofDL (D := D)) := by rw [h1]; exact (mem_cjV x).1 hx
      exact this
  · intro h
    apply hw0
    apply ofD_injective
    rw [h]; rfl
  · intro a
    rw [Edd_ofD, hwa, smul_smul, sg_sq, smul_ofD, lowK_rev]
    congr 1
    push_cast
    simp
  · intro a b hab hε
    rw [Edd_ofD, hwb _ _ (Fin.rev_lt_rev.mpr hab) hε.symm, smul_zero]
    rfl

theorem casimir_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (u : D) :
    casimir (Edd ε E) (ofD u) = ofD (casimir E u) := by
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, Edd_ofD, ofD_sum, LinearMap.map_smul, smul_smul]
  conv_lhs => rw [sum_rev_swap]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Fin.rev_rev]
  have h1 : -(sg ε (Fin.rev b) * sg ε (Fin.rev a)) * -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) = 1 := by
    linear_combination (sg ε (Fin.rev a) * sg ε (Fin.rev a)) * sg_sq ε (Fin.rev b) + sg_sq ε (Fin.rev a)
  rw [h1, one_smul]

theorem le_genSub' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) : S ≤ genSub E S := le_sInf fun _ hT => hT.1

theorem genSub_stable' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (S : Submodule ℂ M) (a b : Fin n) {v : M} (hv : v ∈ genSub E S) : E a b v ∈ genSub E S := by
  unfold genSub at hv ⊢
  rw [Submodule.mem_sInf] at hv ⊢
  intro T hT
  exact hT.2 a b v (hv T hT)

theorem genSub_le' {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    {S T : Submodule ℂ M} (hS : S ≤ T) (hT : ∀ a b, ∀ v ∈ T, E a b v ∈ T) : genSub E S ≤ T :=
  sInf_le ⟨hS, hT⟩

theorem mem_genSub_Edd (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (V : Submodule ℂ D) {u : D}
    (hu : u ∈ genSub E V) : ofD u ∈ genSub (Edd ε E) (cjV V) := by
  have hle : genSub E V ≤ (genSub (Edd ε E) (cjV V)).comap (ofDL (D := D)) := by
    refine genSub_le' E (fun v hv => (le_genSub' (Edd ε E) (cjV V) ((mem_cjV (ofD v)).2 hv) : ofD v ∈ genSub (Edd ε E) (cjV V))) fun a b v hv => ?_
    show ofD (E a b v) ∈ _
    rw [ofD_E ε E a b v]
    exact Submodule.smul_mem _ _ (genSub_stable' (Edd ε E) (cjV V) _ _ (hv : ofD v ∈ genSub (Edd ε E) (cjV V)))
  exact hle hu

def Tf (ε : Fin n → Bool) (f : Fin n → D) : Fin n → cjSub D := fun c => ofD (sg ε c • f (Fin.rev c))

def Tfh (ε : Fin n → Bool) : (Fin n → D) →+ (Fin n → cjSub D) where
  toFun := Tf ε
  map_zero' := by
    funext c
    show ofD (sg ε c • (0 : D)) = 0
    rw [smul_zero]; rfl
  map_add' f g := by
    funext c
    show ofD (sg ε c • (f (Fin.rev c) + g (Fin.rev c))) = ofD (sg ε c • f (Fin.rev c)) + ofD (sg ε c • g (Fin.rev c))
    rw [smul_add, ofD_add]

theorem Tf_smul (ε : Fin n → Bool) (z : ℂ) (f : Fin n → D) : Tfh ε (z • f) = conj z • Tfh ε f := by
  funext c
  show ofD (sg ε c • (z • f (Fin.rev c))) = conj z • ofD (sg ε c • f (Fin.rev c))
  rw [smul_ofD, Complex.conj_conj, smul_comm]

theorem Tf_inj (ε : Fin n → Bool) {g : Fin n → D} (h : Tf ε g = 0) : g = 0 := by
  funext c
  have h1 := congrFun h (Fin.rev c)
  simp only [Tf, Fin.rev_rev, Pi.zero_apply] at h1
  have h2 : sg ε (Fin.rev c) • g c = 0 := ofD_injective (h1.trans ofD_zero.symm)
  exact (smul_eq_zero.mp h2).resolve_left (sg_ne ε _)

theorem weightVector_tensor_eq_dual (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ D) (f : Fin n → D) :
    eeV (Edd ε E) (Tf ε f) = Tf ε (eeVd E f) := by
  funext d
  simp only [Tf, eeV, eeVd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, prj, LinearMap.proj_apply, Edd_ofD, LinearMap.map_smul, smul_smul]
  rw [← ofD_sum]
  congr 1
  rw [smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  conv_rhs => rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Fin.revPerm_apply]
  rw [← neg_smul]
  congr 1
  linear_combination (-sg ε d) * sg_sq ε c

theorem prodShift_eq {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = ((List.ofFn θ).map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod := by
  unfold prodShift; rw [List.map_ofFn]; rfl

theorem prodShift_aeval {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A θ = Polynomial.aeval A (∏ t, (Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  unfold prodShift
  congr 2
  funext t
  simp [Algebra.algebraMap_eq_smul_one]

theorem prodShift_rev {X : Type*} [AddCommGroup X] [Module ℂ X] (A : Module.End ℂ X) (θ : Fin n → ℝ) :
    prodShift A (fun t => θ (Fin.rev t)) = prodShift A θ := by
  rw [prodShift_aeval, prodShift_aeval]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun t => Polynomial.X - Polynomial.C ((θ t : ℝ) : ℂ))

theorem list_inter {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (T : X →+ Y) (hs : ∀ (z : ℂ) (x : X), T (z • x) = conj z • T x) (A : Module.End ℂ Y)
    (B : Module.End ℂ X) (hAB : ∀ x, T (B x) = A (T x)) (L : List ℝ) (x : X) :
    T ((L.map fun r : ℝ => B - ((r : ℝ) : ℂ) • (1 : Module.End ℂ X)).prod x) =
      (L.map fun r : ℝ => A - ((r : ℝ) : ℂ) • (1 : Module.End ℂ Y)).prod (T x) := by
  induction L with
  | nil => simp
  | cons r L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [map_sub, hAB, hs, Complex.conj_ofReal, ih]

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.DualRepresentationReversal
end
end

section
noncomputable section

open ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS DualRepresentationReversal

theorem dualKType_of_standardKType (n : ℕ) (hK : LowestKTypeEulerTensorStandard n) : LowestKTypeEulerTensorDual n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgl hp hq f hf
  have hint' : ∀ a, ∃ m : ℤ, lamd lam a - ((n : ℝ) - 1) / 2 = (m : ℝ) := fun a => by
    obtain ⟨m, hm⟩ := hint (Fin.rev a)
    exact ⟨-m - ((n : ℤ) - 1), by push_cast; simp only [lamd]; linarith⟩
  have hc' : ∀ v ∈ cjV V, casimir (Edd ε E) v = (casVal (lamd lam) : ℂ) • v := fun v hv => by
    rw [← ofD_toD v, casimir_Edd, hc _ ((mem_cjV v).1 hv), casVal_rev, ofD_smul, Complex.conj_ofReal]
  have hVK' : ∀ k ∈ Kset (ε ∘ Fin.rev), ∀ v ∈ cjV V, ∃ w ∈ cjV V, (w : Cj H) = sdd σ k v :=
    fun k hk v hv => by
      obtain ⟨w, hw, hweq⟩ := hVK (sub k) (K_sub hk) (toD v) ((mem_cjV v).1 hv)
      exact ⟨ofD w, (mem_cjV _).2 hw, hweq⟩
  have hgl' := gapLap_rev hgl
  have key := hK (ε ∘ Fin.rev) (lamd lam) h (Cj H) (sdd σ) (cjSub D) (Edd ε E) (cjV V) (urep_sdd hσ)
    (derived_sdd hD) (kirr_cjV hV) hc' hVK' hint' hgl'.1 hgl' (by rwa [pOf_rev]) (by rwa [qOf_rev])
    (Tf ε f) (fun c => mem_genSub_Edd ε E V (Submodule.smul_mem _ _ (hf _)))
  have hθ : thV (lamd lam) = fun t => thVd lam (Fin.rev t) := by
    funext t; simp only [thV, thVd, lamd]
  rw [hθ, prodShift_rev] at key
  have hl := list_inter (Tfh ε) (Tf_smul ε) (eeV (Edd ε E)) (eeVd E) (fun g => (weightVector_tensor_eq_dual ε E g).symm)
    (List.ofFn (thVd lam)) f
  rw [← prodShift_eq, ← prodShift_eq] at hl
  have h2 : Tfh ε (prodShift (eeVd E) (thVd lam) f) = 0 := by rw [hl]; exact key
  exact Tf_inj ε h2

theorem k1Vd (n : ℕ) : LowestKTypeEulerTensorDual n :=
  dualKType_of_standardKType n (k1V n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem sg_sq (ε : Fin n → Bool) (a : Fin n) : sg ε a * sg ε a = 1 := by
  unfold sg
  split_ifs <;> norm_num

theorem sg_ne (ε : Fin n → Bool) (a : Fin n) : sg ε a ≠ 0 := by
  unfold sg
  split_ifs <;> norm_num

theorem sg_comp (ε : Fin n → Bool) (a : Fin n) : sg (ε ∘ Fin.rev) a = sg ε (Fin.rev a) := rfl

theorem sum_rev {X : Type*} [AddCommMonoid X] (f : Fin n → X) : ∑ a, f (Fin.rev a) = ∑ a, f a :=
  Equiv.sum_comp Fin.revPerm f

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => (-(sg ε (Fin.rev a) * sg ε (Fin.rev b))) • E (Fin.rev b) (Fin.rev a)

theorem twE_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (v : M) :
    twE ε E a b v = (-(sg ε (Fin.rev a) * sg ε (Fin.rev b))) • E (Fin.rev b) (Fin.rev a) v := rfl

theorem comp_rev_rev (ε : Fin n → Bool) : (ε ∘ Fin.rev) ∘ Fin.rev = ε := by
  funext a
  simp [Fin.rev_rev]

theorem twE_twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    twE (ε ∘ Fin.rev) (twE ε E) = E := by
  funext a b
  simp only [twE, sg_comp, Fin.rev_rev, smul_smul]
  convert one_smul ℂ (E a b) using 2
  linear_combination (sg ε b * sg ε b) * sg_sq ε a + sg_sq ε b

theorem twE_gl {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    IsGlRep (twE ε E) := by
  intro a b c d
  have h := hE (Fin.rev b) (Fin.rev a) (Fin.rev d) (Fin.rev c)
  rw [sub_eq_iff_eq_add] at h
  simp only [twE, smul_mul_smul_comm, h, Fin.rev_inj]
  simp only [@eq_comm (Fin n) b c, @eq_comm (Fin n) d a]
  split_ifs <;> subst_vars <;> simp only [sg] <;> split_ifs <;> module

theorem casimir_twE (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) :
    casimir (twE ε E) = casimir E := by
  unfold casimir
  simp only [twE, smul_mul_smul_comm]
  have hs : ∀ a b : Fin n,
      (-(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * -(sg ε (Fin.rev b) * sg ε (Fin.rev a))) = 1 := by
    intro a b
    linear_combination (sg ε (Fin.rev b) * sg ε (Fin.rev b)) * sg_sq ε (Fin.rev a) + sg_sq ε (Fin.rev b)
  simp only [hs, one_smul]
  have h1 : ∀ a : Fin n, ∑ b, E (Fin.rev b) (Fin.rev a) * E (Fin.rev a) (Fin.rev b) =
      ∑ b, E b (Fin.rev a) * E (Fin.rev a) b :=
    fun a => sum_rev (fun b => E b (Fin.rev a) * E (Fin.rev a) b)
  simp only [h1]
  exact (sum_rev (fun a => ∑ b, E b a * E a b)).trans Finset.sum_comm

theorem kst_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (h : IsKStableSub ε E S) : IsKStableSub (ε ∘ Fin.rev) (twE ε E) S := by
  intro a b hab v hv
  rw [twE_apply]
  exact S.smul_mem _ (h _ _ hab.symm v hv)

theorem kst_tw_iff {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} :
    IsKStableSub (ε ∘ Fin.rev) (twE ε E) S ↔ IsKStableSub ε E S := by
  refine ⟨fun h => ?_, kst_tw⟩
  have h' := kst_tw (ε := ε ∘ Fin.rev) h
  rwa [twE_twE, comp_rev_rev] at h'

theorem khw_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {v : M}
    (h : IsKHWVec ε E μ v) : IsKHWVec (ε ∘ Fin.rev) (twE ε E) (fun a => -μ (Fin.rev a)) v := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [twE_apply, h1, sg_sq, smul_smul]
    congr 1
    push_cast
    ring
  · rw [twE_apply, h2 _ _ (Fin.rev_lt_rev.2 hab) he.symm, smul_zero]

theorem genSub_tw (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M) :
    genSub (twE ε E) S = genSub E S := by
  unfold genSub
  congr 1
  ext T
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun hT a b v hv => ?_, fun hT a b v hv => ?_⟩
  · rw [← twE_twE ε E, twE_apply]
    exact T.smul_mem _ (hT _ _ v hv)
  · rw [twE_apply]
    exact T.smul_mem _ (hT _ _ v hv)

theorem kirr_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {Λ : Fin n → ℝ}
    {S : Submodule ℂ M} (h : IsKIrrHW ε E Λ S) :
    IsKIrrHW (ε ∘ Fin.rev) (twE ε E) (fun a => -Λ (Fin.rev a)) S := by
  obtain ⟨h1, h2, h3, w, hw, hw0, hw1⟩ := h
  exact ⟨h1, kst_tw h2, fun S' hS' hk => h3 S' hS' (kst_tw_iff.1 hk), w, hw, hw0, khw_tw hw1⟩

end Alg

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

section Tens

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tensV_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + (if c = a then f b else 0) := by
  simp only [tensV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

theorem tensVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - (if c = b then f a else 0) := by
  simp only [tensVd, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply]
  split_ifs <;> simp [prj]

theorem eeV_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeV E f d = ∑ c, E c d (f c) := by
  simp [eeV, prj, LinearMap.sum_apply]

theorem eeVd_apply' (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (d : Fin n) :
    eeVd E f d = -∑ c, E d c (f c) := by
  simp [eeVd, prj, LinearMap.sum_apply]

def twT (ε : Fin n → Bool) : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
  LinearMap.pi fun c => sg ε (Fin.rev c) • prj (Fin.rev c)

theorem twT_apply (ε : Fin n → Bool) (f : Fin n → M) (c : Fin n) :
    twT ε f c = sg ε (Fin.rev c) • f (Fin.rev c) := by
  simp [twT, prj]

theorem twT_eq_zero {ε : Fin n → Bool} {f : Fin n → M} (h : twT ε f = 0) : f = 0 := by
  funext c
  have := congrFun h (Fin.rev c)
  rw [twT_apply, Fin.rev_rev] at this
  exact (smul_eq_zero.1 this).resolve_left (sg_ne ε c)

theorem twT_tens (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) :
    tensV (twE ε E) a b (twT ε f) = twT ε (twE ε (tensVd E) a b f) := by
  funext c
  rw [tensV_apply', twT_apply, twT_apply, twE_apply, twE_apply, map_smul (twT ε), Pi.smul_apply,
    twT_apply, tensVd_apply', map_smul]
  simp only [Fin.rev_inj]
  by_cases hc : c = a
  · subst hc
    simp only [if_true]
    unfold sg; split_ifs <;> module
  · simp [hc]

theorem twT_ee (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) :
    eeV (twE ε E) (twT ε f) = twT ε (eeVd E f) := by
  funext d
  rw [eeV_apply', twT_apply, eeVd_apply', smul_neg, Finset.smul_sum,
    ← sum_rev (fun c => sg ε (Fin.rev d) • E (Fin.rev d) c (f c)), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [twT_apply, twE_apply, map_smul, smul_smul, ← neg_smul]
  congr 1
  linear_combination (-sg ε (Fin.rev d)) * sg_sq ε (Fin.rev c)

theorem mem_Xs {A : Module.End ℂ (Fin n → M)} {S : Submodule ℂ M} {θ : ℝ} {f : Fin n → M} :
    f ∈ Xs A S θ ↔ (∀ c, f c ∈ S) ∧ A f = ((θ : ℝ) : ℂ) • f := by
  simp [Xs, Submodule.mem_inf, Submodule.mem_pi, LinearMap.mem_ker, sub_eq_zero]

theorem xs_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M} {θ : ℝ}
    {f : Fin n → M} (h : f ∈ Xs (eeVd E) S θ) : twT ε f ∈ Xs (eeV (twE ε E)) S θ := by
  rw [mem_Xs] at h ⊢
  refine ⟨fun c => ?_, ?_⟩
  · rw [twT_apply]; exact S.smul_mem _ (h.1 _)
  · rw [twT_ee, h.2, map_smul]

theorem khwT_tw {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ}
    {f : Fin n → M} (h : IsKHWVec ε (tensVd E) μ f) :
    IsKHWVec (ε ∘ Fin.rev) (tensV (twE ε E)) (fun a => -μ (Fin.rev a)) (twT ε f) := by
  have h' := khw_tw h
  exact ⟨fun a => by rw [twT_tens, h'.1, map_smul], fun a b hab he => by
    rw [twT_tens, h'.2 a b hab he, map_zero]⟩

end Tens

section Wt

theorem rhoN_tw (ε : Fin n → Bool) (a : Fin n) : rhoN (ε ∘ Fin.rev) a = -rhoN ε (Fin.rev a) := by
  unfold rhoN
  simp only [Function.comp_apply]
  have h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b ≠ ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  have h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) ≠ ε (Fin.rev a)).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b ≠ ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  rw [h1, h2]; ring

theorem rhoC_tw (ε : Fin n → Bool) (a : Fin n) : rhoC (ε ∘ Fin.rev) a = -rhoC ε (Fin.rev a) := by
  unfold rhoC
  simp only [Function.comp_apply]
  have h1 : (univ.filter fun b => a < b ∧ ε (Fin.rev b) = ε (Fin.rev a)).card =
      (univ.filter fun b => b < Fin.rev a ∧ ε b = ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  have h2 : (univ.filter fun b => b < a ∧ ε (Fin.rev b) = ε (Fin.rev a)).card =
      (univ.filter fun b => Fin.rev a < b ∧ ε b = ε (Fin.rev a)).card := by
    refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      exact ⟨Fin.rev_lt_rev.2 hb.1, hb.2⟩
    · intro b hb; simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      refine ⟨?_, by simpa using hb.2⟩
      simpa using Fin.rev_lt_rev.2 hb.1
    · intro b _; simp
    · intro b _; simp
  rw [h1, h2]; ring

theorem lowK_tw (ε : Fin n → Bool) (ν : Fin n → ℝ) :
    lowK (ε ∘ Fin.rev) (fun a => -ν (Fin.rev a)) = fun a => -lowK ε ν (Fin.rev a) := by
  funext a
  simp only [lowK, Pi.add_apply, Pi.sub_apply, rhoN_tw, rhoC_tw]
  ring

theorem casVal_tw (lam : Fin n → ℝ) : casVal (fun a => -lam (Fin.rev a)) = casVal lam := by
  unfold casVal nsq dot
  simp only [neg_mul_neg]
  rw [sum_rev (fun a => lam a * lam a)]

theorem pOf_tw (ε : Fin n → Bool) : pOf (ε ∘ Fin.rev) = pOf ε := by
  unfold pOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

theorem qOf_tw (ε : Fin n → Bool) : qOf (ε ∘ Fin.rev) = qOf ε := by
  unfold qOf
  refine Finset.card_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ <;> intro b hb <;> simp_all

theorem gapLap_tw {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} (hg : GapLap ε lam h) :
    GapLap (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun a b hab => ?_, fun a b hab => ?_, ?_⟩
  · have := h1 (Fin.rev_lt_rev.2 hab)
    simp only; linarith
  · have := h2 (Fin.rev a) (Fin.rev b) hab
    rw [abs_sub_comm] at this
    simp only; rwa [neg_sub_neg]
  · have e : hNeed (ε ∘ Fin.rev) = hNeed ε := by unfold hNeed; rw [pOf_tw, qOf_tw]
    rw [e]; exact h3

theorem root_rev (a b x : Fin n) : root (Fin.rev b) (Fin.rev a) x = -root a b (Fin.rev x) := by
  have e : ∀ i j : Fin n, (j = Fin.rev i ↔ Fin.rev j = i) := fun i j => by
    constructor <;> rintro rfl <;> simp
  simp only [root, Pi.sub_apply, Pi.single_apply, e]
  ring

theorem cone_ev (k : Fin n → Fin n → ℕ) (y : Fin n) :
    (∑ a, ∑ b, if a < b then (k a b : ℝ) • root a b else 0) y =
      ∑ a, ∑ b, if a < b then (k a b : ℝ) * root a b y else 0 := by
  simp only [Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem cone_rev {β : Fin n → ℝ} (h : InRootCone (fun a => -β (Fin.rev a))) : InRootCone β := by
  obtain ⟨m, hm⟩ := h
  refine ⟨fun a b => m (Fin.rev b) (Fin.rev a), ?_⟩
  funext x
  have hx := congrFun hm (Fin.rev x)
  simp only [Fin.rev_rev] at hx
  rw [cone_ev] at hx
  rw [cone_ev, show β x = -(-β x) by ring, hx, ← sum_rev, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← sum_rev, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Fin.rev_rev, Fin.rev_lt_rev, root_rev]
  split_ifs <;> ring

end Wt

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
end
end

section
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK

variable {n : ℕ}

def phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.reindexRingEquiv (R := ℂ) (e := (Fin.revPerm : Fin n ≃ Fin n))).toRingHom.comp
    (starRingEnd ℂ).mapMatrix

theorem phiR_apply (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    phiR g i j = star (g (Fin.rev i) (Fin.rev j)) := by
  simp [phiR, Matrix.reindexRingEquiv, Fin.revPerm_symm]

theorem phiR_phiR (g : Matrix (Fin n) (Fin n) ℂ) : phiR (phiR g) = g := by
  ext i j; simp [phiR_apply]

theorem phiR_conjT (g : Matrix (Fin n) (Fin n) ℂ) : phiR gᴴ = (phiR g)ᴴ := by
  ext i j; simp [phiR_apply, conjTranspose_apply]

theorem phiR_J (ε : Fin n → Bool) : phiR (Jm (ε ∘ Fin.rev)) = Jm ε := by
  ext i j
  by_cases h : i = j
  · subst h; simp [phiR_apply, Jm]; split_ifs <;> simp
  · simp [phiR_apply, Jm, h]

theorem phiR_smul_real (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    phiR ((t : ℂ) • X) = (t : ℂ) • phiR X := by
  ext i j; simp [phiR_apply]

theorem phiR_cont : Continuous (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  have : (phiR : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) =
      fun g => (g.submatrix Fin.rev Fin.rev).map star := by
    funext g; ext i j; simp [phiR_apply]
  rw [this]
  exact (continuous_id.matrix_submatrix _ _).matrix_map continuous_star

theorem phiR_exp (A : Matrix (Fin n) (Fin n) ℂ) : phiR (NormedSpace.exp A) = NormedSpace.exp (phiR A) := by
  simp only [NormedSpace.exp_eq_tsum_rat]
  rw [Function.LeftInverse.map_tsum (g := (phiR : Matrix (Fin n) (Fin n) ℂ →+* Matrix (Fin n) (Fin n) ℂ))
    _ phiR_cont phiR_cont phiR_phiR]
  simp only [map_rat_smul, map_pow]

theorem phiR_UJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset (ε ∘ Fin.rev)) :
    phiR g ∈ UJset ε := by
  have hg' : gᴴ * Jm (ε ∘ Fin.rev) * g = Jm (ε ∘ Fin.rev) := hg
  show (phiR g)ᴴ * Jm ε * phiR g = Jm ε
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, hg']

theorem phiR_K {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset (ε ∘ Fin.rev)) :
    phiR k ∈ Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu ⊢
    rw [← phiR_conjT, ← map_mul, hu, map_one]
  · rw [← phiR_J, ← map_mul, hc, map_mul]

theorem phiR_G {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    inG ε (phiR X) := by
  have h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0 := hX
  show (phiR X)ᴴ * Jm ε + Jm ε * phiR X = 0
  rw [← phiR_conjT, ← phiR_J, ← map_mul, ← map_mul, ← map_add, h, map_zero]

theorem actM_tw {M : Type*} [AddCommGroup M] [Module ℂ M] {ε : Fin n → Bool}
    (E : Fin n → Fin n → Module.End ℂ M) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG (ε ∘ Fin.rev) X) :
    actM E (phiR X) = actM (twE ε E) X := by
  have h : Xᴴ * Jm (ε ∘ Fin.rev) + Jm (ε ∘ Fin.rev) * X = 0 := hX
  have key : ∀ a b, star (X b a) = -(sg ε (Fin.rev a) * sg ε (Fin.rev b)) * X a b := by
    intro a b
    have e := congrFun (congrFun h a) b
    simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.conjTranspose_apply, Matrix.zero_apply] at e
    change star (X b a) * sg ε (Fin.rev b) + sg ε (Fin.rev a) * X a b = 0 at e
    linear_combination (sg ε (Fin.rev b)) * e - star (X b a) * sg_sq ε (Fin.rev b)
  show ∑ a, ∑ b, (phiR X) a b • E a b = ∑ a, ∑ b, X a b • twE ε E a b
  calc ∑ a, ∑ b, (phiR X) a b • E a b
      = ∑ a, ∑ b, (phiR X) (Fin.rev a) (Fin.rev b) • E (Fin.rev a) (Fin.rev b) := by
        rw [← sum_rev (fun a => ∑ b, (phiR X) a b • E a b)]
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (sum_rev (fun b => (phiR X) (Fin.rev a) b • E (Fin.rev a) b)).symm
    _ = ∑ b, ∑ a, (phiR X) (Fin.rev a) (Fin.rev b) • E (Fin.rev a) (Fin.rev b) := Finset.sum_comm
    _ = ∑ a, ∑ b, X a b • twE ε E a b := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [phiR_apply, Fin.rev_rev, Fin.rev_rev, key]
        simp only [twE, smul_smul]
        congr 1; ring

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem urep_tw {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : IsURepOn (UJset (ε ∘ Fin.rev)) (fun g => σ (phiR g)) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hσ
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (phiR_UJ hg) v, fun v => ?_⟩
  · simp only [map_one, h1]
  · simp only [map_mul]; exact h2 _ (phiR_UJ ha) _ (phiR_UJ hb)
  · exact (h4 v).comp phiR_cont.continuousOn (fun g hg => phiR_UJ hg)

theorem derived_tw {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} (hD : IsDerivedOn ε σ D E) :
    IsDerivedOn (ε ∘ Fin.rev) (fun g => σ (phiR g)) D (twE ε E) where
  glRep := twE_gl hD.glRep
  kStable := fun k hk v hv => hD.kStable _ (phiR_K hk) v hv
  deriv := fun X hX v => by
    have := hD.deriv (phiR X) (phiR_G hX) v
    rw [actM_tw E hX] at this
    have hf : (fun t : ℝ => σ (phiR (NormedSpace.exp ((t : ℂ) • X))) (v : H)) =
        fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • phiR X)) (v : H) := by
      funext t; rw [phiR_exp, phiR_smul_real]
    show HasDerivAt (fun t : ℝ => σ (phiR (NormedSpace.exp ((t : ℂ) • X))) (v : H)) _ 0
    rw [hf]; exact this

end Rep

theorem dualLowestKType_of_standard (hK : EigenspaceWeightConeStandard n) : EigenspaceWeightConeDual n := by
  intro ε lam h H _ _ _ σ D E V s hσ hD hV hc hVK hint hanti hgap hp hq
  have hV' : IsKIrrHW (ε ∘ Fin.rev) (twE ε E) (lowK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a))) V := by
    rw [lowK_tw]; exact kirr_tw hV
  have hc' : ∀ v ∈ V, casimir (twE ε E) v = (casVal (fun a => -lam (Fin.rev a)) : ℂ) • v := by
    intro v hv; rw [casimir_twE, casVal_tw]; exact hc v hv
  have hint' : ∀ a, ∃ m : ℤ, (fun a => -lam (Fin.rev a)) a - ((n : ℝ) - 1) / 2 = (m : ℝ) := by
    intro a
    obtain ⟨m, hm⟩ := hint (Fin.rev a)
    refine ⟨-m - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  have hgap' := gapLap_tw hgap
  obtain ⟨K1, K2⟩ := hK (ε ∘ Fin.rev) (fun a => -lam (Fin.rev a)) h H (fun g => σ (phiR g)) D (twE ε E) V
    (Fin.rev s) (urep_tw hσ) (derived_tw hD) hV' hc' (fun k hk v hv => hVK _ (phiR_K hk) v hv) hint'
    hgap'.1 hgap' (by rwa [pOf_tw]) (by rwa [qOf_tw])
  have hθ : thV (fun a => -lam (Fin.rev a)) (Fin.rev s) = thVd lam s := by simp [thV, thVd]
  have hG : genSub (twE ε E) V = genSub E V := genSub_tw ε E V
  have hW : lowK (ε ∘ Fin.rev) ((fun a => -lam (Fin.rev a)) + Pi.single (Fin.rev s) 1) =
      fun a => -lowK ε (lam - Pi.single s 1) (Fin.rev a) := by
    rw [← lowK_tw]
    congr 1
    funext a
    have e : (a = Fin.rev s ↔ Fin.rev a = s) :=
      ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
    simp only [Pi.add_apply, Pi.sub_apply, Pi.single_apply, e]
    ring
  refine ⟨fun μ f hf hf0 hμ => ?_, fun f₁ f₂ h1 h2 hw1 hw2 => ?_⟩
  · have hf' := xs_tw (ε := ε) hf
    rw [← hθ, ← hG] at hf'
    have := K1 (fun a => -μ (Fin.rev a)) (twT ε f) hf' (fun h0 => hf0 (twT_eq_zero h0)) (khwT_tw hμ)
    rw [hW] at this
    apply cone_rev
    convert this using 1
    funext a
    simp only [Pi.sub_apply]
    ring
  · have h1' := xs_tw (ε := ε) h1
    rw [← hθ, ← hG] at h1'
    have h2' := xs_tw (ε := ε) h2
    rw [← hθ, ← hG] at h2'
    have k1 := khwT_tw hw1
    rw [← hW] at k1
    have k2 := khwT_tw hw2
    rw [← hW] at k2
    obtain ⟨c₁, c₂, hne, heq⟩ := K2 _ _ h1' h2' k1 k2
    refine ⟨c₁, c₂, hne, twT_eq_zero (ε := ε) ?_⟩
    rw [map_add, map_smul, map_smul]
    exact heq

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK.TwistedDualLemmas
end
end

section
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

theorem k2Vd (n : ℕ) : EigenspaceWeightConeDual n :=
  TwistedDualLemmas.dualLowestKType_of_standard (k2V n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end

section
noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS

theorem casimirValue_sub_single {n : ℕ} (lam : Fin n → ℝ) (s : Fin n) :
    casVal (lam - Pi.single s 1) = casVal lam + n + 2 * thVd lam s := by
  have hd1 : dot lam (Pi.single s 1) = lam s := by simp [dot, Pi.single_apply]
  have hd2 : nsq (Pi.single s (1 : ℝ)) = 1 := by simp [nsq, dot, Pi.single_apply]
  unfold casVal thVd
  rw [nsq_sub', hd1, hd2]
  ring

theorem three_add_le_gapBound_dual {n : ℕ} (ε : Fin n → Bool) : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 3 ≤ hNeed ε := by
  unfold hNeed
  have h1 := le_max_right (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ))
  have h2 := le_max_left (2 + max (3 * (n : ℝ) / 2) (1 + (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ)))
    (max (16 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ) + 8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) + 2)
      (8 * Real.sqrt (2 * (min (pOf ε) (qOf ε) : ℝ)) *
        (4 * max (2 * (n : ℝ) * (min (pOf ε) (qOf ε) : ℝ)) (2 * ((qOf ε : ℝ) - 1) * (n : ℝ) ^ 2) + 1)))
  linarith

theorem k3Vd (n : ℕ) : QuotientHighestWeightTensorDual n := by
  intro ε lam h H _ _ _ σ D E V s N _ _ EN φ x hσ hD hV hc hVK hint hmono hgap hp hq hmono' hEN hUN hφ hx hφx
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  have hKU := isKUnitary_of_isInfUnitary hU
  have hKUN := isKUnitary_of_isInfUnitary hUN
  have hVk : IsKStableSub ε E V := hV.2.1
  have hVfd : FiniteDimensional ℂ V := hV.1
  have hGs : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := fun a b v hv => generated_submodule_stable_under_action V a b hv
  have hXg : ∀ f ∈ Xs (eeVd E) (genSub E V) (thVd lam s), ∀ c, f c ∈ genSub E V :=
    fun f hf => (mem_euler_eigenspace_iff.1 hf).1
  have hps : ∀ k (u v : Fin n → ℝ), kirrPs k (u - v) = kirrPs k u - kirrPs k v := by
    intro k u v; rw [← k3vdPs_apply, map_sub, k3vdPs_apply, k3vdPs_apply]
  have hpa : ∀ k (u v : Fin n → ℝ), kirrPs k (u + v) = kirrPs k u + kirrPs k v := by
    intro k u v; rw [← k3vdPs_apply, map_add, k3vdPs_apply, k3vdPs_apply]
  have hN3 := three_add_le_gapBound_dual ε
  have hnpq : 0 ≤ (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) := by positivity
  have hh := hgap.2.2
  set Y := (Xs (eeVd E) (genSub E V) (thVd lam s)).map φ with hYdef

  have hYst : ∀ a b, ∀ y ∈ Y, EN a b y ∈ Y := by
    intro a b y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    rw [← hφ a b f (hXg f hf)]
    exact Submodule.mem_map_of_mem (euler_eigenspace_stable_under_action hE hGs a b hf)

  have hcasY : ∀ y ∈ Y, casimir EN y = (casVal (lam - Pi.single s 1) : ℂ) • y := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hy
    have hfg := hXg f hf
    have h1 : casimir EN (φ f) = φ (casimir (tensVd E) f) := by
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [← hφ b a f hfg, ← hφ a b _ (dualTensorAction_mem hGs b a hfg)]
    have h2 := ((tens_statement n) (↥D) E hE).2.2.2 f
    have h3 : (fun c => casimir E (f c)) = (casVal lam : ℂ) • f :=
      funext fun c => casimir_genSub hE hc (f c) (hfg c)
    have hnum : (casVal (lam - Pi.single s 1) : ℂ) = (casVal lam : ℂ) + n + 2 * ((thVd lam s : ℝ) : ℂ) := by
      rw [casimirValue_sub_single]; push_cast; ring
    rw [h1, h2, h3, (mem_euler_eigenspace_iff.1 hf).2, smul_smul, ← add_smul, ← add_smul, ← hnum, map_smul]

  have hK2 := (k2Vd n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hgap hp hq).1
  have hcone : ∀ (μ : Fin n → ℝ) (y : N), y ∈ Y → y ≠ 0 → IsKHWVec ε EN μ y →
      InRootCone (μ - lowK ε (lam - Pi.single s 1)) :=
    fun μ y hy hy0 hμ => image_weights_in_root_cone hE hU hVfd hVk hφ hK2 hy hy0 hμ

  have hx0 : x ≠ 0 := by rintro rfl; exact hφx (map_zero φ)
  have hinj : ∀ t, t ≠ s → thVd lam t ≠ thVd lam s := by
    intro t hts heq
    apply hts
    have : lam t = lam s := by unfold thVd at heq; linarith
    exact hmono.injective this
  set Fs : ℂ[X] := ∏ t ∈ univ.erase s, (X - C (((thVd lam t : ℝ) : ℂ))) with hFs
  set P : Module.End ℂ (Fin n → D) := aeval (eeVd E) Fs with hP
  have hPg : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → ∀ c, P f c ∈ genSub E V := by
    intro f hf
    have := aeval_mem_invariant_submodule (eeVd E) (Submodule.pi Set.univ fun _ => genSub E V)
      (fun g hg => mem_pi_submodule_iff.2 (euler_tensor_dual_mem_of_stable hGs (mem_pi_submodule_iff.1 hg))) Fs f (mem_pi_submodule_iff.2 hf)
    exact mem_pi_submodule_iff.1 this
  have hPc : ∀ a b, Commute P (tensVd E a b) := fun a b =>
    aeval_commute_of_commute (eeVd E) (tensVd E a b) (euler_tensor_dual_commute_gl_action hE a b) Fs
  have hPX : ∀ f : Fin n → D, (∀ c, f c ∈ genSub E V) → P f ∈ Xs (eeVd E) (genSub E V) (thVd lam s) := by
    intro f hf
    have hk1 := k1Vd n ε lam h H σ D E V hσ hD hV hc hVK hint hmono hgap hp hq f hf
    rw [shifted_product_eq_aeval, ← Finset.mul_prod_erase univ _ (mem_univ s), map_mul, Module.End.mul_apply,
      map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hk1
    refine mem_euler_eigenspace_iff.2 ⟨hPg f hf, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at hk1
    exact hk1
  have hPx : P x = (Fs.eval ((thVd lam s : ℝ) : ℂ)) • x := by
    apply Module.End.aeval_apply_of_hasEigenvector
    refine ⟨Module.End.mem_eigenspace_iff.2 (mem_euler_eigenspace_iff.1 hx).2, hx0⟩
  have hFs0 : Fs.eval ((thVd lam s : ℝ) : ℂ) ≠ 0 := by
    rw [hFs, eval_prod, Finset.prod_ne_zero_iff]
    intro t ht
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    exact_mod_cast (hinj t (Finset.ne_of_mem_erase ht)).symm
  have hφPx : φ (P x) ≠ 0 := by
    rw [hPx, map_smul]; exact smul_ne_zero hFs0 hφx
  have hGen := (gen_statement n ε (↥D) E V hE hVk).2
  obtain ⟨u, huV, hu⟩ := exists_commuting_projection_image V hGen P hPg hPc φ hφ (hXg x hx) hφPx

  have hpiV : ∀ a b, ε a = ε b → ∀ w ∈ Submodule.pi Set.univ (fun _ : Fin n => V),
      tensVd E a b w ∈ Submodule.pi Set.univ (fun _ : Fin n => V) := by
    intro a b hab w hw
    refine mem_pi_submodule_iff.2 fun c => ?_
    rw [tensor_dual_action_apply_component]
    refine sub_mem (hVk a b hab _ (mem_pi_submodule_iff.1 hw c)) ?_
    split_ifs
    · exact mem_pi_submodule_iff.1 hw a
    · exact zero_mem _
  have hVg : ∀ w ∈ Submodule.pi Set.univ (fun _ : Fin n => V), ∀ c, w c ∈ genSub E V :=
    fun w hw c => le_generatedSubmodule_dual V (mem_pi_submodule_iff.1 hw c)
  have hfPV : ∀ a b, ε a = ε b → ∀ w ∈ Submodule.pi Set.univ (fun _ : Fin n => V),
      (φ ∘ₗ P) (tensVd E a b w) = EN a b ((φ ∘ₗ P) w) := by
    intro a b _ w hw
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, (hPc a b).eq, Module.End.mul_apply, hφ a b _ (hPg w (hVg w hw))]
  have hfdpi : FiniteDimensional ℂ (Submodule.pi Set.univ (fun _ : Fin n => V)) := pi_submodule_finiteDimensional V
  set Z := (Submodule.pi Set.univ (fun _ : Fin n => V)).map (φ ∘ₗ P) with hZ
  have hZst : IsKStableSub ε EN Z := by
    intro a b hab z hz
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
    rw [← hfPV a b hab w hw]
    exact Submodule.mem_map_of_mem (hpiV a b hab w hw)
  have hZne : Z ≠ ⊥ := by
    intro hZb
    have : (φ ∘ₗ P) u ∈ Z := Submodule.mem_map_of_mem (mem_pi_submodule_iff.2 huV)
    rw [hZb, Submodule.mem_bot] at this
    exact hu this
  obtain ⟨y0, hy0Z, hy00, ν0, hν0⟩ := exists_khw hEN hKUN inferInstance hZst hZne
  obtain ⟨w0, hw0, rfl⟩ := Submodule.mem_map.1 hy0Z
  have hy0Y : (φ ∘ₗ P) w0 ∈ Y := Submodule.mem_map_of_mem (hPX w0 (hVg w0 hw0))
  have hν0lo : ∀ k, kirrPs k ν0 ≤ kirrPs k (lowK ε lam) := by
    obtain ⟨u1, hu1, hkhw, hfu1⟩ := exists_highest_weight_lift_pi hKU (φ ∘ₗ P) hfdpi
      (fun a b hab w hw => hpiV a b hab w hw) hfPV hw0 hν0
    have hu10 : u1 ≠ 0 := by rintro rfl; rw [map_zero] at hfu1; exact hy00 hfu1.symm
    obtain ⟨c, hc0⟩ := Function.ne_iff.1 hu10
    have hwt : ∀ a, E a a (u1 c) = (((ν0 + Pi.single c (1 : ℝ) : Fin n → ℝ) a : ℝ) : ℂ) • u1 c := by
      intro a
      have := congrFun (hkhw.1 a) c
      rw [tensor_dual_action_apply_component, Pi.smul_apply] at this
      by_cases hca : c = a
      · subst hca
        simp only [if_true] at this
        rw [sub_eq_iff_eq_add] at this
        rw [this]; simp [add_smul, Pi.add_apply]
      · simp only [hca, if_false, sub_zero] at this
        rw [this]; simp [Pi.add_apply, Pi.single_apply, Ne.symm hca]
    obtain ⟨w1, hw1V, hw10, hw1⟩ := hV.2.2.2
    intro k
    have := kirrPs_le hE hV hw1V hw10 hw1 (mem_pi_submodule_iff.1 hu1 c) (by simpa using hc0) hwt k
    rw [hpa, partial_sum_of_basis_vector] at this
    split_ifs at this <;> linarith

  have hQ : ∃ m : ℕ, ∃ y ∈ Y, y ≠ 0 ∧ ∃ ν : Fin n → ℝ, IsKHWVec ε EN ν y ∧
      (∀ k, kirrPs k ν ≤ kirrPs k ν0) ∧ weightHeightFunctional (ν - lowK ε (lam - Pi.single s 1)) = m := by
    obtain ⟨N0, hN0⟩ := root_cone_height_natural (hcone ν0 _ hy0Y hy00 hν0)
    exact ⟨N0, _, hy0Y, hy00, ν0, hν0, fun k => le_rfl, hN0⟩
  obtain ⟨y, hyY, hy0, ν, hν, hνbd, hνht⟩ := Nat.find_spec hQ
  have hβ := hcone ν y hyY hy0 hν
  have hlowK' : lowK ε (lam - Pi.single s 1) = lowK ε lam - Pi.single s 1 := by
    ext a; simp only [lowK, Pi.add_apply, Pi.sub_apply]; ring
  set γ : Fin n → ℝ := ν - lowK ε lam with hγ
  have hγβ : γ = (ν - lowK ε (lam - Pi.single s 1)) - Pi.single s 1 := by
    rw [hlowK', hγ]; abel
  have hγps : ∀ k, kirrPs k γ = kirrPs k (ν - lowK ε (lam - Pi.single s 1)) - (if (s : ℕ) < k then 1 else 0) := by
    intro k; rw [hγβ, hps, partial_sum_of_basis_vector]
  have hSγ : ∀ k, -1 ≤ kirrPs k γ ∧ kirrPs k γ ≤ 0 := by
    intro k
    obtain ⟨Nk, hNk⟩ := root_cone_partial_sum_natural hβ k
    have hNk0 : (0 : ℝ) ≤ Nk := Nat.cast_nonneg _
    refine ⟨by rw [hγps, hNk]; split_ifs <;> linarith, ?_⟩
    rw [hγ, hps]
    linarith [hνbd k, hν0lo k]

  obtain ⟨T, hTY, hTfd, hTk, hyT⟩ := image_eigenspace_K_finite hE hVfd hVk hφ hyY
  obtain ⟨W, hWT, hWirr⟩ := exists_irreducible_highest_weight_submodule hKUN _ T rfl hTfd hTk y hyT hy0 hν
  have hWY : W ≤ Y := hWT.trans hTY

  set lam'' : Fin n → ℝ := ν + rhoC ε - rhoN ε with hlam''
  have hlowK'' : lowK ε lam'' = ν := by
    ext a; simp only [lowK, hlam'', Pi.add_apply, Pi.sub_apply]; ring
  have hlam''γ : ∀ a, lam'' a = lam a + γ a := by
    intro a; simp only [hlam'', hγ, lowK, Pi.add_apply, Pi.sub_apply]; ring
  have hγd : ∀ a b, |γ a - γ b| ≤ 2 := coordinate_difference_le_two γ hSγ
  have hmono'' : StrictAnti lam'' := by
    refine strictAnti_of_consecutive_lt fun a b hb => ?_
    have hab : a < b := Fin.lt_def.2 (by omega)
    by_cases he : ε a = ε b
    · obtain ⟨h1, h2⟩ := rho_consecutive_compact_pair ε a b hb he
      have := highest_weight_dominant_of_unitary hEN hKUN hν hy0 hab he
      simp only [hlam'', Pi.add_apply, Pi.sub_apply]
      linarith
    · have h1 := hgap.2.1 a b he
      have hlt := hmono hab
      rw [abs_of_pos (sub_pos.2 hlt)] at h1
      have h2 := abs_le.1 (hγd a b)
      rw [hlam''γ, hlam''γ]
      linarith
  have hgap'' : GapAtLeast ε lam'' (h - 2) := by
    intro a b he
    rw [hlam''γ, hlam''γ]
    have h1 := hgap.2.1 a b he
    have h2 := abs_sub_abs_le_abs_sub (lam a - lam b) (γ b - γ a)
    have h3 : |γ b - γ a| ≤ 2 := by rw [abs_sub_comm]; exact hγd a b
    have e : lam a - lam b - (γ b - γ a) = lam a + γ a - (lam b + γ b) := by ring
    rw [e] at h2
    linarith
  have hint'' : ∀ a, ∃ m : ℤ, lam'' a - ((n : ℝ) - 1) / 2 = (m : ℝ) := by
    intro a
    obtain ⟨m1, hm1⟩ := hint a
    obtain ⟨N1, hN1⟩ := root_cone_partial_sum_natural hβ ((a : ℕ) + 1)
    obtain ⟨N2, hN2⟩ := root_cone_partial_sum_natural hβ (a : ℕ)
    refine ⟨m1 + N1 - N2 - (if (s : ℕ) < (a : ℕ) + 1 then 1 else 0) + (if (s : ℕ) < (a : ℕ) then 1 else 0), ?_⟩
    rw [hlam''γ, coordinate_eq_partial_sum_difference γ a, hγps, hγps, hN1, hN2]
    split_ifs <;> push_cast <;> linarith
  have hbig : (n : ℝ) * (pOf ε : ℝ) * (qOf ε : ℝ) + 1 < h - 2 := by linarith
  have hW'' : IsKIrrHW ε EN (lowK ε lam'') W := by rw [hlowK'']; exact hWirr

  have hSch : ∀ w ∈ Wm ε EN W, phi EN 1 w = 0 := by
    intro w hw
    by_contra hne
    have := finiteDimensional_ncV (ε := ε) hWirr.1 1
    have hfdW : FiniteDimensional ℂ (Wm ε EN W) := Submodule.finiteDimensional_of_le Wm_le_ncV
    have hWst : IsKStableSub ε (bAct EN 1) (Wm ε EN W) := Wm_kStable hEN hUN hW''
    set T' : Submodule ℂ N := (Wm ε EN W).map (phi EN 1) with hT'
    have hT'st : IsKStableSub ε EN T' := by
      intro a b hab v hv
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
      rw [← phi_bAct hEN 1 hab z]
      exact Submodule.mem_map_of_mem (hWst a b hab z hz)
    have hT'ne : T' ≠ ⊥ := by
      intro hb
      have : phi EN 1 w ∈ T' := Submodule.mem_map_of_mem hw
      rw [hb, Submodule.mem_bot] at this
      exact hne this
    obtain ⟨y', hy'T, hy'0, μ', hy'μ⟩ := exists_khw hEN hKUN inferInstance hT'st hT'ne
    obtain ⟨w0', hw0', rfl⟩ := Submodule.mem_map.1 hy'T
    obtain ⟨x1, hx1, -, hkhw, hfx⟩ := lift_khw (A := bAct EN 1) (bAct_isKUnitary hUN 1) (phi EN 1)
      (fun a b hab z => phi_bAct hEN 1 hab z) hfdW hWst hw0' hy'μ
    have hx10 : x1 ≠ 0 := by rintro rfl; rw [map_zero] at hfx; exact hy'0 hfx.symm
    obtain ⟨a, b, hab, -, hμ'⟩ := Wm_khw hEN hUN hW'' hmono'' hgap'' hbig hx1 hx10 hkhw
    rw [hlowK''] at hμ'
    have hw0Y : phi EN 1 w0' ∈ Y := by
      rw [sch_phi_one_apply]
      refine Submodule.sum_mem _ fun p _ => hYst _ _ _ (hWY ?_)
      have hn := Wm_le_ncV hw0'
      unfold ncV at hn
      have h1 := (Submodule.mem_iInf _).1 hn (fun _ => p)
      rw [Submodule.mem_comap] at h1
      split_ifs at h1
      · exact h1
      · rw [Submodule.mem_bot] at h1
        rw [← sch_coord_apply, h1]
        exact zero_mem _
    have hcone' := hcone μ' _ hw0Y hy'0 hy'μ
    obtain ⟨N', hN'⟩ := root_cone_height_natural hcone'
    have hbd' : ∀ k, kirrPs k μ' ≤ kirrPs k ν0 := by
      intro k
      rw [hμ', hps, partial_sum_of_root]
      have := Fin.lt_def.1 hab
      have hνk := hνbd k
      by_cases h1 : (a : ℕ) < k <;> by_cases h2 : (b : ℕ) < k
      · simp only [h1, h2, if_true]; linarith
      · simp only [h1, h2, if_true, if_false]; linarith
      · omega
      · simp only [h1, h2, if_false]; linarith
    have hmin := Nat.find_min' hQ ⟨_, hw0Y, hy'0, μ', hy'μ, hbd', hN'⟩
    have e : μ' - lowK ε (lam - Pi.single s 1) = (ν - lowK ε (lam - Pi.single s 1)) - root a b := by
      rw [hμ']; abel
    rw [e, map_sub, hνht, k3vdHt_root] at hN'
    have hba : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.1 hab
    have hmin' : ((Nat.find hQ : ℕ) : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hmin
    linarith

  have hcasW : ∀ v ∈ W, casimir EN v = (casVal (lam - Pi.single s 1) : ℂ) • v :=
    fun v hv => hcasY v (hWY hv)
  have hSC := schmid_casimir n ε ν (h - 2) (casVal (lam - Pi.single s 1) : ℂ) N EN W hEN hUN hWirr hSch hcasW
    hint'' hmono'' hgap'' (by linarith) hp hq
  have hcv : casVal (lam - Pi.single s 1) = casVal lam'' := by exact_mod_cast hSC
  have hsum : (lam - Pi.single s 1) + (ν - lowK ε (lam - Pi.single s 1)) = lam'' := by
    ext a; simp only [hlam'', lowK, Pi.add_apply, Pi.sub_apply]; ring
  have hnsq : nsq ((lam - Pi.single s 1) + (ν - lowK ε (lam - Pi.single s 1))) = nsq (lam - Pi.single s 1) := by
    rw [hsum]; unfold casVal at hcv; linarith
  have hβ0 := cone_norm n (lam - Pi.single s 1) _ hmono'.antitone hβ hnsq
  have hνeq : ν = lowK ε (lam - Pi.single s 1) := sub_eq_zero.1 hβ0
  exact ⟨W, hWY, hνeq ▸ hWirr, hcasW⟩

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
end
end
