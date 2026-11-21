import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Gelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.GelfandHW

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def coordV (c : Fin n) : (Fin n → M) →ₗ[ℂ] M := LinearMap.proj c

def tensV (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) + if c = a then coordV b else 0

def tensVd (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => (E a b).comp (coordV c) - if c = b then coordV a else 0

def eeV (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun s => ∑ r, (E r s).comp (coordV r)

def eeVd (E : Fin n → Fin n → Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun r => -∑ s, (E r s).comp (coordV s)

def diagOp (A : Module.End ℂ M) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => A.comp (coordV c)

theorem tensV_coord (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensV E a b f c = E a b (f c) + if c = a then f b else 0 := by
  simp only [tensV, coordV, LinearMap.pi_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]

theorem tensVd_coord (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin n) (f : Fin n → M) (c : Fin n) :
    tensVd E a b f c = E a b (f c) - if c = b then f a else 0 := by
  simp only [tensVd, coordV, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  split_ifs <;> simp [LinearMap.proj_apply]

theorem eeV_coord (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (s : Fin n) :
    eeV E f s = ∑ r, E r s (f r) := by
  simp [eeV, coordV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem eeVd_coord (E : Fin n → Fin n → Module.End ℂ M) (f : Fin n → M) (r : Fin n) :
    eeVd E f r = -∑ s, E r s (f s) := by
  simp [eeVd, coordV, LinearMap.pi_apply, LinearMap.sum_apply]

theorem diagOp_coord (A : Module.End ℂ M) (f : Fin n → M) (c : Fin n) :
    diagOp (n := n) A f c = A (f c) := by
  simp [diagOp, coordV]

theorem isGlRep_apply_swap {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b c d : Fin n) (v : M) :
    E a b (E c d v) = E c d (E a b v) + ((if b = c then E a d v else 0) - (if d = a then E c b v else 0)) := by
  have h := LinearMap.congr_fun (hE a b c d) v
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add'] at h
  rw [h]; congr 1
  split_ifs <;> simp

theorem ite_end_coord (p : Prop) [Decidable p] (A : Module.End ℂ (Fin n → M)) (f : Fin n → M) (x : Fin n) :
    (if p then A else 0) f x = if p then A f x else 0 := by
  split_ifs <;> rfl

theorem tensV_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensV E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, tensV_coord, map_add,
    isGlRep_apply_swap hE a b c d, ite_end_coord]
  split_ifs <;> subst_vars <;>
    simp only [map_zero, add_zero, sub_zero, zero_sub, sub_self] <;> abel

theorem tensVd_isGlRep {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) : IsGlRep (tensVd E) := by
  intro a b c d
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [LinearMap.sub_apply, Pi.sub_apply, Module.End.mul_apply, tensVd_coord, map_sub,
    isGlRep_apply_swap hE a b c d, ite_end_coord]
  split_ifs <;> subst_vars <;>
    simp only [map_zero, add_zero, sub_zero, zero_sub, sub_self] <;> first | (exfalso; simp_all; done) | abel

theorem casimir_tensV {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensV E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeV E := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [casimir, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, diagOp_coord, eeV_coord, tensV_coord, map_add,
    Module.End.one_apply]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ g : Fin n → Fin n → M, (∑ i, ∑ j, if x = i then g i j else 0) = ∑ j, g x j := by
    intro g
    rw [Finset.sum_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  rw [key (fun i j => E j i (f j) + f i)]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul, two_smul]
  abel

theorem casimir_tensVd {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) :
    casimir (tensVd E) = diagOp (casimir E) + (n : ℂ) • 1 + (2 : ℂ) • eeVd E := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [casimir, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Pi.add_apply, Pi.smul_apply, diagOp_coord, eeVd_coord, tensVd_coord, map_sub,
    Module.End.one_apply]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have key : ∀ g : Fin n → Fin n → M, (∑ i, ∑ j, if x = i then g i j else 0) = ∑ j, g x j := by
    intro g
    rw [Finset.sum_eq_single x (fun i _ hi => by simp [Ne.symm hi]) (by simp)]
    simp
  rw [key (fun i j => E i j (f j))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul, two_smul]
  abel

theorem eeV_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensV E a b * eeV E = eeV E * tensV E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, tensV_coord, eeV_coord, map_sum, map_add, isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = a
  · subst h; simp only [if_true]; abel
  · simp only [h, if_false, Finset.sum_const_zero, sub_zero, add_zero]

theorem eeVd_comm {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) (a b : Fin n) :
    tensVd E a b * eeVd E = eeVd E * tensVd E a b := by
  refine LinearMap.ext fun f => funext fun x => ?_
  simp only [Module.End.mul_apply, tensVd_coord, eeVd_coord, map_sum, map_neg, map_sub, isGlRep_apply_swap hE a b]
  simp only [apply_ite (E _ _), map_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases h : x = b
  · subst h; simp only [if_true]; abel
  · have h' : ¬ b = x := fun e => h e.symm
    simp only [h, h', if_false, Finset.sum_const_zero, sub_zero, zero_sub]
    abel

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def antiE (E : Fin n → Fin n → Module.End ℂ M) : Fin n → Fin n → Module.End ℂ M :=
  fun a b => -E (Fin.rev b) (Fin.rev a)



end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def ptr (A : Module.End ℂ (Fin n → M)) : Module.End ℂ M :=
  ∑ c, (coordV c).comp (A.comp (LinearMap.single ℂ (fun _ : Fin n => M) c))

theorem ptr_apply (A : Module.End ℂ (Fin n → M)) (x : M) :
    ptr A x = ∑ c, A (Pi.single c x) c := by
  unfold ptr
  rw [LinearMap.sum_apply]
  rfl

theorem pow_single_of_mat (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) (c : Fin n) (x : M) :
    (A ^ k) (Pi.single c x) = fun s => ePow T k s c x := by
  induction k with
  | zero =>
    funext s
    simp only [pow_zero, ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, Module.End.one_apply]
    by_cases h : s = c
    · subst h; simp
    · simp [h]
  | succ k ih =>
    funext s
    rw [pow_succ', Module.End.mul_apply, ih, hA]
    simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply, LinearMap.sum_apply,
      Module.End.mul_apply]

theorem ePow_neg_equiv (F : Fin n → Fin n → Module.End ℂ M) (σ : Fin n ≃ Fin n) (k : ℕ) (a b : Fin n) :
    ePow (fun a b => -F (σ a) (σ b)) k a b = ((-1 : ℂ) ^ k) • ePow F k (σ a) (σ b) := by
  induction k generalizing a b with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply]
  | succ k ih =>
    have e1 : ∀ (G : Fin n → Fin n → Module.End ℂ M) (a b : Fin n),
        ePow G (k + 1) a b = ∑ r, ePow G k a r * G r b := by
      intro G a b
      simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ, Matrix.mul_apply, Matrix.of_apply]
    rw [e1, e1]
    simp_rw [ih]
    conv_rhs => rw [Finset.smul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [smul_mul_assoc, mul_neg, smul_neg, pow_succ, mul_neg_one, neg_smul, mul_one]

theorem ptr_eq_gelfand (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) : ptr (A ^ k) = gelfand T k := by
  ext x
  rw [ptr_apply]
  simp only [gelfand, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_single_of_mat A T hA k c x]

theorem ptr_eeV_pow (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) :
    ptr (eeV E ^ k) = ((-1 : ℂ) ^ k) • gelfand (antiE E) k := by
  have hA : ∀ f s, eeV E f s = ∑ r, (fun s r => E r s) s r (f r) := by
    intro f s
    simp [eeV, coordV]
  rw [ptr_eq_gelfand _ _ hA k]
  have key : ∀ a, ePow (antiE E) k a a =
      ((-1 : ℂ) ^ k) • ePow (fun s r => E r s) k (Fin.revPerm a) (Fin.revPerm a) := fun a =>
    ePow_neg_equiv (fun s r => E r s) Fin.revPerm k a a
  simp only [gelfand, key, Finset.smul_sum, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  exact (Equiv.sum_comp Fin.revPerm (fun a => ePow (fun s r => E r s) k a a)).symm

theorem ptr_eeVd_pow (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) :
    ptr (eeVd E ^ k) = ((-1 : ℂ) ^ k) • gelfand E k := by
  have hA : ∀ f r, eeVd E f r = ∑ s, (fun r s => -E r s) r s (f s) := by
    intro f r
    simp [eeVd, coordV]
  rw [ptr_eq_gelfand _ _ hA k]
  simp only [gelfand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact ePow_neg_equiv E (Equiv.refl _) k a a

end ReciprocityTheory.ChartRestriction.DS
end
end

section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def HasGelfandChar (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (S : Submodule ℂ M) : Prop :=
  ∀ k : ℕ, ∀ x ∈ S, gelfand E k x = gval (icShift μ) k • x ∧
    gelfand (antiE E) k x = gval (icShift (-μ)) k • x

def resSeries (a : Fin n → ℂ) : PowerSeries ℂ :=
  ∏ s, (1 + PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) - 1

def poleV (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)

def poleVd (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)

theorem rescale_neg_one_const (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) (PowerSeries.C c) = PowerSeries.C c := by
  ext m
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem rescale_neg_one_geometric_inv (c : ℂ) :
    PowerSeries.rescale (-1 : ℂ) ((1 - PowerSeries.C c * PowerSeries.X)⁻¹) =
      (1 + PowerSeries.C c * PowerSeries.X)⁻¹ := by
  have h1 : PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.C c * PowerSeries.X) =
      1 + PowerSeries.C c * PowerSeries.X := by
    simp [PowerSeries.rescale_X, rescale_neg_one_const]
  have hc0 : PowerSeries.constantCoeff (1 - PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  have hc1 : PowerSeries.constantCoeff (1 + PowerSeries.C c * PowerSeries.X) ≠ 0 := by simp
  rw [PowerSeries.eq_inv_iff_mul_eq_one hc1, ← h1, ← map_mul, PowerSeries.inv_mul_cancel _ hc0, map_one]

theorem residueSeries_neg (l : Fin n → ℂ) :
    resSeries (-l) = -PowerSeries.rescale (-1 : ℂ) (gelfandSeries l) := by
  have key : ∀ s, (1 + PowerSeries.X * (1 - PowerSeries.C ((-l) s) * PowerSeries.X)⁻¹) =
      PowerSeries.rescale (-1 : ℂ) (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
    intro s
    rw [map_sub, map_one, map_mul, PowerSeries.rescale_X, rescale_neg_one_geometric_inv]
    simp only [Pi.neg_apply, map_neg, map_one, neg_mul, one_mul, sub_neg_eq_add]
  unfold resSeries gelfandSeries
  simp_rw [key]
  rw [← map_prod, map_sub, map_one]
  ring

theorem coeff_residueSeries_neg (l : Fin n → ℂ) (k : ℕ) :
    PowerSeries.coeff (k + 1) (resSeries (-l)) = (-1 : ℂ) ^ k * gval l k := by
  rw [residueSeries_neg, map_neg, PowerSeries.coeff_rescale]
  unfold gval
  ring

theorem pole_eq_neg_shift (μ : Fin n → ℝ) : poleV μ = -icShift (-μ) := by
  funext s
  simp only [poleV, icShift, Pi.neg_apply]
  push_cast
  ring

theorem dualPole_eq_neg_shift (μ : Fin n → ℝ) : poleVd μ = -icShift μ := by
  funext s
  simp only [poleVd, icShift, Pi.neg_apply]
  push_cast
  ring



theorem ptr_eeV_pow_char {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : HasGelfandChar E μ S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeV E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleV μ)) • x := by
  rw [ptr_eeV_pow, LinearMap.smul_apply, (hS k x hx).2, smul_smul, pole_eq_neg_shift, coeff_residueSeries_neg]

theorem ptr_eeVd_pow_char {E : Fin n → Fin n → Module.End ℂ M} {μ : Fin n → ℝ} {S : Submodule ℂ M}
    (hS : HasGelfandChar E μ S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeVd E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleVd μ)) • x := by
  rw [ptr_eeVd_pow, LinearMap.smul_apply, (hS k x hx).1, smul_smul, dualPole_eq_neg_shift, coeff_residueSeries_neg]

end ReciprocityTheory.ChartRestriction.DS
end
end
