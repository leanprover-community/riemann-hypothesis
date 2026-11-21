import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightModuleUnitaryForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryTAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationStepFromSectionKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirSectionSumIdentity

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem orthogonal_kstable_compl : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B →
    ∀ U : Submodule ℂ W, KStable actW U → KStable actW (U.orthogonalBilin B) ∧ U ⊔ U.orthogonalBilin B = ⊤ := by
  intro R S W _ _ _ actW B hB U hU
  obtain ⟨_, hpos, hadj⟩ := hB
  constructor
  · intro X hX x hx
    refine GlobalTheory.TensorHW.kc_ind actW (U.orthogonalBilin B) x (fun a b hab => ?_) hX
    rw [Submodule.mem_orthogonalBilin_iff] at hx ⊢
    intro n hn
    have hba : sameBlock b a := by
      cases a <;> cases b <;> simp_all [sameBlock]
    have h := hadj b a hba n x
    show B n (actW (Eab a b) x) = 0
    rw [← h]
    exact hx _ (hU _ (GlobalTheory.TensorHW.isKC_Eab hba) n hn)
  · have hinf : U ⊓ U.orthogonalBilin B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxo⟩ := Submodule.mem_inf.mp hx
      rw [Submodule.mem_orthogonalBilin_iff] at hxo
      have h0 : B x x = 0 := hxo x hxU
      rw [Submodule.mem_bot]
      by_contra hne
      have h := hpos x hne
      rw [h0] at h
      simp at h
    let b := Module.finBasis ℂ U
    let ψ : W →ₗ[ℂ] (Fin (Module.finrank ℂ U) → ℂ) := LinearMap.pi (fun i => B (b i : W))
    have hker : LinearMap.ker ψ ≤ U.orthogonalBilin B := by
      intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_orthogonalBilin_iff]
      intro n hn
      have hf : (B.flip x).comp U.subtype = 0 := by
        refine b.ext (fun i => ?_)
        have h := congrFun hx i
        simpa [ψ] using h
      have h := LinearMap.congr_fun hf ⟨n, hn⟩
      simpa using h
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have h2 : Module.finrank ℂ (LinearMap.range ψ) ≤ Module.finrank ℂ U := by
      have h := Submodule.finrank_le (LinearMap.range ψ)
      simpa using h
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (U.orthogonalBilin B)
    rw [hinf, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    omega

end GlobalTheory.SteepMult
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_form_orthogonal_complement : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B →
    ∀ U : Submodule ℂ W, KStable actW U → KStable actW (U.orthogonalBilin B) ∧ U ⊔ U.orthogonalBilin B = ⊤ := by
  atlas_forward_decl GlobalTheory.SteepMult.orthogonal_kstable_compl
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.TLie

variable {R S : ℕ}

lemma adCoeff_eq (Z : Mat R S) (y x : NC R S) :
    adP Z y x = (Z * eNC x - eNC x * Z) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  obtain ⟨⟨c, d⟩, h'⟩ := x
  simp only [adP, eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
  congr 1
  · rw [Finset.sum_eq_single c]
    · by_cases hbd : b = d
      · simp [hbd]
      · simp [hbd, Ne.symm hbd]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · rw [Finset.sum_eq_single d]
    · by_cases hac : a = c
      · simp [hac]
      · simp [hac, Ne.symm hac]
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

lemma same_trans {a b c : Ix R S} (h1 : sameBlock a b) (h2 : sameBlock b c) : sameBlock a c := by
  cases a <;> cases b <;> cases c <;> first | trivial | exact h1.elim | exact h2.elim

lemma sum_NC (f : Ix R S × Ix R S → ℂ) (hf : ∀ p, sameBlock p.1 p.2 → f p = 0) :
    ∑ x : NC R S, f x.1 = ∑ p, f p := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Ix R S × Ix R S => ¬ sameBlock p.1 p.2)
    (fun p => by rw [Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)) f]
  exact Finset.sum_filter_of_ne fun p _ hp hs => hp (hf p hs)

lemma sum_all {ι : Type} [Fintype ι] [DecidableEq ι] (Y M : Matrix ι ι ℂ) (a b : ι) :
    ∑ p : ι × ι, (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2 =
      (Y * M - M * Y) a b := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul, Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.mul_apply]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    simp [mul_comm]

lemma sum_adP {Y : Mat R S} (hY : IsKC Y) (M : Mat R S) (y : NC R S) :
    ∑ x : NC R S, adP Y y x * M x.1.1 x.1.2 = (Y * M - M * Y) y.1.1 y.1.2 := by
  obtain ⟨⟨a, b⟩, h⟩ := y
  refine Eq.trans ?_ (sum_all Y M a b)
  refine sum_NC (fun p =>
    (Y a p.1 * (if b = p.2 then 1 else 0) - (if a = p.1 then 1 else 0) * Y p.2 b) * M p.1 p.2) ?_
  rintro ⟨c, d⟩ hs
  have e1 : Y a c * (if b = d then 1 else 0) = 0 := by
    split_ifs with hbd
    · subst hbd
      rw [hY a c (fun hac => h (same_trans hac hs)), zero_mul]
    · exact mul_zero _
  have e2 : (if a = c then 1 else 0) * Y d b = 0 := by
    split_ifs with hac
    · subst hac
      rw [hY d b (fun hdb => h (same_trans hs hdb)), mul_zero]
    · exact zero_mul _
  simp only [e1, e2, sub_zero, zero_mul]

lemma adCoeff_commutator {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) (y w : NC R S) :
    adP (Y * Z - Z * Y) y w = ∑ x, adP Y y x * adP Z x w - ∑ x, adP Z y x * adP Y x w := by
  have h1 := sum_adP hY (Z * eNC w - eNC w * Z) y
  have h2 := sum_adP hZ (Y * eNC w - eNC w * Y) y
  simp only [← adCoeff_eq] at h1 h2
  rw [h1, h2, adCoeff_eq, ← Matrix.sub_apply]
  refine congrFun (congrFun ?_ _) _
  simp only [mul_sub, sub_mul, mul_assoc]
  abel

variable {W : Type} [AddCommGroup W] [Module ℂ W]

lemma factorOp_apply (k : ℕ) (i : Fin k) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    factorOp k i Z Ψ g = ∑ x, adP Z (g i) x • Ψ (Function.update g i x) := rfl

lemma factorOp_commutator (k : ℕ) (i : Fin k) {Y Z : Mat R S} (hY : IsKC Y) (hZ : IsKC Z) :
    (factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k i Y * factorOp k i Z - factorOp k i Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Pi.sub_apply, factorOp_apply,
    Function.update_self, Function.update_idem, adCoeff_commutator hY hZ, sub_smul, Finset.sum_sub_distrib,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  congr 1 <;> exact Finset.sum_comm

lemma factorOp_comm_of_ne (k : ℕ) {i j : Fin k} (hij : i ≠ j) (Y Z : Mat R S) :
    (factorOp k i Y * factorOp k j Z : Module.End ℂ ((Fin k → NC R S) → W)) =
      factorOp k j Z * factorOp k i Y := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp only [Module.End.mul_apply, factorOp_apply, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [smul_comm, Function.update_comm hij]

def ptOp (k : ℕ) (A : Module.End ℂ W) : Module.End ℂ ((Fin k → NC R S) → W) :=
  LinearMap.pi (fun g => A ∘ₗ LinearMap.proj g)

lemma ptOp_comm_factorOp (k : ℕ) (i : Fin k) (A : Module.End ℂ W) (Z : Mat R S) :
    (ptOp k A * factorOp k i Z : Module.End ℂ ((Fin k → NC R S) → W)) = factorOp k i Z * ptOp k A := by
  refine LinearMap.ext fun Ψ => funext fun g => ?_
  simp [ptOp, factorOp_apply]

lemma tAct_eq (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) :
    tAct k actW Z = ptOp k (actW Z) + ∑ i, factorOp k i Z := rfl

theorem isKLieAct_tAct (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (h : IsKLieAct actW) : IsKLieAct (tAct k actW) := by
  intro Y Z hY hZ
  have hp : (ptOp k (actW (Y * Z - Z * Y)) : Module.End ℂ ((Fin k → NC R S) → W)) =
      ptOp k (actW Y) * ptOp k (actW Z) - ptOp k (actW Z) * ptOp k (actW Y) := by
    rw [h Y Z hY hZ]
    refine LinearMap.ext fun Ψ => funext fun g => ?_
    simp [ptOp]
  have hs : (∑ i, factorOp k i (Y * Z - Z * Y) : Module.End ℂ ((Fin k → NC R S) → W)) =
      (∑ i, factorOp k i Y) * (∑ i, factorOp k i Z) - (∑ i, factorOp k i Z) * (∑ i, factorOp k i Y) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum,
      Finset.sum_comm (f := fun i j => (factorOp k i Z * factorOp k j Y :
        Module.End ℂ ((Fin k → NC R S) → W))), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i, factorOp_commutator k i hY hZ]
    · intro j _ hj
      rw [factorOp_comm_of_ne k hj.symm, sub_self]
    · simp
  have hc : ∀ (A : Module.End ℂ W) (X : Mat R S),
      (ptOp k A * (∑ i, factorOp k i X) : Module.End ℂ ((Fin k → NC R S) → W)) =
        (∑ i, factorOp k i X) * ptOp k A := by
    intro A X
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => ptOp_comm_factorOp k i A X
  rw [tAct_eq, tAct_eq, tAct_eq, hp, hs]
  simp only [add_mul, mul_add, hc]
  abel

end GlobalTheory.SteepMult.TLie
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_action_is_lie_action : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W),
    IsKLieAct actW → IsKLieAct (tAct k actW) := by
  atlas_forward_decl GlobalTheory.SteepMult.TLie.isKLieAct_tAct
end

section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B → IsUnitary (tAct k actW) (formT k B) := by
  first | exact @GlobalTheory.SteepMult.isUnitary_tAct | exact GlobalTheory.SteepMult.isUnitary_tAct | (intros; apply GlobalTheory.SteepMult.isUnitary_tAct <;> assumption)
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

lemma adP_Eab_self {R S : ℕ} (c : Ix R S) (y x : NC R S) :
    adP (Eab c c) y x = if x = y then ((if y.1.1 = c then 1 else 0) - (if y.1.2 = c then 1 else 0) : ℂ) else 0 := by
  obtain ⟨⟨a, b⟩, h⟩ := x
  obtain ⟨⟨a', b'⟩, h'⟩ := y
  simp only [adP, Eab, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> by_cases h3 : c = a' <;> by_cases h4 : c = b' <;>
    simp_all [eq_comm] <;> grind

lemma tAct_Eab_self_apply {R S k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (c : Ix R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    tAct k actW (Eab c c) Ψ g = actW (Eab c c) (Ψ g) +
      (∑ i, ((if (g i).1.1 = c then 1 else 0) - (if (g i).1.2 = c then 1 else 0) : ℂ)) • Ψ g := by
  rw [tAct_apply, Finset.sum_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single (g i)]
  · simp [adP_Eab_self]
  · intro x _ hx
    simp [adP_Eab_self, hx]
  · simp

lemma single_mem_wtSub {R S k : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W)
    (g : Fin k → NC R S) (μ : Ix R S → ℚ) (w : W) (hw : w ∈ wtSub actW μ) :
    (Pi.single g w : (Fin k → NC R S) → W) ∈ wtSub (tAct k actW)
      (fun c => μ c + ∑ i, ((if (g i).1.1 = c then 1 else 0) - (if (g i).1.2 = c then 1 else 0))) := by
  rw [GlobalTheory.TensorHW.mem_wt] at hw ⊢
  intro c
  funext h
  rw [tAct_Eab_self_apply]
  by_cases hh : h = g
  · subst hh
    simp only [Pi.single_eq_same, Pi.smul_apply, hw c, ← add_smul]
    congr 1
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  · simp [hh]

theorem tAct_mem_iSup_wtSub (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (hW : ∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ)
    (Ψ : (Fin k → NC R S) → W) : Ψ ∈ ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ := by
  rw [← Finset.univ_sum_single Ψ]
  refine Submodule.sum_mem _ fun g _ => ?_
  refine Submodule.iSup_induction (motive := fun w => (Pi.single g w : (Fin k → NC R S) → W) ∈
    ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ) _ (hW (Ψ g)) ?_ ?_ ?_
  · intro μ w hw
    exact Submodule.mem_iSup_of_mem _ (single_mem_wtSub actW g μ w hw)
  · simp
  · intro x y hx hy
    rw [Pi.single_add]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.SteepMult
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_action_weight_decomposition : ∀ (R S k : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (actW : Mat R S →ₗ[ℂ] Module.End ℂ W),
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) →
    ∀ Ψ : (Fin k → NC R S) → W, Ψ ∈ ⨆ μ : Ix R S → ℚ, wtSub (tAct k actW) μ := by
  atlas_forward_decl GlobalTheory.SteepMult.tAct_mem_iSup_wtSub
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.Equivariance

lemma mul_prod_ofFn {A ι : Type} [Ring A] [Algebra ℂ A] [Fintype ι] (X : ι → A) (z : A) (c : ι → ι → ℂ)
    (h : ∀ x, z * X x = X x * z + ∑ y, c y x • X y) (k : ℕ) (g : Fin k → ι) :
    z * (List.ofFn fun i => X (g i)).prod = (List.ofFn fun i => X (g i)).prod * z +
      ∑ i, ∑ y, c y (g i) • (List.ofFn fun j => X (Function.update g i y j)).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ (i : Fin k) (y : ι) (j : Fin k), Function.update g i.succ y j.succ =
        Function.update (fun j : Fin k => g j.succ) i y j := by
      intro i y j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, Function.update_of_ne (fun h' => hj (Fin.succ_injective _ h'))]
    have e0 : ∀ (y : ι) (j : Fin k), Function.update g 0 y j.succ = g j.succ := fun y j =>
      Function.update_of_ne (Fin.succ_ne_zero j) _ _
    have e1 : ∀ (i : Fin k) (y : ι), Function.update g i.succ y 0 = g 0 := fun i y =>
      Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
    rw [Fin.sum_univ_succ]
    simp only [List.ofFn_succ, List.prod_cons, e, e0, e1, Function.update_self]
    rw [← mul_assoc, h, add_mul, mul_assoc, ih (fun j => g j.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

variable {R S : ℕ}

lemma bracket_eNC {Z : Mat R S} (hZ : IsKC Z) (x : NC R S) :
    Z * eNC x - eNC x * Z = ∑ y, adP Z y x • eNC y := by
  obtain ⟨⟨a, b⟩, hab⟩ := x
  ext c d
  have hab' : ¬ sameBlock a b := hab
  have hl : (Z * eNC ⟨(a, b), hab⟩ - eNC ⟨(a, b), hab⟩ * Z) c d =
      Z c a * (if d = b then 1 else 0) - (if c = a then 1 else 0) * Z b d := by
    simp only [eNC, Eab, Matrix.sub_apply, Matrix.mul_apply, Matrix.single_apply]
    congr 1
    · by_cases h : d = b
      · subst h; simp
      · simp [h, Ne.symm h]
    · by_cases h : c = a
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [hl, Matrix.sum_apply]
  by_cases hcd : sameBlock c d
  · rw [Finset.sum_eq_zero]
    · have h1 : Z c a * (if d = b then 1 else 0) = 0 := by
        by_cases h : d = b
        · subst h
          rw [hZ c a, zero_mul]
          clear hl hab
          rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
        · simp [h]
      have h2 : (if c = a then 1 else 0) * Z b d = 0 := by
        by_cases h : c = a
        · subst h
          rw [hZ b d, mul_zero]
          clear h1 hl hab
          rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;> simp_all [sameBlock]
        · simp [h]
      rw [h1, h2, sub_zero]
    · rintro ⟨⟨u, v⟩, huv⟩ _
      have : ¬ (u = c ∧ v = d) := by
        rintro ⟨rfl, rfl⟩
        exact huv hcd
      simp [eNC, Eab, Matrix.single_apply, this]
  · rw [Finset.sum_eq_single (⟨(c, d), hcd⟩ : NC R S)]
    · simp [eNC, Eab, adP]
    · rintro ⟨⟨u, v⟩, huv⟩ _ hne
      have : ¬ (u = c ∧ v = d) := by
        rintro ⟨rfl, rfl⟩
        exact hne rfl
      simp [eNC, Eab, Matrix.single_apply, this]
    · simp

lemma sum_update_swap {ι B : Type} [Fintype ι] [DecidableEq ι] [AddCommMonoid B] {k : ℕ} (i : Fin k)
    (F : (Fin k → ι) → (Fin k → ι) → ι → ι → B) :
    ∑ g, ∑ x, F g (Function.update g i x) (g i) x = ∑ g, ∑ y, F (Function.update g i y) g y (g i) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  refine Finset.sum_nbij' (fun p => (Function.update p.1 i p.2, p.1 i))
    (fun p => (Function.update p.1 i p.2, p.1 i)) ?_ ?_ ?_ ?_ ?_ <;> simp

theorem phiN_tAct : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V) (hN : KStable M.act N) (k : ℕ) (Z : Mat R S),
    IsKC Z → ∀ Ψ : (Fin k → NC R S) → N,
      phiN M.act N k (tAct k (restrAct M.act N hN) Z Ψ) = M.act Z (phiN M.act N k Ψ) := by
  intro R S M N hN k Z hZ Ψ
  have h : ∀ x : NC R S, M.act Z * M.act (eNC x) =
      M.act (eNC x) * M.act Z + ∑ y, adP Z y x • M.act (eNC y) := by
    intro x
    have h1 := M.lie Z (eNC x)
    rw [bracket_eNC hZ, map_sum] at h1
    simp only [map_smul] at h1
    rw [h1]; abel
  have hw : ∀ (g : Fin k → NC R S) (v : M.V), M.act Z (word M.act g v) = word M.act g (M.act Z v) +
      ∑ i, ∑ y, adP Z y (g i) • word M.act (Function.update g i y) v := by
    intro g v
    have := congrArg (fun T : Module.End ℂ M.V => T v)
      (mul_prod_ofFn (fun x => M.act (eNC x)) (M.act Z) (adP Z) h k g)
    simpa [word, LinearMap.sum_apply] using this
  simp only [phiN_apply, tAct_apply, map_sum, hw, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    restrAct_apply, kpart_of_isKC hZ, map_add, map_smul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact sum_update_swap i (fun g g' y x => adP Z y x • word M.act g (Ψ g' : M.V))

end GlobalTheory.SteepMult.Equivariance
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_map_equivariant : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V) (hN : KStable M.act N) (k : ℕ) (Z : Mat R S),
    IsKC Z → ∀ Ψ : (Fin k → NC R S) → N,
      phiN M.act N k (tAct k (restrAct M.act N hN) Z Ψ) = M.act Z (phiN M.act N k Ψ) := by
  atlas_forward_decl GlobalTheory.SteepMult.Equivariance.phiN_tAct
end

section
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepSpan

variable {R S : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

lemma word_zero (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (g : Fin 0 → NC R S) : word act g = 1 := by
  simp [word]

lemma word_succ (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (g : Fin (k + 1) → NC R S) :
    word act g = act (eNC (g 0)) * word act (fun i : Fin k => g i.succ) := by
  simp [word, List.ofFn_succ]

def wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {y | ∃ (k : ℕ) (g : Fin k → NC R S) (n : V), n ∈ N ∧ y = word act g n}

lemma word_mem_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ wordSpan act N :=
  Submodule.subset_span ⟨k, g, n, hn, rfl⟩

lemma le_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {n : V} (hn : n ∈ N) :
    n ∈ wordSpan act N := by
  simpa [word_zero] using word_mem_wordSpan act N (k := 0) Fin.elim0 hn

lemma nc_mem_wordSpan (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (x : NC R S) {y : V}
    (hy : y ∈ wordSpan act N) : act (eNC x) y ∈ wordSpan act N := by
  have : wordSpan act N ≤ (wordSpan act N).comap (act (eNC x)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, g, n, hn, rfl⟩
    have h := word_mem_wordSpan act N (k := k + 1) (Fin.cons x g) hn
    rw [word_succ] at h
    simpa using h
  exact this hy

lemma act_base (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) (Z : Mat R S)
    {n : V} (hn : n ∈ N) : act Z n ∈ wordSpan act N := by
  have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp [Eab, Matrix.smul_single]
  rw [hZ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ ?_
  by_cases h : sameBlock a b
  · exact le_wordSpan act N (hN _ (GlobalTheory.TensorHW.isKC_Eab h) _ hn)
  · exact nc_mem_wordSpan act N ⟨(a, b), h⟩ (le_wordSpan act N hn)

lemma act_word (act : Mat R S →ₗ[ℂ] Module.End ℂ V)
    (hL : ∀ Y Z : Mat R S, act (Y * Z - Z * Y) = act Y * act Z - act Z * act Y)
    (N : Submodule ℂ V) (hN : KStable act N) {n : V} (hn : n ∈ N) (k : ℕ) :
    ∀ (g : Fin k → NC R S) (Z : Mat R S), act Z (word act g n) ∈ wordSpan act N := by
  induction k with
  | zero =>
    intro g Z
    rw [word_zero]
    exact act_base act N hN Z hn
  | succ k ih =>
    intro g Z
    rw [word_succ, Module.End.mul_apply]
    have h := ih (fun i => g i.succ) (Z * eNC (g 0) - eNC (g 0) * Z)
    rw [hL, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply] at h
    simpa using add_mem h (nc_mem_wordSpan act N (g 0) (ih (fun i => g i.succ) Z))

lemma filt_mono (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k l : ℕ} (h : k ≤ l) :
    filt act N k ≤ filt act N l :=
  iSup_le fun j => le_iSup (fun j : Fin (l + 1) => LinearMap.range (phiN act N j)) ⟨j, by omega⟩

lemma word_mem_filt (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ filt act N k := by
  classical
  refine le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN act N j)) (Fin.last k) ?_
  refine ⟨(Pi.single g ⟨n, hn⟩ : (Fin k → NC R S) → N), ?_⟩
  change phiN act N k _ = _
  rw [phiN_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hne
    simp [Pi.single_eq_of_ne hne]
  · simp

theorem filt_exhaustive : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    genSub M.act {v} = ⊤ → ∀ w, ∃ k, w ∈ filt M.act (GlobalTheory.BlockReps.gen M.act v) k := by
  intro R S M Λ v _ hgen w
  have hle : genSub M.act {v} ≤ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) := by
    refine sInf_le ⟨Set.singleton_subset_iff.2 (le_wordSpan _ _ (GlobalTheory.BlockReps.mem_gen v)), fun Z => ?_⟩
    have : wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) ≤
        (wordSpan M.act (GlobalTheory.BlockReps.gen M.act v)).comap (M.act Z) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, g, n, hn, rfl⟩
      exact act_word M.act M.lie _ (GlobalTheory.BlockReps.stable_gen v) hn k g Z
    exact fun y hy => this hy
  have hw : w ∈ wordSpan M.act (GlobalTheory.BlockReps.gen M.act v) := hle (hgen ▸ Submodule.mem_top)
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, g, n, hn, rfl⟩ := hy
    exact ⟨k, word_mem_filt _ _ g hn⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    exact ⟨max k l, add_mem (filt_mono _ _ (le_max_left _ _) hk) (filt_mono _ _ (le_max_right _ _) hl)⟩
  | smul c x _ hx =>
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, Submodule.smul_mem _ _ hk⟩

end GlobalTheory.SteepSpan

end
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_module_filtration_exhaustive : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v → genSub M.act {v} = ⊤ →
    ∀ w, ∃ k, w ∈ filt M.act (GlobalTheory.BlockReps.gen M.act v) k := by
  atlas_forward_decl GlobalTheory.SteepSpan.filt_exhaustive
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem hw_lift_orth : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (φ : W →ₗ[ℂ] V) (F : Submodule ℂ V) (Λ : Ix R S → ℚ) (w : V),
    IsUnitary actW B → KStable act F → (∀ Z, IsKC Z → ∀ x, φ (actW Z x) = act Z (φ x)) →
    w ∈ LinearMap.range φ ⊔ F → w ∈ hwSub act Λ → w ∉ F →
    ∃ Ψ ∈ (F.comap φ).orthogonalBilin B, Ψ ≠ 0 ∧ Ψ ∈ hwSub actW Λ := by
  intro R S W _ _ _ actW B V _ _ act φ F Λ w hU hF hφ hw hhw hwF
  obtain ⟨_hherm, hpos, hadj⟩ := hU
  set K := F.comap φ with hK
  have hKst : ∀ Z, IsKC Z → ∀ x ∈ K, actW Z x ∈ K := by
    intro Z hZ x hx
    simp only [hK, Submodule.mem_comap] at hx ⊢
    rw [hφ Z hZ]; exact hF Z hZ _ hx
  have hperp : ∀ y, y ∈ K.orthogonalBilin B ↔ ∀ v ∈ K, B v y = 0 := fun y => Iff.rfl
  have hsame_symm : ∀ a b : Ix R S, sameBlock a b → sameBlock b a := by
    intro a b; cases a <;> cases b <;> simp [sameBlock]
  have hsame_refl : ∀ a : Ix R S, sameBlock a a := by
    intro a; cases a <;> simp [sameBlock]
  have hpos_same : ∀ a b : Ix R S, posC a b → sameBlock a b := by
    intro a b; cases a <;> cases b <;> simp [posC, sameBlock]
  have hKC_E : ∀ a b : Ix R S, sameBlock a b → IsKC (Eab a b) := by
    intro a b hab c d hcd
    simp only [Eab, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; exact absurd hab hcd
    · rfl
  have hperpE : ∀ a b, sameBlock a b → ∀ y ∈ K.orthogonalBilin B, actW (Eab a b) y ∈ K.orthogonalBilin B := by
    intro a b hab y hy
    rw [hperp] at hy ⊢
    intro v hv
    rw [← hadj b a (hsame_symm a b hab) v y]
    exact hy _ (hKst _ (hKC_E b a (hsame_symm a b hab)) v hv)
  have hdisj : ∀ y ∈ K, y ∈ K.orthogonalBilin B → y = 0 := by
    intro y h1 h2
    by_contra hne
    have := hpos y hne
    rw [(hperp y).1 h2 y h1] at this; simp at this
  have hdec : ∀ x, ∃ κ ∈ K, x - κ ∈ K.orthogonalBilin B := by
    intro x
    let b := Module.finBasis ℂ K
    let G : W →ₗ[ℂ] (Fin (Module.finrank ℂ K) → ℂ) := LinearMap.pi fun i => B (b i : W)
    have key : ∀ y, G y = 0 → ∀ v ∈ K, B v y = 0 := by
      intro y hy v hv
      have h1 : (B.flip y) ∘ₛₗ K.subtype = 0 := b.ext fun i => by simpa [G] using congrFun hy i
      simpa using LinearMap.congr_fun h1 ⟨v, hv⟩
    have hinj : Function.Injective (G ∘ₗ K.subtype) := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      exact Subtype.ext (hdisj z z.2 ((hperp z).2 (key z hz)))
    have hsurj : Function.Surjective (G ∘ₗ K.subtype) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
    obtain ⟨z, hz⟩ := hsurj (G x)
    refine ⟨z, z.2, (hperp _).2 (key _ ?_)⟩
    rw [map_sub, ← hz]; simp
  obtain ⟨y, hy, f, hf, rfl⟩ := Submodule.mem_sup.1 hw
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨κ, hκ, hΨ⟩ := hdec x
  have hκF : φ κ ∈ F := hκ
  have hfκ : f + φ κ ∈ F := F.add_mem hf hκF
  have hφΨ : φ (x - κ) = (φ x + f) - (f + φ κ) := by rw [map_sub]; abel
  have gen : ∀ (Z : Mat R S) (c : ℂ), IsKC Z → act Z (φ x + f) = c • (φ x + f) →
      actW Z (x - κ) - c • (x - κ) ∈ K.orthogonalBilin B → actW Z (x - κ) - c • (x - κ) = 0 := by
    intro Z c hZ hw' hperpZ
    refine hdisj _ ?_ hperpZ
    show φ (actW Z (x - κ) - c • (x - κ)) ∈ F
    rw [map_sub, map_smul, hφ Z hZ, hφΨ, map_sub, hw', smul_sub]
    have : c • (φ x + f) - act Z (f + φ κ) - (c • (φ x + f) - c • (f + φ κ))
        = c • (f + φ κ) - act Z (f + φ κ) := by abel
    rw [this]
    exact F.sub_mem (F.smul_mem _ hfκ) (hF Z hZ _ hfκ)
  refine ⟨x - κ, hΨ, ?_, ?_⟩
  · intro h0
    apply hwF
    rw [sub_eq_zero.1 h0]; exact F.add_mem hκF hf
  · simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hhw ⊢
    obtain ⟨hwt, hkill⟩ := hhw
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · have e := gen (Eab a a) ((Λ a : ℚ) : ℂ) (hKC_E a a (hsame_refl a)) (hwt a)
        (Submodule.sub_mem _ (hperpE a a (hsame_refl a) _ hΨ) (Submodule.smul_mem _ _ hΨ))
      exact sub_eq_zero.1 e
    · have e := gen (Eab a b) 0 (hKC_E a b (hpos_same a b hab)) (by rw [hkill a b hab, zero_smul])
        (Submodule.sub_mem _ (hperpE a b (hpos_same a b hab) _ hΨ) (Submodule.smul_mem _ _ hΨ))
      simpa using e

end GlobalTheory.SteepMult
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_highestWeight_orthogonal_comap_of_mem_range_sup : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (φ : W →ₗ[ℂ] V) (F : Submodule ℂ V) (Λ : Ix R S → ℚ) (w : V),
    IsUnitary actW B → KStable act F → (∀ Z, IsKC Z → ∀ x, φ (actW Z x) = act Z (φ x)) →
    w ∈ LinearMap.range φ ⊔ F → w ∈ hwSub act Λ → w ∉ F →
    ∃ Ψ ∈ (F.comap φ).orthogonalBilin B, Ψ ≠ 0 ∧ Ψ ∈ hwSub actW Λ := by
  atlas_forward_decl GlobalTheory.SteepMult.hw_lift_orth
end

section
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem section1_mem_orthogonal_ker : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N →
    ∀ (B : N →ₗ⋆[ℂ] N →ₗ[ℂ] ℂ) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N),
    Ψ ∈ ((filt M.act N k).comap (phiN M.act N (k + 1))).orthogonalBilin (formT (k + 1) B) →
    ∀ i g, section1 Ψ i g ∈ (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) := by
  intro R S M N hN B k Ψ hΨ i g
  classical
  rw [Submodule.mem_orthogonalBilin_iff]
  intro x hx
  let Φ : (Fin (k + 1) → NC R S) → N := fun g' =>
    if ∀ j, j ≠ i → g' j = g j then x (fun _ => g' i) else 0
  have hΦ : Φ ∈ (filt M.act N k).comap (phiN M.act N (k + 1)) := by
    rw [Submodule.mem_comap]
    apply GlobalTheory.T.filtration_step_from_section_kernel R S M N hN k i Φ
    intro g''
    by_cases h : ∀ j, j ≠ i → g'' j = g j
    · have e : section1 Φ i g'' = x := by
        funext h'
        simp only [section1, Φ]
        rw [if_pos (fun j hj => by rw [Function.update_of_ne hj]; exact h j hj)]
        simp only [Function.update_self]
        congr 1
        funext j
        rw [Subsingleton.elim j 0]
      rw [e]
      exact hx
    · have e : section1 Φ i g'' = 0 := by
        funext h'
        simp only [section1, Φ]
        rw [if_neg]
        · rfl
        · intro hc
          apply h
          intro j hj
          have := hc j hj
          rwa [Function.update_of_ne hj] at this
      rw [e, map_zero]
  have h0 : formT (k + 1) B Φ Ψ = 0 := (Submodule.mem_orthogonalBilin_iff.1 hΨ) Φ hΦ
  have key : formT (k + 1) B Φ Ψ = ∑ y, B (x (fun _ => y)) (Ψ (Function.update g i y)) := by
    rw [formT_apply, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Function.update g i)))]
    · rw [Finset.sum_image (fun a _ b _ hab => Function.update_injective g i hab)]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [Φ]
      rw [if_pos (fun j hj => Function.update_of_ne hj _ _)]
      simp only [Function.update_self]
    · intro g' _ hg'
      simp only [Φ]
      rw [if_neg, map_zero, LinearMap.zero_apply]
      intro hc
      apply hg'
      rw [Finset.mem_image]
      refine ⟨g' i, Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj, hc j hj]
  show formT 1 B x (section1 Ψ i g) = 0
  rw [key] at h0
  rw [formT_apply]
  refine (Fintype.sum_equiv (Equiv.funUnique (Fin 1) (NC R S)) _ _ fun h => ?_).trans h0
  simp only [section1, Equiv.funUnique_apply]
  congr 2
  congr 1
  funext j
  rw [Subsingleton.elim j default]

end GlobalTheory.SteepMult

end
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_orthogonal_kernel : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N →
    ∀ (B : N →ₗ⋆[ℂ] N →ₗ[ℂ] ℂ) (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N),
    Ψ ∈ ((filt M.act N k).comap (phiN M.act N (k + 1))).orthogonalBilin (formT (k + 1) B) →
    ∀ i g, section1 Ψ i g ∈ (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) := by
  atlas_forward_decl GlobalTheory.SteepMult.section1_mem_orthogonal_ker
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

lemma adP_Eab_diag {R S : ℕ} (c : Ix R S) (y x : NC R S) :
    adP (Eab c c) y x =
      if y = x then ((if c = y.1.1 then 1 else 0) - (if c = y.1.2 then 1 else 0)) else 0 := by
  obtain ⟨⟨y1, y2⟩, hy⟩ := y
  obtain ⟨⟨x1, x2⟩, hx⟩ := x
  simp only [adP, Eab, Matrix.single_apply, Subtype.mk.injEq, Prod.mk.injEq]
  split_ifs <;> aesop

theorem hw_tensor_one : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∀ (ν : Ix R S → ℚ) (y : (Fin 1 → NC R S) → W), IsHW (tAct 1 actW) ν y →
      ∃ a b, ¬ sameBlock a b ∧ ν = GlobalTheory.RealLift.addRoot Λ a b := by
  intro R S W _ _ _ actW Λ v hL hwts hv hgen ν y hy
  have hirr : ∀ U, KStable actW U → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    rcases GlobalTheory.BlockReps.gen_irred (W := ⊤) hL (fun Z _ w _ => Submodule.mem_top) (fun w _ => hwts w)
      Submodule.mem_top hv U hU (hgen ▸ le_top) with h | h
    · exact Or.inl h
    · exact Or.inr (top_le_iff.1 (hgen ▸ GlobalTheory.BlockReps.gen_le h hU))
  obtain ⟨φ, hφ, h1, h2⟩ := GlobalTheory.TensorHW.exists_dual hL hv hirr
  obtain ⟨hy0, hy⟩ := hy
  rw [GlobalTheory.TensorHW.mem_hw] at hy
  obtain ⟨hyw, hyr⟩ := hy
  have hupd : ∀ (g : Fin 1 → NC R S) (x : NC R S), Function.update g 0 x = fun _ => x := by
    intro g x; funext i; rw [Subsingleton.elim i 0]; simp
  have hex : ∃ x : NC R S, φ (y fun _ => x) ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hall : ∀ g, φ (y g) = 0 := fun g => by
      have : g = fun _ => g 0 := by funext i; rw [Subsingleton.elim i 0]
      rw [this]; exact hne _
    have hbot := GlobalTheory.TensorHW.ker_bot hL hirr φ hφ h1 h2 (Submodule.span ℂ (Set.range y)) ?_ ?_
    · apply hy0
      funext g
      have : y g ∈ Submodule.span ℂ (Set.range y) := Submodule.subset_span ⟨g, rfl⟩
      rw [hbot] at this
      exact this
    · rw [Submodule.span_le]; rintro _ ⟨g, rfl⟩; exact hall g
    · intro a b hab
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      have := congrFun (hyr a b hab) g
      rw [tAct_apply] at this
      simp only [Pi.zero_apply] at this
      show actW (Eab a b) (y g) ∈ Submodule.span ℂ (Set.range y)
      rw [eq_neg_of_add_eq_zero_left this]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun x _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
  obtain ⟨x, hx⟩ := hex
  refine ⟨x.1.1, x.1.2, x.2, funext fun c => ?_⟩
  have := congrArg φ (congrFun (hyw c) (fun _ => x))
  rw [tAct_apply] at this
  simp only [Fin.sum_univ_one, adP_Eab_diag, hupd, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, map_add, map_smul, h1, Pi.smul_apply, smul_eq_mul] at this
  have key : ((ν c : ℚ) : ℂ) = ((GlobalTheory.RealLift.addRoot Λ x.1.1 x.1.2 c : ℚ) : ℂ) := by
    apply mul_right_cancel₀ hx
    rw [← this]
    simp only [GlobalTheory.RealLift.addRoot]
    split_ifs <;> push_cast <;> ring
  exact_mod_cast key

end GlobalTheory.SteepMult
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.highest_weight_tensor_root_shift : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Λ : Ix R S → ℚ) (v : W), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsHW actW Λ v → GlobalTheory.BlockReps.gen actW v = ⊤ →
    ∀ (ν : Ix R S → ℚ) (y : (Fin 1 → NC R S) → W), IsHW (tAct 1 actW) ν y →
      ∃ a b, ¬ sameBlock a b ∧ ν = GlobalTheory.RealLift.addRoot Λ a b := by
  atlas_forward_decl GlobalTheory.SteepMult.hw_tensor_one
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult GlobalTheory.TensorHW GlobalTheory.BlockReps

noncomputable section

namespace GlobalTheory.CasimirBound

variable {R S : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
  {actW : Mat R S →ₗ[ℂ] Module.End ℂ W} {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ}

lemma unitK_adj (hB : IsUnitary actW B) (a b : Ix R S) (x y : W) :
    B (unitK actW a b x) y = B x (unitK actW b a y) := by
  by_cases h : sameBlock a b
  · have h' : sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    rw [unitK, unitK, if_pos h, if_pos h']
    exact hB.2.2 a b h x y
  · have h' : ¬ sameBlock b a := by cases a <;> cases b <;> simp_all [sameBlock]
    simp [unitK, h, h']

lemma casK_adj (hB : IsUnitary actW B) (x y : W) :
    B (casK actW x) y = B x (casK actW y) := by
  simp only [casK, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [unitK_adj hB, unitK_adj hB]

lemma finrank_map_add_inf_ker [FiniteDimensional ℂ W] (U : Submodule ℂ W) (f : Module.End ℂ W) :
    Module.finrank ℂ (U.map f) + Module.finrank ℂ (U ⊓ LinearMap.ker f : Submodule ℂ W) =
      Module.finrank ℂ U := by
  have h := (f.domRestrict U).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype] at h
  exact h

lemma finiteRing_sq_sub_mul_sq_eq_of_card [FiniteDimensional ℂ W] (hL : IsKLieAct actW)
    (hd : ∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) (hB : IsUnitary actW B) (c₀ : ℚ) (n : ℕ) :
    ∀ U : Submodule ℂ W, Module.finrank ℂ U ≤ n → KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (casK actW x)).re := by
  induction n with
  | zero =>
    intro U hU _ _ x hx h0
    have : U = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hU)
    subst this
    exact absurd ((Submodule.mem_bot ℂ).1 hx) h0
  | succ n ih =>
    intro U hU hUs hc x hx h0
    obtain ⟨ν, v, hvU, hv⟩ := exists_hw hL hUs (fun w _ => hd w) ((Submodule.ne_bot_iff U).2 ⟨x, hx, h0⟩)
    set c : ℂ := ((casVal ν : ℚ) : ℂ) with hcdef
    set f : Module.End ℂ W := casK actW - c • 1 with hf
    set E : Submodule ℂ W := U ⊓ LinearMap.ker f with hE
    set U₂ : Submodule ℂ W := U.map f with hU₂
    have hstar : starRingEnd ℂ c = c := by rw [hcdef, map_ratCast]
    have hfadj : ∀ y z, B (f y) z = B y (f z) := by
      intro y z
      simp only [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
        LinearMap.map_smulₛₗ₂, LinearMap.sub_apply, hstar, casK_adj hB, smul_eq_mul, LinearMap.smul_apply, map_smul]
    have hfU : ∀ u ∈ U, f u ∈ U := fun u hu => U.sub_mem (casK_mem hUs hu) (U.smul_mem _ hu)
    have hU₂U : U₂ ≤ U := Submodule.map_le_iff_le_comap.2 fun u hu => hfU u hu
    have hcomm : ∀ a b, sameBlock a b → ∀ y, actW (Eab a b) (f y) = f (actW (Eab a b) y) := by
      intro a b hab y
      rw [← Module.End.mul_apply, ← Module.End.mul_apply]
      congr 1
      exact ((casK_comm hL hab).sub_right ((Commute.one_right _).smul_right _)).eq
    have hU₂s : KStable actW U₂ := by
      intro Z hZ w hw
      obtain ⟨u, hu, rfl⟩ := hw
      refine kc_ind actW U₂ (f u) (fun a b hab => ?_) hZ
      rw [hcomm a b hab]
      exact ⟨_, hUs _ (isKC_Eab hab) u hu, rfl⟩
    have horth : ∀ e ∈ E, ∀ z ∈ U₂, B e z = 0 := by
      intro e he z hz
      obtain ⟨u, -, rfl⟩ := hz
      rw [← hfadj, LinearMap.mem_ker.1 he.2, map_zero, LinearMap.zero_apply]
    have hdisj : E ⊓ U₂ = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Submodule.mem_bot]
      by_contra hz0
      have := hB.2.1 z hz0
      rw [horth z hz.1 z hz.2] at this
      simp at this
    have hdim : Module.finrank ℂ U₂ + Module.finrank ℂ E = Module.finrank ℂ U :=
      finrank_map_add_inf_ker U f
    have hsup : E ⊔ U₂ = U := by
      have h1 : Module.finrank ℂ (E ⊔ U₂ : Submodule ℂ W) + Module.finrank ℂ (E ⊓ U₂ : Submodule ℂ W) =
          Module.finrank ℂ E + Module.finrank ℂ U₂ := Submodule.finrank_sup_add_finrank_inf_eq E U₂
      rw [hdisj, finrank_bot] at h1
      exact Submodule.eq_of_le_of_finrank_eq (sup_le inf_le_left hU₂U) (by omega)
    have hvE : v ∈ E := ⟨hvU, by simp [hf, casK_hw hL hv.2, hcdef]⟩
    have hlt : Module.finrank ℂ U₂ < Module.finrank ℂ U := by
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne hU₂U fun h => hv.1 ?_
      have : v ∈ E ⊓ U₂ := ⟨hvE, h ▸ hvU⟩
      rwa [hdisj, Submodule.mem_bot] at this
    have hcv := hc ν v hvU hv
    obtain ⟨e, he, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ hx : x ∈ E ⊔ U₂)
    have hce : casK actW e = c • e := by
      have := LinearMap.mem_ker.1 he.2
      simp only [hf, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at this
      exact sub_eq_zero.1 this
    have hze : B z e = 0 := by rw [← hB.1, horth e he z hz, star_zero]
    have hcz : B e (casK actW z) = 0 := by
      rw [← casK_adj hB, hce, LinearMap.map_smulₛₗ₂, horth e he z hz, smul_zero]
    have hIH : z ≠ 0 → (c₀ : ℝ) * (B z z).re < (B z (casK actW z)).re := fun hz0 =>
      ih U₂ (by omega) hU₂s (fun ν y hy => hc ν y (hU₂U hy)) z hz hz0
    have ex1 : B (e + z) (e + z) = B e e + B z z := by
      simp only [map_add, LinearMap.add_apply, horth e he z hz, hze]; ring
    have ex2 : B (e + z) (casK actW (e + z)) = c * B e e + B z (casK actW z) := by
      simp only [map_add, LinearMap.add_apply, hce, LinearMap.map_smul, hcz, hze, smul_eq_mul]; ring
    have hcr : (c * B e e).re = (casVal ν : ℝ) * (B e e).re := by
      simp [hcdef, Complex.mul_re]
    have hc' : (c₀ : ℝ) < (casVal ν : ℝ) := by exact_mod_cast hcv
    rw [ex1, ex2, Complex.add_re, Complex.add_re, hcr]
    by_cases he0 : e = 0
    · subst he0
      have hz0 : z ≠ 0 := by simpa using h0
      have := hIH hz0
      simp only [map_zero, LinearMap.zero_apply, Complex.zero_re, mul_zero, zero_add]
      exact this
    · have hpos := hB.2.1 e he0
      have h2 : (c₀ : ℝ) * (B z z).re ≤ (B z (casK actW z)).re := by
        by_cases hz0 : z = 0
        · subst hz0; simp
        · exact (hIH hz0).le
      nlinarith

theorem casimir_form_gt : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c₀ : ℚ), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsUnitary actW B → ∀ U : Submodule ℂ W, KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < GlobalTheory.BlockReps.casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (GlobalTheory.BlockReps.casK actW x)).re := by
  intro R S W _ _ _ actW B c₀ hL hd hB U hU hc
  exact finiteRing_sq_sub_mul_sq_eq_of_card hL hd hB c₀ _ U le_rfl hU hc

end GlobalTheory.CasimirBound
end
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_lower_bound_on_stable_subspace : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c₀ : ℚ), IsKLieAct actW →
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub actW μ) → IsUnitary actW B → ∀ U : Submodule ℂ W, KStable actW U →
    (∀ (ν : Ix R S → ℚ) y, y ∈ U → IsHW actW ν y → c₀ < GlobalTheory.BlockReps.casVal ν) →
    ∀ x ∈ U, x ≠ 0 → (c₀ : ℝ) * (B x x).re < (B x (GlobalTheory.BlockReps.casK actW x)).re := by
  atlas_forward_decl GlobalTheory.CasimirBound.casimir_form_gt
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.GenHW

theorem block_span_hw : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    FiniteDimensional ℂ (GlobalTheory.BlockReps.gen M.act v) ∧
    IsKLieAct (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ∧
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) μ) ∧
    IsHW (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) Λ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ ∧
    GlobalTheory.BlockReps.gen (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ = ⊤ := by
  intro R S M Λ v hv
  have hKS : KStable M.act (GlobalTheory.BlockReps.gen M.act v) := GlobalTheory.BlockReps.stable_gen (act := M.act) v
  set G := GlobalTheory.BlockReps.gen M.act v with hG
  set ρ := restrAct M.act G hKS with hρ
  have hρapp : ∀ Z, IsKC Z → ∀ x : G, ((ρ Z x : G) : M.V) = M.act Z x := by
    intro Z hZ x
    rw [hρ, restrAct_apply, kpart_of_isKC hZ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨W, hWf, hvW, hWs⟩ := M.kfin v
    exact Submodule.finiteDimensional_of_le (GlobalTheory.BlockReps.gen_le hvW hWs)
  · intro Y Z hY hZ
    ext x
    have hYZ := GlobalTheory.TensorHW.isKC_comm hY hZ
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub]
    rw [hρapp _ hYZ, hρapp _ hY, hρapp _ hZ, hρapp _ hZ, hρapp _ hY, M.lie]
    simp
  · intro w
    have h := GlobalTheory.BlockReps.decomp hKS w.2 (M.wts w)
    have hle : (⨆ μ, G ⊓ wtSub M.act μ) ≤ (⨆ μ : Ix R S → ℚ, wtSub ρ μ).map G.subtype := by
      refine iSup_le fun μ x hx => ⟨⟨x, hx.1⟩, Submodule.mem_iSup_of_mem μ ?_, rfl⟩
      rw [GlobalTheory.TensorHW.mem_wt]
      intro a
      apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact GlobalTheory.TensorHW.mem_wt.1 hx.2 a
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle h)
    rwa [Subtype.val_injective hyw] at hy
  · refine ⟨fun h => hv.1 (congrArg Subtype.val h), ?_⟩
    have hv2 := GlobalTheory.TensorHW.mem_hw.1 hv.2
    rw [GlobalTheory.TensorHW.mem_hw]
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl a))]
      exact hv2.1 a
    · apply Subtype.ext
      rw [hρapp _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hab))]
      exact hv2.2 a b hab
  · set N := GlobalTheory.BlockReps.gen ρ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hN
    have hNs : KStable ρ N := GlobalTheory.BlockReps.stable_gen (act := ρ) _
    have hmap : KStable M.act (N.map G.subtype) := by
      rintro X hX _ ⟨y, hy, rfl⟩
      exact ⟨ρ X y, hNs X hX y hy, hρapp X hX y⟩
    have hle : G ≤ N.map G.subtype :=
      GlobalTheory.BlockReps.gen_le ⟨⟨v, GlobalTheory.BlockReps.mem_gen v⟩, GlobalTheory.BlockReps.mem_gen _, rfl⟩ hmap
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 (hle w.2)
    rwa [Subtype.val_injective hyw] at hy

end GlobalTheory.GenHW
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generated_submodule_highest_weight_structure : ∀ (R S : ℕ) (M : GKMod R S) (Λ : Ix R S → ℚ) (v : M.V), IsHW M.act Λ v →
    FiniteDimensional ℂ (GlobalTheory.BlockReps.gen M.act v) ∧
    IsKLieAct (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ∧
    (∀ w, w ∈ ⨆ μ : Ix R S → ℚ, wtSub (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) μ) ∧
    IsHW (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) Λ ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ ∧
    GlobalTheory.BlockReps.gen (restrAct M.act _ (GlobalTheory.BlockReps.stable_gen (act := M.act) v)) ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ = ⊤ := by
  atlas_forward_decl GlobalTheory.GenHW.block_span_hw
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

noncomputable section

namespace GlobalTheory.SteepMult.Filt

variable {R S : ℕ}

lemma sameBlock_symm {a b : Ix R S} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

lemma sameBlock_trans {a b c : Ix R S} (h₁ : sameBlock a b) (h₂ : sameBlock b c) : sameBlock a c := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp_all [sameBlock]

lemma comm_single_apply (Z : Mat R S) (a b c d : Ix R S) :
    ((Z * Matrix.single a b (1 : ℂ) - Matrix.single a b 1 * Z : Mat R S)) c d =
      Z c a * (if d = b then 1 else 0) - (if c = a then 1 else 0) * Z b d := by
  by_cases hd : d = b <;> by_cases hc : c = a
  all_goals (try subst hd); (try subst hc); simp [Matrix.sub_apply, *]

lemma bracket_eNC {Z : Mat R S} (hZ : IsKC Z) (x : NC R S) :
    Z * eNC x - eNC x * Z = ∑ y, adP Z y x • eNC y := by
  ext c d
  rw [Matrix.sum_apply]
  simp only [eNC, Eab, Matrix.smul_apply, smul_eq_mul]
  rw [comm_single_apply]
  obtain ⟨⟨a, b⟩, hab⟩ := x
  by_cases h : sameBlock c d
  · rw [Finset.sum_eq_zero]
    · simp only
      by_cases hd : d = b
      · subst hd
        have hca : ¬ sameBlock c a := fun h' => hab (sameBlock_trans (sameBlock_symm h') h)
        by_cases hc : c = a
        · subst hc; exact absurd h hab
        · simp [hZ _ _ hca, hc]
      · by_cases hc : c = a
        · subst hc
          have hbd : ¬ sameBlock b d := fun h' => hab (sameBlock_trans h (sameBlock_symm h'))
          simp [hZ _ _ hbd, hd]
        · simp [hd, hc]
    · intro y _
      have : ¬ (y.1.1 = c ∧ y.1.2 = d) := fun ⟨h1, h2⟩ => y.2 (h1 ▸ h2 ▸ h)
      simp [Matrix.single_apply, this]
  · rw [Finset.sum_eq_single ⟨(c, d), h⟩]
    · simp [adP]
    · intro y _ hy
      have : ¬ (y.1.1 = c ∧ y.1.2 = d) := fun ⟨h1, h2⟩ => hy (Subtype.ext (Prod.ext h1 h2))
      simp [Matrix.single_apply, this]
    · simp

variable {V : Type} [AddCommGroup V] [Module ℂ V]

lemma act_comm_eNC {act : Mat R S →ₗ[ℂ] Module.End ℂ V} (hlie : IsLieAct act) {Z : Mat R S} (hZ : IsKC Z)
    (x : NC R S) (w : V) :
    act Z (act (eNC x) w) = act (eNC x) (act Z w) + ∑ y, adP Z y x • act (eNC y) w := by
  have h := hlie Z (eNC x)
  rw [bracket_eNC hZ x] at h
  have h2 := congrArg (fun T : Module.End ℂ V => T w) h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, Module.End.mul_apply] at h2
  rw [h2]; abel

lemma word_zero (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (g : Fin 0 → NC R S) : word act g = 1 := by
  simp [word]

lemma word_cons (act : Mat R S →ₗ[ℂ] Module.End ℂ V) {k : ℕ} (x : NC R S) (g : Fin k → NC R S) :
    word act (Fin.cons x g : Fin (k + 1) → NC R S) = act (eNC x) * word act g := by
  simp [word, List.ofFn_succ]

lemma word_mem_range (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (g : Fin k → NC R S)
    {n : V} (hn : n ∈ N) : word act g n ∈ LinearMap.range (phiN act N k) := by
  classical
  refine ⟨Pi.single g ⟨n, hn⟩, ?_⟩
  rw [phiN_apply, Finset.sum_eq_single g]
  · simp
  · intro h _ hh; simp [Pi.single_apply, hh]
  · simp

lemma act_eNC_mem_range (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) {k : ℕ} (x : NC R S) {w : V}
    (hw : w ∈ LinearMap.range (phiN act N k)) : act (eNC x) w ∈ LinearMap.range (phiN act N (k + 1)) := by
  obtain ⟨Ψ, rfl⟩ := hw
  rw [phiN_apply, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  have := word_mem_range act N (Fin.cons x g : Fin (k + 1) → NC R S) (Ψ g).2
  rwa [word_cons, Module.End.mul_apply] at this

lemma kstable_range {act : Mat R S →ₗ[ℂ] Module.End ℂ V} (hlie : IsLieAct act) (N : Submodule ℂ V)
    (hN : KStable act N) (k : ℕ) : KStable act (LinearMap.range (phiN act N k)) := by
  induction k with
  | zero =>
    intro Z hZ w hw
    obtain ⟨Ψ, rfl⟩ := hw
    rw [phiN_apply, map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have := word_mem_range act N g (hN Z hZ _ (Ψ g).2)
    simpa [word_zero] using this
  | succ k ih =>
    intro Z hZ w hw
    obtain ⟨Ψ, rfl⟩ := hw
    rw [phiN_apply, map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    rw [← Fin.cons_self_tail g, word_cons, Module.End.mul_apply, act_comm_eNC hlie hZ]
    have hw' := word_mem_range act N (Fin.tail g) (Ψ (Fin.cons (g 0) (Fin.tail g))).2
    refine add_mem (act_eNC_mem_range act N _ (ih Z hZ _ hw')) (Submodule.sum_mem _ fun y _ => ?_)
    exact Submodule.smul_mem _ _ (act_eNC_mem_range act N _ hw')

theorem filt_basic : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ k : ℕ,
    KStable M.act (filt M.act N k) ∧
    filt M.act N (k + 1) = filt M.act N k ⊔ LinearMap.range (phiN M.act N (k + 1)) ∧ filt M.act N 0 ≤ N := by
  intro R S M N hN k
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ w hw
    refine Submodule.iSup_induction (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j))
      (motive := fun w => M.act Z w ∈ filt M.act N k) hw ?_ ?_ ?_
    · intro j w hw
      exact (le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j)) j)
        (kstable_range M.lie N hN j Z hZ w hw)
    · simp
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · apply le_antisymm
    · refine iSup_le fun j => ?_
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact le_sup_right
      · exact le_sup_of_le_left (le_iSup (fun j : Fin (k + 1) => LinearMap.range (phiN M.act N j)) i)
    · refine sup_le (iSup_le fun i => ?_) ?_
      · exact le_iSup (fun j : Fin (k + 2) => LinearMap.range (phiN M.act N j)) i.castSucc
      · exact le_iSup (fun j : Fin (k + 2) => LinearMap.range (phiN M.act N j)) (Fin.last (k + 1))
  · refine iSup_le fun j => ?_
    obtain rfl : j = 0 := Fin.fin_one_eq_zero j
    rintro _ ⟨Ψ, rfl⟩
    rw [phiN_apply]
    refine Submodule.sum_mem _ fun g _ => ?_
    have : word M.act g = 1 := by simp [word]
    rw [this]; exact (Ψ g).2

end GlobalTheory.SteepMult.Filt

end
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_stable_and_increasing : ∀ (R S : ℕ) (M : GKMod R S) (N : Submodule ℂ M.V), KStable M.act N → ∀ k : ℕ,
    KStable M.act (filt M.act N k) ∧
    filt M.act N (k + 1) = filt M.act N k ⊔ LinearMap.range (phiN M.act N (k + 1)) ∧ filt M.act N 0 ≤ N := by
  atlas_forward_decl GlobalTheory.SteepMult.Filt.filt_basic
end

section
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.CasimirCoord

theorem sum_lt_sub : ∀ (n : ℕ) (f : Fin n → ℚ),
    ∑ i, ∑ j, (if i < j then f i - f j else 0) = ∑ i : Fin n, f i * ((n:ℚ) - 1 - 2 * ((i:ℕ):ℚ))
  | 0, f => by simp
  | n+1, f => by
    have h := sum_lt_sub n (fun i => f i.succ)
    simp only [Fin.sum_univ_succ, Fin.succ_lt_succ_iff, Fin.not_lt_zero, Fin.succ_pos, if_true, if_false,
      lt_irrefl, zero_add] at h ⊢
    rw [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e : ∑ i : Fin n, f i.succ * (((n+1:ℕ):ℚ) - 1 - 2 * ((i.succ:ℕ):ℚ))
        = ∑ i : Fin n, f i.succ * ((n:ℚ) - 1 - 2 * ((i:ℕ):ℚ)) - ∑ i : Fin n, f i.succ := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ]; push_cast; ring
    rw [e]; simp only [Fin.val_zero]; push_cast; ring

open Classical in
theorem casVal_eq_casK : ∀ (R S : ℕ) (μ : Ix R S → ℚ), GlobalTheory.BlockReps.casVal μ = GlobalTheory.RealLift.casK μ := by
  intro R S μ
  have hx : ∀ i j : Fin R, (if posC (Sum.inl i : Ix R S) (Sum.inl j) then μ (Sum.inl i) - μ (Sum.inl j) else 0)
      = if i < j then μ (Sum.inl i) - μ (Sum.inl j) else 0 := by
    intro i j; by_cases h : i < j
    · rw [if_pos (show posC (Sum.inl i : Ix R S) (Sum.inl j) from h), if_pos h]
    · rw [if_neg (show ¬ posC (Sum.inl i : Ix R S) (Sum.inl j) from h), if_neg h]
  have hy : ∀ i j : Fin S, (if posC (Sum.inr i : Ix R S) (Sum.inr j) then μ (Sum.inr i) - μ (Sum.inr j) else 0)
      = if i < j then μ (Sum.inr i) - μ (Sum.inr j) else 0 := by
    intro i j; by_cases h : i < j
    · rw [if_pos (show posC (Sum.inr i : Ix R S) (Sum.inr j) from h), if_pos h]
    · rw [if_neg (show ¬ posC (Sum.inr i : Ix R S) (Sum.inr j) from h), if_neg h]
  have hlr : ∀ (i : Fin R) (j : Fin S),
      (if posC (Sum.inl i : Ix R S) (Sum.inr j) then μ (Sum.inl i) - μ (Sum.inr j) else 0) = 0 :=
    fun i j => if_neg (show ¬ posC (Sum.inl i : Ix R S) (Sum.inr j) from id)
  have hrl : ∀ (i : Fin S) (j : Fin R),
      (if posC (Sum.inr i : Ix R S) (Sum.inl j) then μ (Sum.inr i) - μ (Sum.inl j) else 0) = 0 :=
    fun i j => if_neg (show ¬ posC (Sum.inr i : Ix R S) (Sum.inl j) from id)
  unfold GlobalTheory.BlockReps.casVal GlobalTheory.RealLift.casK
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← sq]
  rw [add_assoc]
  congr 1
  simp only [Fintype.sum_sum_type, hx, hy, hlr, hrl, Finset.sum_const_zero, add_zero, zero_add]
  rw [sum_lt_sub R (fun i => μ (Sum.inl i)), sum_lt_sub S (fun j => μ (Sum.inr j))]

end GlobalTheory.CasimirCoord
end

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_casimir_eq_real_casimir : ∀ (R S : ℕ) (μ : Ix R S → ℚ), GlobalTheory.BlockReps.casVal μ = GlobalTheory.RealLift.casK μ := by
  atlas_forward_decl GlobalTheory.CasimirCoord.casVal_eq_casK
end

section
section
noncomputable section
open scoped TensorProduct

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem multOne : GlobalTheory.RealLift.MultOne := by
  intro R S M Λ v hv hgen hsteep w hw
  classical
  have hML : IsKLieAct M.act := fun Y Z _ _ => M.lie Y Z
  obtain ⟨hfin, hlie, hwts, hvN, hgenN⟩ := GlobalTheory.T.generated_submodule_highest_weight_structure R S M Λ v hv
  have hN : KStable M.act (GlobalTheory.BlockReps.gen M.act v) := GlobalTheory.BlockReps.stable_gen (act := M.act) v
  set N := GlobalTheory.BlockReps.gen M.act v with hNdef
  haveI : FiniteDimensional ℂ N := hfin
  set A := restrAct M.act N hN with hA
  set v₀ : N := ⟨v, GlobalTheory.BlockReps.mem_gen v⟩ with hv₀
  obtain ⟨B, hB⟩ := GlobalTheory.T.highest_weight_module_unitary_form R S N A Λ v₀ hlie hwts hvN hgenN
  set c : ℚ := GlobalTheory.BlockReps.casVal Λ with hc

  have hcasN : ∀ x : N, GlobalTheory.BlockReps.casK A x = ((c : ℚ) : ℂ) • x := by
    have hker := GlobalTheory.BlockReps.stable_ker (act := A) hlie ((c : ℚ) : ℂ) 1
    have hv1 : v₀ ∈ LinearMap.ker ((GlobalTheory.BlockReps.casK A - ((c : ℚ) : ℂ) • 1) ^ 1) := by
      rw [pow_one, LinearMap.mem_ker, LinearMap.sub_apply, GlobalTheory.BlockReps.casK_hw hlie hvN.2]
      simp [hc]
    have htop := GlobalTheory.BlockReps.gen_le hv1 hker
    rw [hgenN] at htop
    intro x
    have := htop (Submodule.mem_top (x := x))
    rw [pow_one, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    simpa using this
  set P1 := (LinearMap.ker (phiN M.act N 1)).orthogonalBilin (formT 1 B) with hP1
  have hU1 := GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S 1 N A B hB

  have hpos : ∀ x ∈ P1, x ≠ 0 → ((((R + S : ℕ) : ℚ) + c : ℚ) : ℝ) * (formT 1 B x x).re <
      (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re := by
    have hL1 := GlobalTheory.T.tensor_action_is_lie_action R S 1 N A hlie
    have hW1 := GlobalTheory.T.tensor_action_weight_decomposition R S 1 N A hwts
    have hkerS : KStable (tAct 1 A) (LinearMap.ker (phiN M.act N 1)) := fun Z hZ x hx => by
      rw [LinearMap.mem_ker] at hx ⊢
      rw [GlobalTheory.T.filtration_map_equivariant R S M N hN 1 Z hZ, hx, map_zero]
    have hPS := (GlobalTheory.T.unitary_form_orthogonal_complement R S _ (tAct 1 A) (formT 1 B) hU1 _ hkerS).1
    refine GlobalTheory.T.casimir_lower_bound_on_stable_subspace R S _ (tAct 1 A) (formT 1 B) _ hL1 hW1 hU1 P1 hPS ?_
    intro ν y hyP hy
    obtain ⟨a, b, hab, rfl⟩ := GlobalTheory.T.highest_weight_tensor_root_shift R S N A Λ v₀ hlie hwts hvN hgenN ν y hy
    have hφ0 : phiN M.act N 1 y ≠ 0 := by
      intro h0
      have h1 := (Submodule.mem_orthogonalBilin_iff.1 hyP) y (LinearMap.mem_ker.2 h0)
      have hp := hU1.2.1 y hy.1
      have h1' : formT 1 B y y = 0 := h1
      rw [h1'] at hp
      simp at hp
    have hhw : IsHW M.act (GlobalTheory.RealLift.addRoot Λ a b) (phiN M.act N 1 y) := by
      refine ⟨hφ0, ?_⟩
      have hy2 := GlobalTheory.TensorHW.mem_hw.1 hy.2
      refine GlobalTheory.TensorHW.mem_hw.2 ⟨fun d => ?_, fun d e hde => ?_⟩
      · rw [← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_refl d)), hy2.1 d, map_smul]
      · rw [← GlobalTheory.T.filtration_map_equivariant R S M N hN 1 _ (GlobalTheory.TensorHW.isKC_Eab (GlobalTheory.TensorHW.same_of_pos hde)), hy2.2 d e hde, map_zero]
    have := hsteep a b hab _ hhw
    rw [GlobalTheory.T.block_casimir_eq_real_casimir, hc, GlobalTheory.T.block_casimir_eq_real_casimir]
    linarith

  have hno : ∀ (k : ℕ) (Ψ : (Fin (k + 1) → NC R S) → N), Ψ ≠ 0 → Ψ ∈ hwSub (tAct (k + 1) A) Λ →
      (∀ i g, section1 Ψ i g ∈ P1) → False := by
    intro k Ψ hΨ hhw hsec
    set tm : ((Fin 1 → NC R S) → N) → ℝ := fun x => (formT 1 B x (GlobalTheory.BlockReps.casK (tAct 1 A) x)).re -
        ((R + S : ℕ) : ℝ) * (formT 1 B x x).re - (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re with htm
    have hsc : ∀ x : (Fin 1 → NC R S) → N, (formT 1 B x (fun h => GlobalTheory.BlockReps.casK A (x h))).re =
        (c : ℝ) * (formT 1 B x x).re := by
      intro x
      have e : (fun h => GlobalTheory.BlockReps.casK A (x h)) = ((c : ℚ) : ℂ) • x := funext fun h => hcasN _
      rw [e, map_smul, smul_eq_mul]
      have : ((c : ℚ) : ℂ) = ((c : ℝ) : ℂ) := by push_cast; rfl
      rw [this, Complex.re_ofReal_mul]
    have hterm : ∀ x ∈ P1, 0 ≤ tm x ∧ (x ≠ 0 → 0 < tm x) := by
      intro x hx
      have hpos' : x ≠ 0 → 0 < tm x := fun hne => by
        have := hpos x hx hne
        simp only [htm, hsc]
        push_cast at this ⊢
        linarith
      refine ⟨?_, hpos'⟩
      by_cases h0 : x = 0
      · simp [htm, h0]
      · exact (hpos' h0).le
    have hI := GlobalTheory.T.casimir_section_sum_identity R S (k + 1) N A B hB Ψ
    have hcasT : GlobalTheory.BlockReps.casK (tAct (k + 1) A) Ψ = ((c : ℚ) : ℂ) • Ψ :=
      GlobalTheory.BlockReps.casK_hw (GlobalTheory.T.tensor_action_is_lie_action R S (k + 1) N A hlie) hhw
    have hpt : (fun g => GlobalTheory.BlockReps.casK A (Ψ g)) = ((c : ℚ) : ℂ) • Ψ := funext fun g => hcasN _
    rw [hcasT, hpt, sub_self, mul_zero] at hI
    obtain ⟨g₀, hg₀⟩ := Function.ne_iff.1 hΨ
    have hne : section1 Ψ 0 g₀ ≠ 0 := by
      intro h
      have := congrFun h (fun _ => g₀ 0)
      simp only [section1, Function.update_eq_self, Pi.zero_apply] at this
      exact hg₀ this
    have hpos2 : 0 < ∑ i, ∑ g, tm (section1 Ψ i g) := by
      refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun g _ => (hterm _ (hsec i g)).1) ⟨0, Finset.mem_univ _, ?_⟩
      exact Finset.sum_pos' (fun g _ => (hterm _ (hsec 0 g)).1) ⟨g₀, Finset.mem_univ _, (hterm _ (hsec 0 g₀)).2 hne⟩
    exact absurd hI (not_le.2 hpos2)

  have hdesc : ∀ k, w ∈ filt M.act N k → w ∈ N := by
    intro k
    induction k with
    | zero => exact fun h => (GlobalTheory.T.filtration_stable_and_increasing R S M N hN 0).2.2 h
    | succ k ih =>
      intro hk
      by_cases hwk : w ∈ filt M.act N k
      · exact ih hwk
      exfalso
      obtain ⟨hFs, hFeq, -⟩ := GlobalTheory.T.filtration_stable_and_increasing R S M N hN k
      rw [hFeq, sup_comm] at hk
      obtain ⟨Ψ, hΨP, hΨ0, hΨhw⟩ := GlobalTheory.T.exists_highestWeight_orthogonal_comap_of_mem_range_sup R S ((Fin (k + 1) → NC R S) → N) (tAct (k + 1) A) (formT (k + 1) B) M.V
        M.act (phiN M.act N (k + 1)) (filt M.act N k) Λ w (GlobalTheory.T.isUnitary_tAct_formT_of_isUnitary R S (k + 1) N A B hB) hFs
        (fun Z hZ x => GlobalTheory.T.filtration_map_equivariant R S M N hN (k + 1) Z hZ x) hk hw hwk
      exact hno k Ψ hΨ0 hΨhw (GlobalTheory.T.section_orthogonal_kernel R S M N hN B k Ψ hΨP)
  obtain ⟨k, hk⟩ := GlobalTheory.T.generated_module_filtration_exhaustive R S M Λ v hv hgen w
  have hwN := hdesc k hk
  by_cases hw0 : w = 0
  · exact ⟨0, by simp [hw0]⟩
  obtain ⟨-, hspan⟩ := GlobalTheory.BlockReps.hw_unique hML hN (GlobalTheory.BlockReps.mem_gen v) hv hwN ⟨hw0, hw⟩
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hspan
  exact ⟨d, hd.symm⟩

end GlobalTheory.SteepMult

end
end

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multOne' : GlobalTheory.RealLift.MultOne := by
  atlas_forward_decl GlobalTheory.SteepMult.multOne
end
