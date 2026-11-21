import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDiagActEq
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingSelfIrreducibleAlgClos
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsStandardUnipotentRadicalBijOnNilradical
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveExtendZeroOfSumUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FiniteGroupFunctionPairingEqZeroOfDistinctIrredu
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem exists_sum_conj_eq_smul_one {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x : G) :
    ∃ c : ℂ, ∑ h : G, ρ (h * x * h⁻¹) = c • (1 : Module.End ℂ V) := by
  have hc : ∀ g : G, (∑ h : G, ρ (h * x * h⁻¹)) * ρ g = ρ g * ∑ h : G, ρ (h * x * h⁻¹) := by
    intro g
    rw [Finset.sum_mul, Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => ?_).symm
    rw [← map_mul, ← map_mul]
    congr 1
    simp [mul_assoc]
  let T : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := ∑ h : G, ρ (h * x * h⁻¹)
      isIntertwining' := fun g => hc g }
  obtain ⟨c, hT⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).2 T
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  change T v = c • v
  rw [← hT, Algebra.algebraMap_eq_smul_one]
  rfl

theorem character_one_mul_sum_conj_mul {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [ρ.IsIrreducible] (x y : G) :
    ρ.character 1 * ∑ h : G, ρ.character (h * x * h⁻¹ * y)
      = (Fintype.card G : ℂ) * (ρ.character x * ρ.character y) := by
  obtain ⟨c, hc⟩ := exists_sum_conj_eq_smul_one ρ x
  have key : ∀ z : G, ∑ h : G, ρ.character (h * x * h⁻¹ * z) = c * ρ.character z := by
    intro z
    have := congrArg (fun A => LinearMap.trace ℂ V (A * ρ z)) hc
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, one_mul, map_smul, smul_eq_mul, ← map_mul] at this
    exact this
  have h1 := key 1
  simp only [mul_one, Representation.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [key y, ← mul_assoc, mul_comm _ c, ← h1, mul_assoc]

theorem irrChar_one_mul_finsum_conj_mul : ∀ (G : Type) [Group G] [Finite G] (χ : G → ℂ), IsIrrChar ℂ ℂ χ → ∀ x y : G, χ 1 * ∑ᶠ h : G, χ (h * x * h⁻¹ * y) = (Nat.card G : ℂ) * (χ x * χ y) := by
  intro G _ _ χ hχ x y
  let := Fintype.ofFinite G
  obtain ⟨n, ρ, hρ, h⟩ := hχ
  have hh : χ = ρ.character := by
    funext g
    simpa using h g
  subst hh
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  exact character_one_mul_sum_conj_mul ρ x y

end GlobalTheory
end

section
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.IrrPi

theorem isChar_of_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : IsChar ℂ ℂ χ := by
  obtain ⟨n, ρ, _, h⟩ := h
  exact ⟨n, ρ, h⟩

theorem pair_prod {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (a b : ∀ i, G i → ℂ) :
    pair (fun x : ∀ i, G i => ∏ i, a i (x i)) (fun x => ∏ i, b i (x i)) = ∏ i, pair (a i) (b i) := by
  classical
  have := fun i => Fintype.ofFinite (G i)
  simp only [pair, finsum_eq_sum_of_fintype, Finset.prod_mul_distrib, Nat.card_pi, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_univ_sum, Fintype.piFinset_univ, Pi.inv_apply]

theorem irr_one {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, n ≠ 0 ∧ χ 1 = n := by
  obtain ⟨n, hn, h0⟩ := (isChar_restrict_conj_one ℂ ℂ G χ (isChar_of_irr h)).2.2
  refine ⟨n, fun h1 => ?_, hn⟩
  have := pair_self_of_isIrrChar_algClosed ℂ G χ h
  rw [h0 h1] at this
  simp [pair] at this

theorem irr_mulSingle {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (i : ι) (a : G i) (y : ∀ i, G i)
    (hy : y i = 1) : χ 1 * χ (Pi.mulSingle i a * y) = χ (Pi.mulSingle i a) * χ y := by
  have := Fintype.ofFinite (∀ i, G i)
  have h1 := irrChar_one_mul_finsum_conj_mul _ χ h (Pi.mulSingle i a) y
  have hc := (isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).2.1
  have h2 : ∀ k : ∀ i, G i, χ (k * Pi.mulSingle i a * k⁻¹ * y) = χ (Pi.mulSingle i a * y) := by
    intro k
    rw [← hc (Pi.mulSingle i a * y) (Pi.mulSingle i (k i)⁻¹)]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hy]
    · simp [Pi.mulSingle_eq_of_ne hj]
  simp only [h2, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [Nat.card_eq_fintype_card] at h1
  have hN : (Fintype.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ hN
  rw [← h1]
  ring

theorem irr_factor {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (x : ∀ i, G i) :
    χ x = χ 1 * ∏ i, (χ (Pi.mulSingle i (x i)) / χ 1) := by
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have key : ∀ s : Finset ι, χ (fun j => if j ∈ s then x j else 1) =
      χ 1 * ∏ i ∈ s, (χ (Pi.mulSingle i (x i)) / χ 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one]
      rfl
    | insert i s hi ih =>
      have e : (fun j => if j ∈ insert i s then x j else 1) =
          Pi.mulSingle i (x i) * (fun j => if j ∈ s then x j else 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · simp [Pi.mulSingle_eq_of_ne hj, hj]
      have := irr_mulSingle h i (x i) (fun j => if j ∈ s then x j else 1) (by simp [hi])
      rw [e, Finset.prod_insert hi]
      apply mul_left_cancel₀ h0
      rw [this, ih]
      field_simp
  simpa using key Finset.univ

theorem exists_irr_pair_ne {G : Type} [Group G] [Finite G] {φ : G → ℂ} (h : φ ∈ Virt ℂ ℂ G)
    (h1 : φ 1 ≠ 0) : ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair φ ψ ≠ 0 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨c, hc, hφ, -⟩ := virt_expand G φ h
  have hne : c.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    rw [hφ] at h1
    simp at h1
  obtain ⟨ψ, hψ⟩ := hne
  refine ⟨ψ, hc ψ hψ, ?_⟩
  have e : pair φ ψ = ∑ χ ∈ c.support, (c χ : ℂ) * pair χ ψ := by
    rw [hφ]
    simp only [pair, finsum_eq_sum_of_fintype, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      zsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Pi.mul_apply, Pi.intCast_apply]
    ring
  rw [e, Finset.sum_eq_single ψ]
  · rw [pair_self_of_isIrrChar_algClosed ℂ G ψ (hc ψ hψ), mul_one]
    exact_mod_cast Finsupp.mem_support_iff.1 hψ
  · intro b hb hbψ
    rw [pair_eq_zero_of_isIrrChar_ne G b ψ (hc b hb) (hc ψ hψ) hbψ, mul_zero]
  · intro h
    exact absurd hψ h

theorem prod_mem_virt {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] (ψ : ∀ i, G i → ℂ) (h : ∀ i, ψ i ∈ Virt ℂ ℂ (G i)) :
    (fun x : ∀ i, G i => ∏ i, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
  classical
  have key : ∀ s : Finset ι, (fun x : ∀ i, G i => ∏ i ∈ s, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact AddSubgroup.subset_closure (by simpa using isChar_one ℂ ℂ (∀ i, G i))
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (virt_mul_comap_conj_ind_linear (∀ i, G i)).1 _
        ((virt_mul_comap_conj_ind_linear (G i)).2.1 _ (h i) _ (Pi.evalMonoidHom G i)) _ ih
  exact key _

end GlobalTheory.IrrPi

namespace GlobalTheory
open IrrPi

theorem irrChar_pi_eq_prod : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by
  intro ι _ G _ _ χ h
  classical
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have hφ : ∀ i, ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair (fun a : G i => χ (Pi.mulSingle i a)) ψ ≠ 0 := by
    intro i
    refine exists_irr_pair_ne (AddSubgroup.subset_closure
      ((isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).1 _ (MonoidHom.mulSingle G i))) ?_
    simpa using h0
  choose ψ hψ hp using hφ
  refine ⟨ψ, hψ, ?_⟩
  have hV := prod_mem_virt ψ fun i => AddSubgroup.subset_closure (isChar_of_irr (hψ i))
  set Ψ : (∀ i, G i) → ℂ := fun x => ∏ i, ψ i (x i) with hΨ
  have hN : (Nat.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hnorm : ∑ᶠ g, Ψ g * star (Ψ g) = (Nat.card (∀ i, G i) : ℂ) := by
    have : pair Ψ Ψ = 1 := by
      rw [hΨ, pair_prod]
      exact Finset.prod_eq_one fun i _ => pair_self_of_isIrrChar_algClosed ℂ _ _ (hψ i)
    simp only [star_virt_eq_inv _ Ψ hV]
    unfold pair at this
    field_simp at this
    exact this
  have hpair : pair χ Ψ ≠ 0 := by
    have e : pair χ Ψ = χ 1 * pair (fun x : ∀ i, G i => ∏ i, χ (Pi.mulSingle i (x i)) / χ 1) Ψ := by
      unfold pair
      have := Fintype.ofFinite (∀ i, G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [irr_factor h x]
      ring
    rw [e, hΨ, pair_prod (fun i (a : G i) => χ (Pi.mulSingle i a) / χ 1) ψ]
    refine mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have e2 : pair (fun a => χ (Pi.mulSingle i a) / χ 1) (ψ i) =
        pair (fun a : G i => χ (Pi.mulSingle i a)) (ψ i) / χ 1 := by
      unfold pair
      have := Fintype.ofFinite (G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e2]
    exact div_ne_zero (hp i) h0
  rcases (irr_of_norm_one _ Ψ hV hnorm).1 with hI | hI
  · by_contra hne
    exact hpair (pair_eq_zero_of_isIrrChar_ne _ χ Ψ h hI fun e => hne fun x => congrFun e x)
  · exfalso
    choose m hm hm1 using fun i => irr_one (hψ i)
    obtain ⟨k, hk, hk1⟩ := irr_one hI
    have : ((k + ∏ i, m i : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hk1]
      simp [hΨ, hm1]
    have : k + ∏ i, m i = 0 := by exact_mod_cast this
    omega

end GlobalTheory
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_character_of_product : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by
  atlas_forward_decl GlobalTheory.irrChar_pi_eq_prod
end

section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI Formalism.L2.DIV GlobalTheory.FinGL

noncomputable section

namespace GlobalTheory.FinGL.LeviChar

variable {F : Type} [Field F] {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {d : ι → ℕ}

def diagHom (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) :
    (∀ a, GL (Fin (d a)) F) →* blockTri (κ := F) b :=
  MonoidHom.codRestrict (MonoidHom.toHomUnits
    { toFun := fun x => (Matrix.blockDiagonal' fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)).submatrix e.symm e.symm
      map_one' := by
        have : (fun a => ((1 : ∀ a, GL (Fin (d a)) F) a : Matrix (Fin (d a)) (Fin (d a)) F)) = 1 := rfl
        rw [this, Matrix.blockDiagonal'_one, Matrix.submatrix_one_equiv]
      map_mul' := fun x y => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        rfl }) _
    fun x i j hij => Matrix.blockDiagonal'_apply_ne
      (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm i).2 (e.symm j).2 fun e' => by
        have := (he _ _).2 e'
        rw [e.apply_symm_apply, e.apply_symm_apply] at this
        exact hij.ne' this

theorem diagHom_apply (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (x : ∀ a, GL (Fin (d a)) F) (p q : Σ a, Fin (d a)) :
    ((diagHom b e he x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e p) (e q) =
      Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) p q := by
  show Matrix.blockDiagonal' (fun a => (x a : Matrix (Fin (d a)) (Fin (d a)) F)) (e.symm (e p)) (e.symm (e q)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]

omit [Fintype ι] [DecidableEq ι] in

theorem exists_blocks (b : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    (p : blockTri (κ := F) b) : ∃ x : ∀ a, GL (Fin (d a)) F, ∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
  refine ⟨fun a => GlobalTheory.Parabolic.leviBlock b (fun i => e ⟨a, i⟩)
    (fun _ _ hij => sigma_mk_injective (β := fun a => Fin (d a)) (e.injective hij)) (fun i j hij => ?_)
    (GlobalTheory.Parabolic.leviProj b p), fun a i j => ?_⟩
  · obtain ⟨⟨c, l⟩, rfl⟩ := e.surjective j
    obtain rfl : a = c := (he _ _).1 hij
    exact ⟨l, rfl⟩
  · exact if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl)

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_eq {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (p : blockTri (κ := F) b)
    (x : ∀ a, GL (Fin (d a)) F) (hx : ∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩)) :
    σ p = σ (diagHom b e he x) := by
  obtain ⟨m, hm, hm'⟩ := IsCuspDatum.exists_blockDiag_act_eq F r V b σ hσ p
  rw [← hm]
  congr 1
  apply Subtype.ext
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨c, j⟩, rfl⟩ := e.surjective j
  rw [hm', diagHom_apply]
  by_cases hac : a = c
  · subst hac
    rw [Matrix.blockDiagonal'_apply_eq, if_pos ((he ⟨a, i⟩ ⟨a, j⟩).2 rfl), hx]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hac, if_neg (fun h => hac ((he _ _).1 h))]

theorem irr_comp {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) :
    Representation.IsIrreducible (σ.comp (diagHom b e he) : Representation ℂ (∀ a, GL (Fin (d a)) F) V) := by
  have hi := hσ.irr
  let φ : Subrepresentation (σ.comp (diagHom b e he) : Representation ℂ (∀ a, GL (Fin (d a)) F) V) ≃o
      Subrepresentation σ :=
    { toFun := fun W => ⟨W.toSubmodule, fun p v hv => by
        obtain ⟨x, hx⟩ := exists_blocks b e he p
        rw [act_eq e he hσ p x hx]
        exact W.apply_mem_toSubmodule x hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun x v hv => W.apply_mem_toSubmodule (diagHom b e he x) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact φ.isSimpleOrder_iff.2 hi

theorem sum_act_eq_zero {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r) (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1)
    {σ : Representation ℂ (blockTri (κ := F) b) V} (hσ : IsCuspDatum b σ) (c : ι) (a : ℕ) (h0 : 0 < a)
    (h1 : a < d c) (H : Subgroup (GL (Fin (d c)) F)) [Fintype H]
    (hH : (H : Set (GL (Fin (d c)) F)) = {u : GL (Fin (d c)) F | ∀ i j : Fin (d c),
      (u : Matrix (Fin (d c)) (Fin (d c)) F) i j = (if i = j then 1 else 0) ∨ (i.val < a ∧ a ≤ j.val)}) :
    ∑ u : H, σ (diagHom b e he (Pi.mulSingle c (u : GL (Fin (d c)) F))) = 0 := by
  ext v
  rw [LinearMap.sum_apply, LinearMap.zero_apply]
  refine hσ.cusp (Finset.univ.filter fun i => (e.symm i).1 = c ∧ (e.symm i).2.val < a)
    ⟨e ⟨c, ⟨0, h0.trans h1⟩⟩, e ⟨c, ⟨a, h1⟩⟩, (he _ _).2 rfl, ?_, ?_⟩ _ fun u hu => ?_
  · rw [Finset.mem_filter, e.symm_apply_apply]
    exact ⟨Finset.mem_univ _, rfl, h0⟩
  · rw [Finset.mem_filter, e.symm_apply_apply]
    exact fun h => lt_irrefl _ h.2.2
  obtain ⟨x, hx⟩ := exists_blocks b e he u
  have key : ∀ c' i j, (x c' : Matrix (Fin (d c')) (Fin (d c')) F) i j = (if i = j then 1 else 0) ∨
      (c' = c ∧ i.val < a ∧ a ≤ j.val) := by
    intro c' i j
    refine or_iff_not_imp_left.2 fun hne => ?_
    have h := hu (e ⟨c', i⟩) (e ⟨c', j⟩) (by
      rw [← hx, Matrix.one_apply]
      simpa using hne)
    rw [Finset.mem_filter, Finset.mem_filter, e.symm_apply_apply, e.symm_apply_apply] at h
    obtain ⟨-, ⟨-, h2, h3⟩, h4⟩ := h
    exact ⟨h2, h3, not_lt.1 fun h5 => h4 ⟨Finset.mem_univ _, h2, h5⟩⟩
  have hxc : x c ∈ H := by
    rw [← SetLike.mem_coe, hH]
    exact fun i j => (key c i j).imp id fun h => h.2
  have hx1 : x = Pi.mulSingle c (x c) := by
    funext c'
    by_cases hc : c' = c
    · subst hc
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hc]
      apply Units.ext
      ext i j
      rw [Units.val_one, Matrix.one_apply]
      exact (key c' i j).resolve_right fun h => hc h.1
  rw [act_eq e he hσ u x hx, hx1, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨x c, hxc⟩ : H)) _ _ fun w => ?_
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, ← Pi.mulSingle_mul]
  rfl

theorem irrChar_one_ne_zero {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : χ 1 ≠ 0 := by
  have hp := GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ h
  obtain ⟨n, ρ, -, hρ⟩ := h
  intro h1
  have hn : n = 0 := by
    rw [hρ] at h1
    simpa [Representation.character] using h1
  subst hn
  have : χ = 0 := by
    funext g
    rw [hρ, Representation.character, Subsingleton.elim (ρ g) 0]
    simp
  rw [this] at hp
  simp [pair] at hp

theorem exists_prod [Finite F] {b : Fin r → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin r)
    (he : ∀ x y, b (e x) = b (e y) ↔ x.1 = y.1) {n : ℕ}
    {σ : Representation ℂ (blockTri (κ := F) b) (Fin n → ℂ)} (hσ : IsCuspDatum b σ) :
    ∃ ψ : ∀ a, GL (Fin (d a)) F → ℂ, (∀ a, IsIrrChar ℂ ℂ (ψ a) ∧ IsPrimitive (extZero (ψ a))) ∧
      ∀ (p : blockTri (κ := F) b) (x : ∀ a, GL (Fin (d a)) F), (∀ a i j, (x a : Matrix (Fin (d a)) (Fin (d a)) F) i j =
      ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) (e ⟨a, i⟩) (e ⟨a, j⟩)) → σ.character p = ∏ a, ψ a (x a) := by
  obtain ⟨ψ, hψ, hprod⟩ := GlobalTheory.T.irreducible_character_of_product ι (fun a => GL (Fin (d a)) F) (fun x => σ.character (diagHom b e he x))
    ⟨n, σ.comp (diagHom b e he), irr_comp e he hσ, fun _ => rfl⟩
  refine ⟨ψ, fun c => ⟨hψ c, ?_⟩, fun p x hx => ?_⟩
  · refine isPrimitive_extZero_of_sum_unipotent F _ _ ?_ fun a h0 h1 => ?_
    · obtain ⟨m, ρ, -, hρ⟩ := hψ c
      exact ⟨m, ρ, hρ⟩
    obtain ⟨-, H, -, hH, -⟩ := GlobalTheory.T.exists_standardUnipotentRadical_bijOn_nilradical F (d c) a h1.le
    letI : Fintype H := Fintype.ofFinite H
    have hs := congrArg (LinearMap.trace ℂ (Fin n → ℂ)) (sum_act_eq_zero e he hσ c a h0 h1 H hH)
    rw [map_sum, map_zero] at hs
    have hv : ∀ u : GL (Fin (d c)) F, LinearMap.trace ℂ (Fin n → ℂ) (σ (diagHom b e he (Pi.mulSingle c u))) =
        ψ c u * ∏ c' ∈ Finset.univ.erase c, ψ c' 1 := by
      intro u
      refine (hprod _).trans ?_
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), Pi.mulSingle_eq_same]
      congr 1
      refine Finset.prod_congr rfl fun c' hc' => ?_
      rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hc')]
    simp only [hv] at hs
    rw [← Finset.sum_mul] at hs
    have hs' := (mul_eq_zero.1 hs).resolve_right
      (Finset.prod_ne_zero_iff.2 fun c' _ => irrChar_one_ne_zero (hψ c'))
    rw [← hH, ← finsum_set_coe_eq_finsum_mem (f := ψ c) (H : Set (GL (Fin (d c)) F))]
    exact (finsum_eq_sum_of_fintype (fun u : H => ψ c u)).trans hs'
  · rw [← hprod x, Representation.character, act_eq e he hσ p x hx]
    rfl


end GlobalTheory.FinGL.LeviChar
end
end
