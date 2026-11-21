import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldFormula

section
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

noncomputable local instance fintypeResidue'' : Fintype 𝓀[F] := Fintype.ofFinite _

theorem addChar_sum_eq_prod {ι : Type*} (ψ₀ : AddChar F ℂ) (s : Finset ι) (f : ι → F) :
    ψ₀ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ₀ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem inv_mul_mem_of_mem_maximalIdeal {y : 𝒪[F]} (hy : y ∈ IsLocalRing.maximalIdeal 𝒪[F]) :
    π⁻¹ * (y : F) ∈ 𝒪[F] := by
  refine mem_of_bdd ?_
  have h := (bdd_zpow (F := F) (-1)).mul (bdd_one_of_mem_maximalIdeal hy)
  rwa [_root_.zpow_neg_one, neg_add_cancel] at h

def residueChar (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) : AddChar 𝓀[F] ℂ where
  toFun x := ψ₀ (π⁻¹ * (residueLift F x : F))
  map_zero_eq_one' := by
    refine hψ₀ _ (inv_mul_mem_of_mem_maximalIdeal ?_)
    rw [← IsLocalRing.residue_eq_zero_iff, residue_residueLift]
  map_add_eq_mul' x y := by
    have hm : residueLift F (x + y) - (residueLift F x + residueLift F y) ∈
        IsLocalRing.maximalIdeal 𝒪[F] := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_add, residue_residueLift,
        residue_residueLift, residue_residueLift, sub_self]
    have h1 := hψ₀ _ (inv_mul_mem_of_mem_maximalIdeal hm)
    rw [← AddChar.map_add_eq_mul, ← mul_add]
    have : π⁻¹ * ((residueLift F (x + y) : 𝒪[F]) : F) =
        π⁻¹ * (((residueLift F x + residueLift F y : 𝒪[F])) : F) +
          π⁻¹ * ((residueLift F (x + y) - (residueLift F x + residueLift F y) : 𝒪[F]) : F) := by
      push_cast
      ring
    rw [this, AddChar.map_add_eq_mul, h1, mul_one]
    push_cast
    rfl

theorem residueChar_ne_one (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) : residueChar ψ₀ hψ₀ ≠ 1 := by
  obtain ⟨y, hy, hψy⟩ := hψ₁
  intro h
  have h1 := congrArg (fun φ : AddChar 𝓀[F] ℂ => φ (IsLocalRing.residue 𝒪[F] ⟨π * y, hy⟩)) h
  simp only [AddChar.one_apply] at h1
  have hm := residueLift_sub_mem (F := F) ⟨π * y, hy⟩
  have h2 := hψ₀ _ (inv_mul_mem_of_mem_maximalIdeal hm)
  have hπ : π ≠ 0 := uniformizer_ne_zero F
  have : π⁻¹ * ((residueLift F (IsLocalRing.residue 𝒪[F] ⟨π * y, hy⟩) : 𝒪[F]) : F) =
      y + π⁻¹ * ((residueLift F (IsLocalRing.residue 𝒪[F] ⟨π * y, hy⟩) -
        ⟨π * y, hy⟩ : 𝒪[F]) : F) := by
    push_cast
    field_simp
    ring
  change ψ₀ (π⁻¹ * ((residueLift F (IsLocalRing.residue 𝒪[F] ⟨π * y, hy⟩) : 𝒪[F]) : F)) = 1 at h1
  rw [this, AddChar.map_add_eq_mul, h2, mul_one] at h1
  exact hψy h1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem superdiagSum_mem {M : Matrix (Fin n) (Fin n) F}
    (h : ∀ i j : Fin n, (j : ℕ) = i + 1 → M i j ∈ 𝒪[F]) : Whittaker.superdiagSum M ∈ 𝒪[F] := by
  refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
  split_ifs with hij
  · exact h i j hij
  · exact Subring.zero_mem _

theorem psiN_conj_eq_one {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) {l : Fin n → ℤ}
    (hl : Antitone l) {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    Whittaker.psiN ψ₀ (torusPow F n l * k * torusPow F n (-l)) = 1 := by
  refine hψ₀ _ (superdiagSum_mem fun i j hij => ?_)
  rw [torusPow_mul_mul_neg_apply]
  refine Subring.mul_mem _ (zpow_mem_of_nonneg ?_) (((mem_integralGL_iff F n).1 hk).1 i j)
  have := hl (show i ≤ j from Fin.le_def.2 (by omega))
  linarith

theorem exists_iwasawa_decomp (g : GL (Fin n) F) :
    ∃ p : GL (Fin n) F × GL (Fin n) F, p.1 ∈ unipotent F n ∧ p.2 ∈ integralGL F n ∧
      g = p.1 * torusPow F n (iwasawaExponent F n g) * p.2 := by
  obtain ⟨u, hu, k, hk, h⟩ := exists_eq_mul_torusPow_iwasawaExponent F n g
  exact ⟨(u, k), hu, hk, h⟩

def iwasawaUnip (g : GL (Fin n) F) : GL (Fin n) F := (exists_iwasawa_decomp g).choose.1

def iwasawaInt (g : GL (Fin n) F) : GL (Fin n) F := (exists_iwasawa_decomp g).choose.2

theorem iwasawaUnip_mem (g : GL (Fin n) F) : iwasawaUnip g ∈ unipotent F n :=
  (exists_iwasawa_decomp g).choose_spec.1

theorem iwasawaInt_mem (g : GL (Fin n) F) : iwasawaInt g ∈ integralGL F n :=
  (exists_iwasawa_decomp g).choose_spec.2.1

theorem eq_iwasawa (g : GL (Fin n) F) :
    g = iwasawaUnip g * torusPow F n (iwasawaExponent F n g) * iwasawaInt g :=
  (exists_iwasawa_decomp g).choose_spec.2.2

variable (ψ₀ : AddChar F ℂ) (z : Fin n → ℂˣ) in

def sphericalWhittaker (g : GL (Fin n) F) : ℂ :=
  if Antitone (iwasawaExponent F n g) then
    Whittaker.psiN ψ₀ (iwasawaUnip g) * halfModulus F (iwasawaExponent F n g) *
      evalAt z (schur (iwasawaExponent F n g))
  else 0

theorem sphericalWhittaker_apply {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) {u k : GL (Fin n) F} (hu : u ∈ unipotent F n) (hk : k ∈ integralGL F n)
    (l : Fin n → ℤ) :
    sphericalWhittaker ψ₀ z (u * torusPow F n l * k) =
      if Antitone l then Whittaker.psiN ψ₀ u * halfModulus F l * evalAt z (schur l) else 0 := by
  have hexp : iwasawaExponent F n (u * torusPow F n l * k) = l := iwasawaExponent_eq F n hu hk
  have hu' := iwasawaUnip_mem (u * torusPow F n l * k)
  have hk' := iwasawaInt_mem (u * torusPow F n l * k)
  have heq := eq_iwasawa (u * torusPow F n l * k)
  set u' := iwasawaUnip (u * torusPow F n l * k)
  set k' := iwasawaInt (u * torusPow F n l * k)
  rw [sphericalWhittaker, hexp]
  split_ifs with hl
  swap
  · rfl
  rw [hexp] at heq

  have hv : u⁻¹ * u' = torusPow F n l * (k * k'⁻¹) * torusPow F n (-l) := by
    rw [torusPow_neg]
    have := congrArg (fun g => u⁻¹ * g * k'⁻¹ * (torusPow F n l)⁻¹) heq
    rw [show u⁻¹ * (u * torusPow F n l * k) * k'⁻¹ * (torusPow F n l)⁻¹ =
      torusPow F n l * (k * k'⁻¹) * (torusPow F n l)⁻¹ by group,
      show u⁻¹ * (u' * torusPow F n l * k') * k'⁻¹ * (torusPow F n l)⁻¹ = u⁻¹ * u' by group] at this
    exact this.symm
  have h1 : Whittaker.psiN ψ₀ (u⁻¹ * u') = 1 := by
    rw [hv]
    exact psiN_conj_eq_one hψ₀ hl (mul_mem hk ((integralGL F n).inv_mem hk'))
  have h2 : u' = u * (u⁻¹ * u') := by group
  change Whittaker.psiN ψ₀ u' * halfModulus F l * evalAt z (schur l) = _
  rw [h2, Whittaker.psiN_mul ψ₀ hu ((unipotent F n).mul_mem ((unipotent F n).inv_mem hu) hu'), h1,
    mul_one]

theorem sphericalWhittaker_mul_left {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) {v : GL (Fin n) F} (hv : v ∈ unipotent F n) (g : GL (Fin n) F) :
    sphericalWhittaker ψ₀ z (v * g) = Whittaker.psiN ψ₀ v * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, show v * (iwasawaUnip g * torusPow F n (iwasawaExponent F n g) * iwasawaInt g) =
    (v * iwasawaUnip g) * torusPow F n (iwasawaExponent F n g) * iwasawaInt g by group,
    sphericalWhittaker_apply hψ₀ z ((unipotent F n).mul_mem hv hu) hk,
    sphericalWhittaker_apply hψ₀ z hu hk, Whittaker.psiN_mul ψ₀ hv hu]
  split_ifs <;> ring

theorem sphericalWhittaker_mul_right {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (g : GL (Fin n) F) {k₀ : GL (Fin n) F} (hk₀ : k₀ ∈ integralGL F n) :
    sphericalWhittaker ψ₀ z (g * k₀) = sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, mul_assoc, sphericalWhittaker_apply hψ₀ z hu (mul_mem hk hk₀),
    sphericalWhittaker_apply hψ₀ z hu hk]

theorem sphericalWhittaker_torusPow {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (l : Fin n → ℤ) :
    sphericalWhittaker ψ₀ z (torusPow F n l) =
      if Antitone l then halfModulus F l * evalAt z (schur l) else 0 := by
  have := sphericalWhittaker_apply hψ₀ z (unipotent F n).one_mem (integralGL F n).one_mem l
  rw [one_mul, mul_one, Whittaker.psiN_one, one_mul] at this
  exact this

theorem sphericalWhittaker_one {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) : sphericalWhittaker ψ₀ z (1 : GL (Fin n) F) = 1 := by
  have := sphericalWhittaker_torusPow hψ₀ z (0 : Fin n → ℤ)
  rw [torusPow_zero, if_pos (show Antitone (0 : Fin n → ℤ) from fun _ _ _ => le_rfl),
    halfModulus_zero, schur_zero, map_one, mul_one] at this
  exact this

theorem psiN_conj_unipC (ψ₀ : AddChar F ℂ) (l : Fin n → ℤ) (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) :
    Whittaker.psiN ψ₀ (torusPow F n l * unipC S c * torusPow F n (-l)) =
      ∏ p : Pairs S, if (p.1.2 : ℕ) = p.1.1 + 1 then
        ψ₀ (π ^ (l p.1.1 - l p.1.2) * ((residueLift F (c p) : 𝒪[F]) : F)) else 1 := by
  classical
  set T : Fin n × Fin n → F := fun q => if (q.2 : ℕ) = q.1 + 1 then
    π ^ (l q.1 - l q.2) * cMat S c q.1 q.2 else 0 with hT
  have h1 : Whittaker.superdiagSum
      ((torusPow F n l * unipC S c * torusPow F n (-l) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ∑ q : Fin n × Fin n, T q := by
    rw [Whittaker.superdiagSum, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hT]
    split_ifs with h
    · rw [torusPow_mul_mul_neg_apply, coe_unipC, Matrix.add_apply,
        Matrix.one_apply_ne (fun h' => by rw [h'] at h; omega), zero_add]
    · rfl
  have h2 : ∑ q : Fin n × Fin n, T q = ∑ p : Pairs S, T p.1 := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun q : Fin n × Fin n => q.1 ∈ S ∧ q.2 ∉ S ∧ q.1 < q.2) T]
    have : ∑ q : {q : Fin n × Fin n // ¬(q.1 ∈ S ∧ q.2 ∉ S ∧ q.1 < q.2)}, T q = 0 := by
      refine Finset.sum_eq_zero fun q _ => ?_
      simp only [hT, cMat_apply_of_not c q.2, mul_zero, ite_self]
    rw [this, add_zero]
    rfl
  rw [Whittaker.psiN, h1, h2, addChar_sum_eq_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp only [hT]
  split_ifs with h
  · congr 2
    exact dif_pos p.2
  · exact AddChar.map_zero_eq_one ψ₀

theorem sum_psiN_conj_unipC_eq_zero {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) {l : Fin n → ℤ} {S : Finset (Fin n)} {i j : Fin n}
    (hij : (j : ℕ) = i + 1) (hi : i ∈ S) (hj : j ∉ S) (hl : l j = l i + 1) :
    ∑ c : Pairs S → 𝓀[F], Whittaker.psiN ψ₀ (torusPow F n l * unipC S c * torusPow F n (-l)) = 0 := by
  classical
  set G : Pairs S → 𝓀[F] → ℂ := fun p x => if (p.1.2 : ℕ) = p.1.1 + 1 then
    ψ₀ (π ^ (l p.1.1 - l p.1.2) * ((residueLift F x : 𝒪[F]) : F)) else 1 with hG
  have key := Finset.prod_univ_sum (fun _ : Pairs S => (Finset.univ : Finset 𝓀[F])) G
  rw [Fintype.piFinset_univ] at key
  have hlt : i < j := Fin.lt_def.2 (by omega)
  have hzero : ∑ c : Pairs S → 𝓀[F], ∏ p, G p (c p) = 0 := by
    rw [← key]
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨(i, j), hi, hj, hlt⟩ : Pairs S)) ?_
    simp only [hG, if_pos hij]
    rw [show l i - l j = -1 by omega, _root_.zpow_neg_one]
    exact AddChar.sum_eq_zero_of_ne_one (residueChar_ne_one ψ₀ hψ₀ hψ₁)
  calc _ = ∑ c : Pairs S → 𝓀[F], ∏ p, G p (c p) :=
        Finset.sum_congr rfl fun c _ => psiN_conj_unipC ψ₀ l S c
    _ = 0 := hzero

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem integral_hecke_mul_left (h : SphericalHecke μ (F := F) (n := n)) (f : GL (Fin n) F → ℂ)
    {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    ∫ x, (h : HeckeAlgebra μ) x * f (k * x) ∂μ = ∫ x, (h : HeckeAlgebra μ) x * f x ∂μ := by
  have := integral_mul_left_eq_self (μ := μ)
    (fun y => (h : HeckeAlgebra μ) (k⁻¹ * y) * f y) k
  simp only [inv_mul_cancel_left] at this
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [HeckeAlgebraLevel.apply_mul_left _ _ h ((integralGL F n).inv_mem hk)]

theorem sphericalWhittaker_torusPow_add_lamS {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) {l : Fin n → ℤ} (hl : Antitone l) (S : Finset (Fin n)) :
    sphericalWhittaker ψ₀ z (torusPow F n (l + lamS S)) =
      halfModulus F (l + lamS S) * evalAt z (schur (l + lamS S)) := by
  rw [sphericalWhittaker_torusPow hψ₀]
  split_ifs with h
  · rfl
  · obtain ⟨i, j, hij, hlij, hiS, hjS⟩ := exists_ascent hl h
    have hasc : (l + lamS S) j = (l + lamS S) i + 1 := by
      simp only [Pi.add_apply, lamS_apply, hiS, hjS, if_true, if_false, hlij]
      ring
    rw [schur_eq_zero_of_ascent hij hasc, map_zero, mul_zero]

theorem integral_minusculeHecke_mul_sphericalWhittaker_torusPow {ψ₀ : AddChar F ℂ}
    (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    {r : ℕ} (hr : r ≤ n) (l : Fin n → ℤ) :
    ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (torusPow F n l * x) ∂μ =
      evalAt z (satakeTransform μ (minusculeHecke μ r)) * sphericalWhittaker ψ₀ z (torusPow F n l) := by
  rw [integral_minusculeHecke_mul (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk),
    evalAt_satakeTransform_minusculeHecke z hr]
  have hterm : ∀ S : Finset (Fin n), ∑ c : Pairs S → 𝓀[F],
      sphericalWhittaker ψ₀ z (torusPow F n l * gMat S c) =
      (∑ c : Pairs S → 𝓀[F], Whittaker.psiN ψ₀ (torusPow F n l * unipC S c * torusPow F n (-l))) *
        sphericalWhittaker ψ₀ z (torusPow F n (l + lamS S)) := by
    intro S
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hN : torusPow F n l * unipC S c * torusPow F n (-l) ∈ unipotent F n := by
      rw [torusPow_neg, torusPow]
      exact diagGL_mul_mul_inv_mem_unipotent F n (unipC_mem_unipotent S c) _
    rw [torusPow_mul_gMat, sphericalWhittaker_mul_left hψ₀ z hN]
  simp only [hterm]
  by_cases hl : Antitone l
  · have hone : ∀ S : Finset (Fin n), ∑ c : Pairs S → 𝓀[F],
        Whittaker.psiN ψ₀ (torusPow F n l * unipC S c * torusPow F n (-l)) = (kappa F S : ℂ) := by
      intro S
      rw [Finset.sum_congr rfl fun c _ => psiN_eq_one_of_mem hψ₀ (torusPow_conj_unipC_mem hl S c),
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, kappa, Nat.card_eq_fintype_card]
    simp only [hone, sphericalWhittaker_torusPow_add_lamS hψ₀ z hl]
    rw [← halfModulus_mul_recursion schur (fun r l => esymmL_mul_schur r l) z hr l,
      sphericalWhittaker_torusPow hψ₀, if_pos hl]
    ring
  · rw [sphericalWhittaker_torusPow hψ₀, if_neg hl, mul_zero]
    rw [Finset.sum_eq_zero, mul_zero]
    intro S _
    by_cases hant : Antitone (l + lamS S)
    · obtain ⟨i, j, hij, hlt⟩ := exists_lt_succ_of_not_antitone hl
      have hle : (l + lamS S) j ≤ (l + lamS S) i := hant (Fin.le_def.2 (by omega))
      simp only [Pi.add_apply, lamS_apply] at hle
      have hiS : i ∈ S := by
        by_contra h
        rw [if_neg h] at hle
        split_ifs at hle <;> omega
      have hjS : j ∉ S := by
        intro h
        rw [if_pos h, if_pos hiS] at hle
        omega
      have hlj : l j = l i + 1 := by
        rw [if_pos hiS, if_neg hjS] at hle
        omega
      rw [sum_psiN_conj_unipC_eq_zero hψ₀ hψ₁ hij hiS hjS hlj, zero_mul]
    · rw [sphericalWhittaker_torusPow hψ₀, if_neg hant, mul_zero]

theorem integral_minusculeHecke_mul_sphericalWhittaker {ψ₀ : AddChar F ℂ}
    (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    {r : ℕ} (hr : r ≤ n) (g : GL (Fin n) F) :
    ∫ x, (minusculeHecke μ r : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x) ∂μ =
      evalAt z (satakeTransform μ (minusculeHecke μ r)) * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  set u := iwasawaUnip g
  set e := iwasawaExponent F n g
  set k := iwasawaInt g
  have hu : u ∈ unipotent F n := iwasawaUnip_mem g
  have hk : k ∈ integralGL F n := iwasawaInt_mem g
  have h1 : ∀ x, sphericalWhittaker ψ₀ z (g * x) =
      Whittaker.psiN ψ₀ u * sphericalWhittaker ψ₀ z (torusPow F n e * (k * x)) := by
    intro x
    rw [← sphericalWhittaker_mul_left hψ₀ z hu]
    congr 1
    rw [hg]
    group
  simp only [h1]
  rw [show (fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * (Whittaker.psiN ψ₀ u *
      sphericalWhittaker ψ₀ z (torusPow F n e * (k * x)))) = fun x => Whittaker.psiN ψ₀ u *
      ((minusculeHecke μ r : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (torusPow F n e * (k * x)))
      by funext x; ring, integral_const_mul,
    integral_hecke_mul_left (minusculeHecke μ r) (fun y => sphericalWhittaker ψ₀ z (torusPow F n e * y)) hk,
    integral_minusculeHecke_mul_sphericalWhittaker_torusPow hψ₀ hψ₁ z hr e]
  conv_rhs => rw [hg, sphericalWhittaker_mul_right hψ₀ z _ hk, sphericalWhittaker_mul_left hψ₀ z hu]
  ring

end Spherical

end GroundTheory.Automorphic
end
end

section
noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

local notation "π" => (GLnLocal.uniformizer F : F)

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem integrable_hecke_mul {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (h : SphericalHecke μ (F := F) (n := n))
    (g : GL (Fin n) F) :
    Integrable (fun x => (h : HeckeAlgebra μ) x * f (g * x)) μ := by
  refine Continuous.integrable_of_hasCompactSupport ?_ (h : HeckeAlgebra μ).mem.2.mul_right
  exact (h : HeckeAlgebra μ).mem.1.continuous.mul
    ((continuous_of_mul_right_invariant hf).comp (continuous_mul_left g))

theorem integral_one_mul {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) (g : GL (Fin n) F) :
    ∫ x, ((1 : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x) ∂μ = f g := by
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have : (fun x => ((1 : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x)) =
      (integralGL F n : Set (GL (Fin n) F)).indicator
        (fun _ => (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ)⁻¹ * f g) := by
    funext x
    rw [HeckeAlgebraLevel.val_one, idem_apply]
    by_cases hx : x ∈ integralGL F n
    · rw [Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_mem (show x ∈ (integralGL F n : Set (GL (Fin n) F)) from hx), hf g x hx]
    · rw [Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx),
        Set.indicator_of_notMem (show x ∉ (integralGL F n : Set (GL (Fin n) F)) from hx), zero_mul]
  rw [this, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, ← mul_assoc, mul_inv_cancel₀ hK, one_mul]

theorem integral_mul_mul_eigen (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) {h₁ h₂ : SphericalHecke μ (F := F) (n := n)}
    (hh₁ : ∀ g, ∫ x, (h₁ : HeckeAlgebra μ) x * f (g * x) ∂μ = evalAt z (satakeTransform μ h₁) * f g)
    (hh₂ : ∀ g, ∫ x, (h₂ : HeckeAlgebra μ) x * f (g * x) ∂μ = evalAt z (satakeTransform μ h₂) * f g)
    (g : GL (Fin n) F) :
    ∫ x, ((h₁ * h₂ : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x * f (g * x) ∂μ =
      evalAt z (satakeTransform μ (h₁ * h₂)) * f g := by
  rw [map_mul, map_mul]
  have hconv : ∀ x, (((h₁ * h₂ : SphericalHecke μ (F := F) (n := n)) : HeckeAlgebra μ) x) =
      ∫ y, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) ∂μ := by
    intro x
    rw [HeckeAlgebraLevel.val_mul, HeckeAlgebra.coe_mul]
    rfl
  simp only [hconv, ← integral_mul_const]
  set B := tsupport ((h₁ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)
  set C := tsupport ((h₂ : HeckeAlgebra μ) : GL (Fin n) F → ℂ)
  have hB : IsCompact B := (h₁ : HeckeAlgebra μ).mem.2
  have hC : IsCompact C := (h₂ : HeckeAlgebra μ).mem.2
  have hswap := integral_integral_swap_of_coset μ (integralOpen F n) (isCompact_integralGL F n)
    (hB.mul hC) hB (F := fun x y => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) *
      f (g * x))
    (by
      intro x y hxy
      have hy : y ∈ B := subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul hxy))
      have hx : y⁻¹ * x ∈ C := subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul hxy))
      exact ⟨Set.mem_mul.2 ⟨y, hy, y⁻¹ * x, hx, by group⟩, hy⟩)
    (by
      intro x y k hk
      rw [← mul_assoc, (HeckeAlgebraLevel.val_mem _ _ h₂ k hk _).2, ← mul_assoc, hf _ k hk])
    (by
      intro x y k hk
      rw [(HeckeAlgebraLevel.val_mem _ _ h₁ k hk y).2, _root_.mul_inv_rev,
        show k⁻¹ * y⁻¹ * x = k⁻¹ * (y⁻¹ * x) from mul_assoc _ _ _,
        HeckeAlgebraLevel.apply_mul_left _ _ h₂ ((integralGL F n).inv_mem hk)])
  rw [hswap]
  have hinner : ∀ y, ∫ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x) ∂μ =
      (h₁ : HeckeAlgebra μ) y * f (g * y) * evalAt z (satakeTransform μ h₂) := by
    intro y
    have e := integral_mul_left_eq_self (μ := μ)
      (fun x => (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) (y⁻¹ * x) * f (g * x)) y
    simp only [inv_mul_cancel_left] at e
    rw [← e]
    have hpt : ∀ x, (h₁ : HeckeAlgebra μ) y * (h₂ : HeckeAlgebra μ) x * f (g * (y * x)) =
        (h₁ : HeckeAlgebra μ) y * ((h₂ : HeckeAlgebra μ) x * f ((g * y) * x)) := by
      intro x
      rw [mul_assoc g y x]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hh₂ (g * y)]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), integral_mul_const, hh₁ g]
  ring

variable (μ) in

def eigenSubalgebra (z : Fin n → ℂˣ) (f : GL (Fin n) F → ℂ)
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g) :
    Subalgebra ℂ (SphericalHecke μ (F := F) (n := n)) where
  carrier := {h | ∀ g, ∫ x, (h : HeckeAlgebra μ) x * f (g * x) ∂μ =
    evalAt z (satakeTransform μ h) * f g}
  mul_mem' {h₁ h₂} hh₁ hh₂ g := integral_mul_mul_eigen z hf hh₁ hh₂ g
  one_mem' g := by
    simp only [Set.mem_setOf_eq, map_one, one_mul]
    exact integral_one_mul hf g
  add_mem' {h₁ h₂} hh₁ hh₂ g := by
    simp only [HeckeAlgebraLevel.val_add, HeckeAlgebra.coe_add, Pi.add_apply, add_mul]
    rw [integral_add (integrable_hecke_mul hf h₁ g) (integrable_hecke_mul hf h₂ g), hh₁, hh₂,
      map_add, map_add, add_mul]
  zero_mem' g := by
    simp [HeckeAlgebraLevel.val_zero]
  algebraMap_mem' c g := by
    rw [Algebra.algebraMap_eq_smul_one, HeckeAlgebraLevel.val_smul, HeckeAlgebra.coe_smul, map_smul,
      map_smul, smul_eq_mul, map_one, map_one, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_one_mul hf g]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem polyEmb_esymm (k : ℕ) : polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) = esymmL n k := by
  rw [MvPolynomial.esymm, map_sum, esymmL]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_prod]
  simp only [polyEmb_X, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one, sum_single_one]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem esymmL_eq_zero {k : ℕ} (hk : n < k) : esymmL n k = 0 := by
  rw [esymmL, Finset.powersetCard_eq_empty.2 (by simpa using hk), Finset.sum_empty]

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in
theorem sum_rho_coeff : ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (n : ℤ) - 1 - 2 * (i : ℤ)) n, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
  have h := Finset.sum_range_id_mul_two n
  have h' : (∑ i ∈ Finset.range n, (i : ℤ)) * 2 = (n : ℤ) * ((n : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have : (((∑ i ∈ Finset.range n, i) * 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by rw [h]
      push_cast [Nat.cast_sub hn] at this
      linarith
  simp only [nsmul_eq_mul]
  linarith

omit [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] in

theorem halfModulus_const (c : ℤ) : halfModulus F (fun _ : Fin n => c) = 1 := by
  rw [halfModulus_eq, rhoPair]
  simp only [mul_comm _ c, ← Finset.mul_sum, sum_rho_coeff, mul_zero, neg_zero, zpow_zero]

theorem satakeTransform_minusculeHecke {k : ℕ} (hk : k ≤ n) :
    satakeTransform μ (minusculeHecke μ k) =
      ((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k))) • esymmL n k := by
  refine eq_of_forall_evalAt fun w => ?_
  rw [evalAt_satakeTransform_minusculeHecke w hk, map_smul, smul_eq_mul]

theorem satakeTransform_centralHecke :
    satakeTransform μ (centralHecke μ) =
      (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) • monomial (fun _ : Fin n => (-1 : ℤ)) := by
  rw [satakeTransform_apply, satake_centralHecke, map_smul, monomial, normalize_single,
    halfModulus_const, one_mul]

theorem eigenSubalgebra_eq_top (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hf : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hT : ∀ r ≤ n, minusculeHecke μ r ∈ eigenSubalgebra μ z f hf)
    (hc : centralHecke μ ∈ eigenSubalgebra μ z f hf) : eigenSubalgebra μ z f hf = ⊤ := by
  set E := eigenSubalgebra μ z f hf
  set A := E.map (satakeTransform μ)
  have hK : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)).ne'
  have h1 : ∀ k, polyEmb n (MvPolynomial.esymm (Fin n) ℂ k) ∈ A := by
    intro k
    rw [polyEmb_esymm]
    by_cases hk : k ≤ n
    · have hc' : (μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) * sqrtQ F ^ (k * (n - k)) ≠ 0 :=
        mul_ne_zero hK (pow_ne_zero _ sqrtQ_ne_zero)
      refine Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ) *
        sqrtQ F ^ (k * (n - k)))⁻¹ • minusculeHecke μ k, E.smul_mem (hT k hk) _, ?_⟩
      rw [map_smul, satakeTransform_minusculeHecke hk, smul_smul, inv_mul_cancel₀ hc', one_smul]
    · rw [esymmL_eq_zero (by omega)]
      exact A.zero_mem
  have h2 : monomial (fun _ : Fin n => (-1 : ℤ)) ∈ A := by
    refine Subalgebra.mem_map.2 ⟨((μ.real (integralGL F n : Set (GL (Fin n) F)) : ℂ))⁻¹ •
      centralHecke μ, E.smul_mem hc _, ?_⟩
    rw [map_smul, satakeTransform_centralHecke, smul_smul, inv_mul_cancel₀ hK, one_smul]
  have hsym := symmetricLaurent_le h1 h2
  rw [Algebra.eq_top_iff]
  intro h
  obtain ⟨e, he, hSe⟩ := Subalgebra.mem_map.1 (hsym (satakeTransform_mem_symmetric h))
  rwa [← satakeTransform_injective hSe]

theorem antitone_add_const_iff (l : Fin n → ℤ) (c : ℤ) :
    Antitone (l + fun _ => c) ↔ Antitone l := by
  constructor
  · intro h i j hij
    have := h hij
    simp only [Pi.add_apply] at this
    linarith
  · intro h i j hij
    simp only [Pi.add_apply]
    linarith [h hij]

theorem schur_add_const (l : Fin n → ℤ) (c : ℤ) :
    schur (l + fun _ => c) = monomial (fun _ : Fin n => c) * schur l := by
  rw [schur, schur, show l + (fun _ => c) + staircase n = (fun _ => c) + (l + staircase n) by abel,
    monomial_add, altQuot_mul_of_symm (permAct_monomial_const c)]

theorem sphericalWhittaker_mul_const {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (z : Fin n → ℂˣ) (g : GL (Fin n) F) (c : ℤ) :
    sphericalWhittaker ψ₀ z (g * torusPow F n (fun _ => c)) =
      monomialChar (fun _ : Fin n => c) z * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  set u := iwasawaUnip g
  set e := iwasawaExponent F n g
  set k := iwasawaInt g
  have : g * torusPow F n (fun _ => c) = u * torusPow F n (e + fun _ => c) * k := by
    rw [hg, torusPow_add, mul_assoc, ← torusPow_const_comm c k]
    group
  rw [this, sphericalWhittaker_apply hψ₀ z hu hk, hg, sphericalWhittaker_apply hψ₀ z hu hk]
  by_cases he : Antitone e
  · rw [if_pos ((antitone_add_const_iff e c).2 he), if_pos he, halfModulus_add, halfModulus_const,
      schur_add_const, map_mul, monomial, evalAt_single, one_mul]
    ring
  · rw [if_neg (fun h => he ((antitone_add_const_iff e c).1 h)), if_neg he, mul_zero]

theorem integral_centralHecke_mul_sphericalWhittaker {ψ₀ : AddChar F ℂ}
    (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1) (z : Fin n → ℂˣ) (g : GL (Fin n) F) :
    ∫ x, (centralHecke μ : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x) ∂μ =
      evalAt z (satakeTransform μ (centralHecke μ)) * sphericalWhittaker ψ₀ z g := by
  set g₀ := torusPow F n (fun _ : Fin n => (-1 : ℤ))
  have e := integral_mul_left_eq_self (μ := μ)
    (fun x => (centralHecke μ : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x)) g₀
  rw [← e]
  have hpt : (fun y => (centralHecke μ : HeckeAlgebra μ) (g₀ * y) *
      sphericalWhittaker ψ₀ z (g * (g₀ * y))) = (integralGL F n : Set (GL (Fin n) F)).indicator
        (fun _ => sphericalWhittaker ψ₀ z (g * g₀)) := by
    funext y
    rw [centralHecke_apply]
    by_cases hy : y ∈ integralGL F n
    · have hm : g₀ * y ∈ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem (show y ∈ (integralGL F n : Set (GL (Fin n) F))
        from hy), one_mul, ← mul_assoc, sphericalWhittaker_mul_right hψ₀ z _ hy]
    · have hm : g₀ * y ∉ centralSet F n := by
        rw [mem_centralSet, inv_mul_cancel_left]
        exact hy
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (show y ∉ (integralGL F n :
        Set (GL (Fin n) F)) from hy), zero_mul]
  rw [hpt, integral_indicator (isOpen_integralGL F n).measurableSet, setIntegral_const,
    Complex.real_smul, sphericalWhittaker_mul_const hψ₀, satakeTransform_centralHecke, map_smul,
    monomial, evalAt_single, one_mul, smul_eq_mul]
  ring

theorem integral_mul_sphericalWhittaker {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F) :
    ∫ x, (h : HeckeAlgebra μ) x * sphericalWhittaker ψ₀ z (g * x) ∂μ =
      evalAt z (satakeTransform μ h) * sphericalWhittaker ψ₀ z g := by
  have htop := eigenSubalgebra_eq_top (μ := μ) z
    (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk)
    (fun r hr g => integral_minusculeHecke_mul_sphericalWhittaker hψ₀ hψ₁ z hr g)
    (fun g => integral_centralHecke_mul_sphericalWhittaker hψ₀ z g)
  have hmem : h ∈ eigenSubalgebra μ z (sphericalWhittaker ψ₀ z)
      (fun g k hk => sphericalWhittaker_mul_right hψ₀ z g hk) := by
    rw [htop]
    exact Algebra.mem_top
  exact hmem g

theorem eq_smul_sphericalWhittaker {ψ₀ : AddChar F ℂ} (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, π * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ) {W : GL (Fin n) F → ℂ}
    (hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g)
    (hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g)
    (heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * W (g * x) ∂μ = evalAt z (satakeTransform μ h) * W g)
    (g : GL (Fin n) F) : W g = W 1 * sphericalWhittaker ψ₀ z g := by
  have hg := eq_iwasawa g
  have hu := iwasawaUnip_mem g
  have hk := iwasawaInt_mem g
  rw [hg, sphericalWhittaker_apply hψ₀ z hu hk, hWK _ _ hk, mul_assoc, hWN _ hu,
    casselman_shalika ψ₀ hψ₀ hψ₁ z hWN hWK heig]
  split_ifs <;> ring

end Spherical

end GroundTheory.Automorphic
end
end
