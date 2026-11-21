import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusIntegralIdentity
import BuildAid.ForwardExisting
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralSumCosets
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DigitCharacterSumValues

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem latvol : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} = (modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ * (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} := by
  intro F _ _ _ _ _ _ ψ _ A
  set S : Set (Fin 2 → F) := {x | ∀ i, x i ∈ 𝒪[F]} with hS
  have hSo : IsOpen S := by
    have : S = Set.univ.pi fun _ => (𝒪[F] : Set F) := by
      ext x; simp [hS]
    rw [this]
    exact isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer
  have hSm : MeasurableSet S := hSo.measurableSet
  have hcont : Continuous fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hPm : MeasurableSet ((fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ⁻¹' S) :=
    (hSo.preimage hcont).measurableSet
  have key := GlobalTheory.CompanionTheory.LFGTorus.integral_mulVec ψ A (S.indicator fun _ => (1 : ℂ))
  have e1 : (fun x : Fin 2 → F => S.indicator (fun _ => (1 : ℂ)) ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x)) =
      ((fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ⁻¹' S).indicator fun _ => (1 : ℂ) := by
    ext x
    by_cases h : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x ∈ S
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.2 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.1 h'))]
  rw [e1, integral_indicator_const _ hPm, integral_indicator_const _ hSm] at key
  have hmp : Ad3.mp (GeneralLinearGroup.det A) (-1) =
      (((modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp [Ad3.mp, Complex.cpow_neg]
  rw [hmp] at key
  have : ((Ad3.LFS.vol2 ψ).real ((fun x : Fin 2 → F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) ⁻¹' S) : ℂ) =
      (((modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ * (Ad3.LFS.vol2 ψ).real S : ℝ) : ℂ) := by
    simpa using key
  exact_mod_cast this

end GlobalTheory.CompanionTheory.LFUDom
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_volume_gl_two_translate : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} = (modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ)⁻¹ * (Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.latvol
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom.LatChar

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_psi_ne_one {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) :
    ∃ w : F, w ≠ 0 ∧ -1 ≤ ord w ∧ ψ w ≠ 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have h := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at h
  simp only [IsTrivialOn, not_forall] at h
  obtain ⟨y, hy, hne⟩ := h
  have y0 : y ≠ 0 := by
    rintro rfl
    simp at hne
  exact ⟨y, y0, by simpa using (mem_valBall_iff_le_ord y0).1 hy, hne⟩

theorem mem_integers_iff {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← mem_valBall_iff_le_ord hx, mem_valBall_zero_iff]

theorem exists_lattice_witness {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) (A : GL (Fin 2) F)
    (hA : ¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) :
    ∃ y : Fin 2 → F, (∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ y) i ∈ 𝒪[F]) ∧ ψ (-y 1) ≠ 1 := by
  obtain ⟨w, w0, hw, hne⟩ := exists_psi_ne_one hψ
  simp only [not_forall] at hA
  obtain ⟨b, hb⟩ := hA
  set e := ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b with he
  have e0 : e ≠ 0 := fun h => hb (h ▸ zero_mem _)
  have hord : ord e < 0 := by
    by_contra hc
    exact hb ((mem_integers_iff e0).2 (not_lt.1 hc))
  have ei : e⁻¹ ≠ 0 := inv_ne_zero e0
  have ht : -w * e⁻¹ ∈ 𝒪[F] := by
    have nw : -w ≠ 0 := neg_ne_zero.2 w0
    have hnw : ord (-w) = ord w := by simp [ord, Valuation.map_neg]
    refine (mem_integers_iff (mul_ne_zero nw ei)).2 ?_
    rw [ord_mul nw ei, ord_inv e0, hnw]
    omega
  refine ⟨((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single b (-w * e⁻¹), ?_, ?_⟩
  · intro i
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hi : i = b
    · subst hi; simpa using ht
    · simp [Pi.single_eq_of_ne hi, zero_mem]
  · have : (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single b (-w * e⁻¹)) 1 = -w := by
      have hg : ∀ (M : Matrix (Fin 2) (Fin 2) F) (t : F), (M *ᵥ Pi.single b t) 1 = M 1 b * t := by
        intro M t
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [hg, ← he]
      field_simp
    rw [this, neg_neg]
    exact hne

end GlobalTheory.CompanionTheory.LFUDom.LatChar

open GlobalTheory.CompanionTheory.LFUDom.LatChar in

theorem GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero
    (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (hψ : Ad3.IsStd ψ) (A : GL (Fin 2) F)
    (hA : ¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) :
    ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
      (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ = 0 := by
  obtain ⟨y, hy, hne⟩ := exists_lattice_witness hψ A hA
  have hv : (Ad3.LFS.vol2 ψ).IsAddHaarMeasure := by unfold Ad3.LFS.vol2; infer_instance
  set S := {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} with hS
  set g : (Fin 2 → F) → ℂ := S.indicator (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) with hg
  have hmem : ∀ x, x + y ∈ S ↔ x ∈ S := by
    intro x
    simp only [hS, Set.mem_setOf_eq, Matrix.mulVec_add, Pi.add_apply]
    refine forall_congr' fun i => ?_
    constructor
    · intro h
      simpa using sub_mem h (hy i)
    · intro h
      exact add_mem h (hy i)
  have hshift : ∀ x, g (x + y) = ((ψ (-y 1) : Circle) : ℂ) * g x := by
    intro x
    by_cases hx : x ∈ S
    · rw [hg, Set.indicator_of_mem ((hmem x).2 hx), Set.indicator_of_mem hx, Pi.add_apply,
        neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm]
    · rw [hg, Set.indicator_of_notMem (fun h => hx ((hmem x).1 h)), Set.indicator_of_notMem hx,
        mul_zero]
  have h := integral_add_right_eq_self (μ := Ad3.LFS.vol2 ψ) g y
  simp only [hshift, integral_const_mul] at h
  have hc : ((ψ (-y 1) : Circle) : ℂ) ≠ 1 := fun h1 => hne (Circle.ext (by simpa using h1))
  have : (((ψ (-y 1) : Circle) : ℂ) - 1) * ∫ x, g x ∂Ad3.LFS.vol2 ψ = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hc)
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_character_integral_zero : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (¬ ∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.integral_lattice_char_eq_zero
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

noncomputable section

namespace GlobalTheory.CompanionTheory.LFUDom

theorem latchar1 : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ =
    (((Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} : ℝ) : ℂ) := by
  intro F _ _ _ _ _ _ ψ hψ A hA
  obtain ⟨hc, h1, h0⟩ := hψ
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have hopen : IsOpen {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} := by
    have hs : {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} =
        ⋂ i, (fun x : Fin 2 → F => ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i) ⁻¹'
          (valBall F 0 : Set F) := by
      ext x
      simp [mem_valBall_zero_iff]
    rw [hs]
    refine isOpen_iInter_of_finite fun i => (isOpen_valBall _).preimage ?_
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    fun_prop
  have hf : Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) =
      Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}
        (fun _ => (1 : ℂ)) := by
    refine Set.indicator_congr fun x hx => ?_
    have hx1 : x 1 = (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x)) 1 := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hint : x 1 ∈ 𝒪[F] := by
      have key : ∀ y : Fin 2 → F, (∀ i, y i ∈ 𝒪[F]) →
          (((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ y) 1 ∈ 𝒪[F] := fun y hy => by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        exact add_mem (mul_mem (hA 0) (hy 0)) (mul_mem (hA 1) (hy 1))
      rw [hx1]
      exact key _ hx
    have hb : -x 1 ∈ valBall F 0 := mem_valBall_zero_iff.2 (neg_mem hint)
    rw [ht _ hb]
    simp
  rw [hf, integral_indicator_const _ hopen.measurableSet]
  simp

end GlobalTheory.CompanionTheory.LFUDom
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_character_integral_value : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ A : GL (Fin 2) F,
  (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) →
  ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ =
    (((Ad3.LFS.vol2 ψ).real {x : Fin 2 → F | ∀ i, ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} : ℝ) : ℂ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.latchar1
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem entries_iff (h : GL (Fin 2) F) (l : Fin 3 → ℤ) (x : Fin 2 → F) :
    (∀ i j, ((h : Matrix (Fin 2) (Fin 2) F) * Ad3.LFS.blk x *
        ((torusPow F 3 l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i j ∈ 𝒪[F]) ↔
    (∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) ∧
    ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F] := by
  simp only [Units.val_mul, coe_torusPow, Matrix.mul_diagonal, Fin.forall_fin_succ, Fin.forall_fin_two,
    Ad3.LFS.blk]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.diagonal_apply]
  have e : ∀ a b c d t : F, t * a * b + t * c * d = (a * b + c * d) * t := fun a b c d t => by ring
  simp only [e]
  tauto

end

theorem innred : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (h : GL (Fin 2) F) (l : Fin 3 → ℤ),
  ((¬ ∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) = 0) ∧
  ((∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) =
      ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ) := by
  intro F _ _ _ _ _ _ ψ h l
  have h1 : ∀ X : Matrix (Fin 2) (Fin 3) F, (∀ i j, X i j ∈ 𝒪[F]) → Ad3.LFS.Φ0 F X = 1 := fun X hX =>
    Set.indicator_of_mem (s := {X : Matrix (Fin 2) (Fin 3) F | ∀ i j, X i j ∈ 𝒪[F]}) hX 1
  have h0 : ∀ X : Matrix (Fin 2) (Fin 3) F, (¬ ∀ i j, X i j ∈ 𝒪[F]) → Ad3.LFS.Φ0 F X = 0 := fun X hX =>
    Set.indicator_of_notMem (s := {X : Matrix (Fin 2) (Fin 3) F | ∀ i j, X i j ∈ 𝒪[F]}) hX 1
  refine ⟨fun hn => ?_, fun hy => ?_⟩
  · unfold Ad3.LFS.inn
    have hz : ∀ x : Fin 2 → F, Ad3.LFS.Φ0 F ((h : Matrix (Fin 2) (Fin 2) F) * Ad3.LFS.blk x *
        ((torusPow F 3 l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = 0 := fun x =>
      h0 _ fun q => hn ((entries_iff h l x).1 q).1
    simp [hz]
  · unfold Ad3.LFS.inn
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]
    · beta_reduce
      rw [h1 _ ((entries_iff h l x).2 ⟨hy, hx⟩), one_mul]
      exact (Set.indicator_of_mem (s := {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}) (a := x) hx
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ))).symm
    · beta_reduce
      rw [h0 _ fun q => hx ((entries_iff h l x).1 q).2, zero_mul]
      exact (Set.indicator_of_notMem (s := {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}) (a := x) hx
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ))).symm

end GlobalTheory.CompanionTheory.LFUDom
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_inner_product_support : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (h : GL (Fin 2) F) (l : Fin 3 → ℤ),
  ((¬ ∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) = 0) ∧
  ((∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) =
      ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.innred
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem mul_integral_of_integral {F : Type} [Field F] [ValuativeRel F]
    (A : Matrix (Fin 2) (Fin 2) F) (X : Matrix (Fin 2) (Fin 3) F)
    (hA : ∀ i j, A i j ∈ 𝒪[F]) (hX : ∀ i j, X i j ∈ 𝒪[F]) :
    ∀ i j, (A * X) i j ∈ 𝒪[F] := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hX k j)

theorem Φ0_integral_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (κ : GL (Fin 2) F) (hκ : κ ∈ integralGL F 2)
    (X : Matrix (Fin 2) (Fin 3) F) :
    Ad3.LFS.Φ0 F ((κ : Matrix (Fin 2) (Fin 2) F) * X) = Ad3.LFS.Φ0 F X := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
  have hiff : (∀ i j, ((κ : Matrix (Fin 2) (Fin 2) F) * X) i j ∈ 𝒪[F]) ↔
      ∀ i j, X i j ∈ 𝒪[F] := by
    refine ⟨fun h => ?_, mul_integral_of_integral _ _ h1⟩
    have hk : ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((κ : Matrix (Fin 2) (Fin 2) F) * X) = X := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have := mul_integral_of_integral _ _ h2 h
    rwa [hk] at this
  unfold Ad3.LFS.Φ0
  by_cases hX : ∀ i j, X i j ∈ 𝒪[F]
  · rw [Set.indicator_of_mem (by exact hiff.2 hX), Set.indicator_of_mem (by exact hX)]
    rfl
  · rw [Set.indicator_of_notMem (by exact fun h => hX (hiff.1 h)), Set.indicator_of_notMem (by exact hX)]

theorem inn_Φ0_integral_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (κ : GL (Fin 2) F), κ ∈ integralGL F 2 → ∀ (h : GL (Fin 2) F) (g : GL (Fin 3) F),
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) (κ * h) g = Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h g := by
  intro F _ _ _ _ _ _ ψ κ hκ h g
  unfold Ad3.LFS.inn
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Φ0_integral_mul κ hκ, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.LFUDom
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_inner_product_left_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (κ : GL (Fin 2) F), κ ∈ integralGL F 2 → ∀ (h : GL (Fin 2) F) (g : GL (Fin 3) F),
  Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) (κ * h) g = Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem integral_eq_measure_mul_sum_cosets :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (ι : Type) (R : ι → G) (S : Finset ι) (f : G → ℂ),
  (∀ a b, R a * (R b)⁻¹ ∈ K → a = b) → (∀ κ ∈ K, ∀ g, f (κ * g) = f g) →
  (∀ g, f g ≠ 0 → ∃ a ∈ S, g * (R a)⁻¹ ∈ K) →
  ∫ g, f g ∂μ = ((μ.real (K : Set G) : ℝ) : ℂ) * ∑ a ∈ S, f (R a) :=
  _root_.UpperTheory.Reformulated.B.IntegralSumCosets.integral_eq_measure_mul_sum_cosets

end GlobalTheory.CompanionTheory.LFUDom
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_coset_decomposition : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] (K : Subgroup G),
  IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (ι : Type) (R : ι → G) (S : Finset ι) (f : G → ℂ),
  (∀ a b, R a * (R b)⁻¹ ∈ K → a = b) → (∀ κ ∈ K, ∀ g, f (κ * g) = f g) →
  (∀ g, f g ≠ 0 → ∃ a ∈ S, g * (R a)⁻¹ ∈ K) →
  ∫ g, f g ∂μ = ((μ.real (K : Set G) : ℝ) : ℂ) * ∑ a ∈ S, f (R a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.integral_eq_measure_mul_sum_cosets
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section AntiTranspose

variable {R : Type*} [CommRing R]

def antiTr (A : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![A 1 1, A 0 1; A 1 0, A 0 0]

theorem antiTr_mul (A B : Matrix (Fin 2) (Fin 2) R) : antiTr (A * B) = antiTr B * antiTr A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiTr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem antiTr_one : antiTr (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiTr]

theorem antiTr_antiTr (A : Matrix (Fin 2) (Fin 2) R) : antiTr (antiTr A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antiTr]

def antiTrGL (g : GL (Fin 2) R) : GL (Fin 2) R where
  val := antiTr (g : Matrix (Fin 2) (Fin 2) R)
  inv := antiTr ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  val_inv := by rw [← antiTr_mul, Units.inv_mul, antiTr_one]
  inv_val := by rw [← antiTr_mul, Units.mul_inv, antiTr_one]

theorem coe_antiTrGL (g : GL (Fin 2) R) :
    (antiTrGL g : Matrix (Fin 2) (Fin 2) R) = antiTr (g : Matrix (Fin 2) (Fin 2) R) := rfl

theorem antiTrGL_mul (x y : GL (Fin 2) R) : antiTrGL (x * y) = antiTrGL y * antiTrGL x :=
  Units.ext (antiTr_mul _ _)

theorem antiTrGL_inv (x : GL (Fin 2) R) : antiTrGL x⁻¹ = (antiTrGL x)⁻¹ :=
  Units.ext rfl

theorem antiTrGL_antiTrGL (x : GL (Fin 2) R) : antiTrGL (antiTrGL x) = x :=
  Units.ext (antiTr_antiTr _)

end AntiTranspose

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem antiTr_entries_mem {A : Matrix (Fin 2) (Fin 2) F} (hA : ∀ a b, A a b ∈ 𝒪[F]) (a b : Fin 2) :
    antiTr A a b ∈ 𝒪[F] := by
  fin_cases a <;> fin_cases b <;> simpa [antiTr] using hA _ _

theorem antiTrGL_mem_integralGL {x : GL (Fin 2) F} (hx : x ∈ integralGL F 2) :
    antiTrGL x ∈ integralGL F 2 := by
  obtain ⟨h1, h2⟩ := (mem_integralGL_iff F 2).1 hx
  refine (mem_integralGL_iff F 2).2 ⟨fun a b => antiTr_entries_mem h1 a b, fun a b => ?_⟩
  rw [← antiTrGL_inv]
  exact antiTr_entries_mem h2 a b

theorem antiTrGL_rowRep (l : Fin 2 → ℕ) (c : NormalData F l) :
    antiTrGL (rowRep (l 1) (l 0) (c ⟨(0, 1), by decide⟩)) = normalGL F l c := by
  refine Units.ext ?_
  rw [coe_antiTrGL, coe_rowRep, coe_normalGL]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [antiTr] using (normalMat_self l c 0).symm
  · simpa [antiTr] using (normalMat_of_lt l c (i := 0) (j := 1) (by decide)).symm
  · simpa [antiTr] using (normalMat_of_gt l c (i := 1) (j := 0) (by decide)).symm
  · simpa [antiTr] using (normalMat_self l c 1).symm

theorem exists_mul_rowRep_inv_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F)
    (hg : ∀ a b, (g : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) :
    ∃ (i j : ℕ) (c : Fin j → 𝓀[F]), g * (rowRep i j c)⁻¹ ∈ integralGL F 2 := by
  obtain ⟨l, c, hc⟩ := exists_normalGL (g := antiTrGL g) (fun a b => antiTr_entries_mem hg a b)
  have h1 : (normalGL F l c)⁻¹ * antiTrGL g ∈ integralGL F 2 := QuotientGroup.eq.1 hc
  refine ⟨l 1, l 0, c ⟨(0, 1), by decide⟩, ?_⟩
  have h2 : antiTrGL (g * (rowRep (l 1) (l 0) (c ⟨(0, 1), by decide⟩))⁻¹) ∈ integralGL F 2 := by
    rw [antiTrGL_mul, antiTrGL_inv, antiTrGL_rowRep]
    exact h1
  have h3 := antiTrGL_mem_integralGL h2
  rwa [antiTrGL_antiTrGL] at h3

end GlobalTheory.CompanionTheory.LFUDom
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_matrix_row_rep_exists : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (g : GL (Fin 2) F), (∀ a b, (g : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
  ∃ (i j : ℕ) (c : Fin j → 𝓀[F]), g * (rowRep i j c)⁻¹ ∈ integralGL F 2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.exists_mul_rowRep_inv_mem
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem le_of_mul_pow_eq_pow {m n : ℕ} {y : F} (hy : y ∈ 𝒪[F])
    (h : y * (GLnLocal.uniformizer F : F) ^ n = (GLnLocal.uniformizer F : F) ^ m) : n ≤ m := by
  have hb := (bdd_of_mem hy).mul (bdd_zpow (F := F) (n : ℤ))
  rw [zero_add, zpow_natCast, h, ← zpow_natCast] at hb
  exact_mod_cast le_of_bdd_zpow hb

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem entries_of_mul_eq {K : Matrix (Fin 2) (Fin 2) F} {x y z x' y' z' : F}
    (h : K * !![x', y'; 0, z'] = !![x, y; 0, z]) :
    K 0 0 * x' = x ∧ K 1 0 * x' = 0 ∧ K 0 0 * y' + K 0 1 * z' = y ∧
      K 1 0 * y' + K 1 1 * z' = z := by
  have h00 := congrFun (congrFun h 0) 0
  have h10 := congrFun (congrFun h 1) 0
  have h01 := congrFun (congrFun h 0) 1
  have h11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h10 h01 h11
  refine ⟨h00, ?_, h01, h11⟩
  simpa using h10

theorem rowRep_unique (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (a b : Σ _ : ℕ, Σ j : ℕ, (Fin j → 𝓀[F]))
    (h : rowRep a.1 a.2.1 a.2.2 * (rowRep b.1 b.2.1 b.2.2)⁻¹ ∈ integralGL F 2) : a = b := by
  obtain ⟨i, j, c⟩ := a
  obtain ⟨i', j', c'⟩ := b
  dsimp only at h
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  obtain ⟨hO, hI⟩ := (mem_integralGL_iff F 2).1 h
  set κ := rowRep i j c * (rowRep i' j' c')⁻¹ with hκ
  have e1 : (κ : Matrix (Fin 2) (Fin 2) F) * (rowRep i' j' c' : Matrix (Fin 2) (Fin 2) F) =
      (rowRep i j c : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, hκ, inv_mul_cancel_right]
  have e2 : ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (rowRep i j c : Matrix (Fin 2) (Fin 2) F) =
      (rowRep i' j' c' : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, hκ, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
  rw [coe_rowRep, coe_rowRep] at e1 e2
  obtain ⟨p1, r1, q1, s1⟩ := entries_of_mul_eq e1
  obtain ⟨p2, r2, q2, s2⟩ := entries_of_mul_eq e2
  have hr : (κ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    (mul_eq_zero.1 r1).resolve_right (pow_ne_zero _ hϖ)
  have hr' : ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 :=
    (mul_eq_zero.1 r2).resolve_right (pow_ne_zero _ hϖ)
  rw [hr, zero_mul, zero_add] at s1
  rw [hr', zero_mul, zero_add] at s2
  have hi : i = i' := le_antisymm (le_of_mul_pow_eq_pow (hI 0 0) p2) (le_of_mul_pow_eq_pow (hO 0 0) p1)
  have hj : j = j' := le_antisymm (le_of_mul_pow_eq_pow (hI 1 1) s2) (le_of_mul_pow_eq_pow (hO 1 1) s1)
  subst hi hj
  have hp : (κ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 :=
    mul_right_cancel₀ (pow_ne_zero i hϖ) (by rw [p1, one_mul])
  rw [hp, one_mul] at q1
  have hb : Bdd F (j : ℤ) (digitSum F j c - digitSum F j c') := by
    have := (bdd_of_mem (hO 0 1)).mul (bdd_zpow (F := F) (j : ℤ))
    rw [zero_add, zpow_natCast] at this
    convert this using 1
    rw [← q1]
    ring
  rw [eq_of_bdd_digitSum_sub j hb]

end GlobalTheory.CompanionTheory.LFUDom
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_reps_distinct_cosets : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : Σ _ : ℕ, Σ j : ℕ, (Fin j → 𝓀[F])),
  rowRep a.1 a.2.1 a.2.2 * (rowRep b.1 b.2.1 b.2.2)⁻¹ ∈ integralGL F 2 → a = b := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.rowRep_unique
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem torusPow_mul_rowRep_inv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]),
  torusPow F 2 ![a, b] * (rowRep i j c)⁻¹ =
    Ad3.uni2 (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * torusPow F 2 ![a - i, b - j] := by
  intro F _ _ _ _ a b i j c
  have h : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have e1 : (GLnLocal.uniformizer F : F) ^ (a - i) * (GLnLocal.uniformizer F : F) ^ i =
      (GLnLocal.uniformizer F : F) ^ a := by
    rw [← zpow_natCast, ← zpow_add₀ h, sub_add_cancel]
  have e2 : (GLnLocal.uniformizer F : F) ^ (b - j) * (GLnLocal.uniformizer F : F) ^ j =
      (GLnLocal.uniformizer F : F) ^ b := by
    rw [← zpow_natCast, ← zpow_add₀ h, sub_add_cancel]
  have e3 : (GLnLocal.uniformizer F : F) ^ (a - b - i) * (GLnLocal.uniformizer F : F) ^ b =
      (GLnLocal.uniformizer F : F) ^ (a - i) := by
    rw [← zpow_add₀ h]
    congr 1
    ring
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_rowRep, coe_torusPow, coe_torusPow]
  simp only [Ad3.uni2]
  have d : ∀ u v : ℤ, (diagonal fun k => (GLnLocal.uniformizer F : F) ^ (![u, v] k)) =
      !![(GLnLocal.uniformizer F : F) ^ u, 0; 0, (GLnLocal.uniformizer F : F) ^ v] := by
    intro u v
    ext r s
    fin_cases r <;> fin_cases s <;> simp
  rw [d, d]
  ext r s
  fin_cases r <;> fin_cases s <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -e1
  · linear_combination (digitSum F j c * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * e2 + digitSum F j c * e3
  · linear_combination -e2

end GlobalTheory.CompanionTheory.LFUDom
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_row_rep_factorization : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (a b : ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]),
  torusPow F 2 ![a, b] * (rowRep i j c)⁻¹ =
    Ad3.uni2 (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ (a - b - i)) * torusPow F 2 ![a - i, b - j] := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.torusPow_mul_rowRep_inv
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

theorem compChar_eq_one_of_isStd {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {ψ : AddChar F Circle} (h : Ad3.IsStd ψ) :
    ∀ x ∈ 𝒪[F], Circle.coeHom.compAddChar ψ x = 1 := by
  intro x hx
  obtain ⟨hc, h1, h0⟩ := h
  have ht := isTrivialOn_addCharConductor hc h1
  rw [h0] at ht
  have := ht x (mem_valBall_zero_iff.2 hx)
  show ((ψ x : Circle) : ℂ) = 1
  rw [this, Circle.coe_one]

theorem uni2_mem_unipotent {F : Type} [Field F] (y : F) : Ad3.uni2 y ∈ unipotent F 2 := by
  refine ⟨fun {i j} hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [Ad3.uni2]
  · fin_cases i <;> simp [Ad3.uni2]

theorem superdiagSum_uni2 {F : Type} [Field F] (y : F) :
    Whittaker.superdiagSum ((Ad3.uni2 y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = y := by
  simp [Whittaker.superdiagSum, Fin.sum_univ_two, Ad3.uni2]

theorem whittaker_unipotent_left_equivariant : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle),
    Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (y : F) (g : GL (Fin 2) F),
      Ad3.LFS.s2 ψ ν (Ad3.uni2 y * g) = ((ψ y : Circle) : ℂ) * Ad3.LFS.s2 ψ ν g := by
  intro F _ _ _ _ _ _ ψ hψ ν y g
  unfold Ad3.LFS.s2
  rw [sphericalWhittaker_mul_left (compChar_eq_one_of_isStd hψ) _ (uni2_mem_unipotent y) g,
    Whittaker.psiN, superdiagSum_uni2]
  rfl

end GlobalTheory.CompanionTheory.LFUDom
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_unipotent_equivariant_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (y : F) (g : GL (Fin 2) F),
  Ad3.LFS.s2 ψ ν (Ad3.uni2 y * g) = ((ψ y : Circle) : ℂ) * Ad3.LFS.s2 ψ ν g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.whittaker_unipotent_left_equivariant
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem whittaker_torus_value_formula (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle) (hψ : Ad3.IsStd ψ) (ν : Fˣ →* ℂˣ) (a b : ℤ) :
    (b ≤ a → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) =
      sqrtQ F ^ (-(a - b)) * evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])) ∧
    (a < b → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) = 0) := by
  have hψ₀ : ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1 := by
    intro x hx
    obtain ⟨hc, h1, h0⟩ := hψ
    have ht := isTrivialOn_addCharConductor hc h1
    rw [h0] at ht
    have := ht x (mem_valBall_zero_iff.2 hx)
    show ((ψ x : Circle) : ℂ) = 1
    rw [this, Circle.coe_one]
  have hanti : Antitone (![a, b] : Fin 2 → ℤ) ↔ b ≤ a := by
    constructor
    · intro h
      simpa using h (show (0 : Fin 2) ≤ 1 by decide)
    · intro h i j hij
      fin_cases i <;> fin_cases j <;> simp_all
  have hrho : rhoPair (![a, b] : Fin 2 → ℤ) = a - b := by
    simp [rhoPair, Fin.sum_univ_two]
    ring
  have key := sphericalWhittaker_torusPow hψ₀ ![ν (unifUnit F), ν⁻¹ (unifUnit F)] ![a, b]
  rw [MonoidHom.inv_apply] at key
  unfold Ad3.LFS.s2
  rw [MonoidHom.inv_apply, key]
  constructor
  · intro h
    rw [if_pos (hanti.2 h), halfModulus_eq, hrho]
  · intro h
    rw [if_neg (fun h' => absurd (hanti.1 h') (not_le.2 h))]

end GlobalTheory.CompanionTheory.LFUDom
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_torus_value_formula_holds : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (ν : Fˣ →* ℂˣ) (a b : ℤ),
  (b ≤ a → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) =
    sqrtQ F ^ (-(a - b)) * evalAt ![ν (unifUnit F), (ν (unifUnit F))⁻¹] (schur ![a, b])) ∧
  (a < b → Ad3.LFS.s2 ψ ν (torusPow F 2 ![a, b]) = 0) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.whittaker_torus_value_formula
end

section
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem mp_uniformizerUnit_zpow_half (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (m t : ℤ) :
    Ad3.mp (uniformizerUnit F ^ m) ((t : ℂ) / 2) = sqrtQ F ^ (-(t * m)) := by
  set r : ℝ := (NNReal.sqrt (qF F : NNReal) : ℝ) with hr
  have hq0 : (0 : ℝ) < residueCard F := by
    exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have hrq : r ^ 2 = (residueCard F : ℝ) := by
    rw [hr, ← NNReal.coe_pow, NNReal.sq_sqrt]
    simp [qF, residueCard]
  have hr0 : 0 < r := by
    rcases (NNReal.coe_nonneg (NNReal.sqrt (qF F : NNReal))).lt_or_eq with h | h
    · exact h
    · exfalso
      have : r = 0 := h.symm
      rw [this] at hrq
      simp at hrq
      exact hq0.ne' (by exact_mod_cast hrq.symm)
  have hord : ord (((uniformizerUnit F ^ m : Fˣ)) : F) = m := by
    rw [ord_units_zpow, coe_uniformizerUnit, ord_uniformizer (irreducible_uniformizer F), mul_one]
  have hmod : ((modulus (((uniformizerUnit F ^ m : Fˣ)) : F) : NNReal) : ℝ) = r ^ (-(2 * m)) := by
    rw [modulus_of_ne_zero (Units.ne_zero _), hord, NNReal.coe_zpow, NNReal.coe_natCast, ← hrq,
      ← zpow_natCast, ← _root_.zpow_mul]
    norm_num
  have hpow : (r ^ (-(2 * m))) ^ ((t : ℝ) / 2) = r ^ (-(t * m)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_mul hr0.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hcast : ((t : ℂ) / 2) = (((t : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
  have hnn : 0 ≤ r ^ (-(2 * m)) := (zpow_pos hr0 _).le
  unfold Ad3.mp
  rw [hmod, hcast, ← Complex.ofReal_cpow hnn, hpow, Complex.ofReal_zpow]
  rfl

end GlobalTheory.CompanionTheory.LFUDom
end
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_uniformizer_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (m t : ℤ), Ad3.mp (uniformizerUnit F ^ m) ((t : ℂ) / 2) = sqrtQ F ^ (-(t * m)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.mp_uniformizerUnit_zpow_half
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem det_torusPow_eq (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℤ) :
    GeneralLinearGroup.det (torusPow F n l) = uniformizerUnit F ^ (∑ i, l i) := by
  have key : ∀ s : Finset (Fin n),
      ∏ i ∈ s, uniformizerUnit F ^ l i = uniformizerUnit F ^ (∑ i ∈ s, l i) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, _root_.zpow_add]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_torusPow, det_diagonal, ← key Finset.univ]
  simp [Units.coe_prod, Iwasawa.coe_uniformizerUnit, Units.val_zpow_eq_zpow_val]

end GlobalTheory.CompanionTheory.LFUDom
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_torus_power : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (l : Fin n → ℤ), GeneralLinearGroup.det (torusPow F n l) = uniformizerUnit F ^ (∑ i, l i) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.det_torusPow_eq
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem det_rowRep_eq_zpow : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (i j : ℕ) (c : Fin j → 𝓀[F]), GeneralLinearGroup.det (rowRep i j c) = uniformizerUnit F ^ ((i : ℤ) + j) := by
  intro F _ _ _ _ i j c
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_rowRep, Matrix.det_fin_two_of]
  have h : ((i : ℤ) + j) = ((i + j : ℕ) : ℤ) := by push_cast; rfl
  rw [h, zpow_natCast, Units.val_pow_eq_pow_val, coe_uniformizerUnit, pow_add]
  simp

end GlobalTheory.CompanionTheory.LFUDom
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_row_rep : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (i j : ℕ) (c : Fin j → 𝓀[F]), GeneralLinearGroup.det (rowRep i j c) = uniformizerUnit F ^ ((i : ℤ) + j) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.det_rowRep_eq_zpow
end

section
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem uniformizer_zpow_mem_integers_iff :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (z : ℤ), (GLnLocal.uniformizer F : F) ^ z ∈ 𝒪[F] ↔ 0 ≤ z := by
  intro F _ _ _ _ z
  constructor
  · intro h
    by_contra hz
    have hz' : 0 < -z := by omega
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hz'.le
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
      omega
    have hlt := GLnLocal.valuation_uniformizer_lt_one F
    have hpow : (GLnLocal.uniformizer F : F) ^ m ∈ 𝒪[F] :=
      Subring.pow_mem _ (GLnLocal.uniformizer F).2 m
    have hne : (GLnLocal.uniformizer F : F) ≠ 0 := by
      intro h0
      have h1 := GLnLocal.uniformizer_ne_zero F
      exact h1 h0
    have hone : (GLnLocal.uniformizer F : F) ^ z * (GLnLocal.uniformizer F : F) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hne, ← hm]
      simp
    have hv : ValuativeRel.valuation F ((GLnLocal.uniformizer F : F) ^ z) ≤ 1 := h
    have hvm : ValuativeRel.valuation F ((GLnLocal.uniformizer F : F) ^ m) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ zero_le' hlt hm0
    have h2 : ValuativeRel.valuation F
        ((GLnLocal.uniformizer F : F) ^ z * (GLnLocal.uniformizer F : F) ^ m) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) hvm
    rw [hone, map_one] at h2
    exact lt_irrefl _ h2
  · intro h
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast]
    exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 m

end GlobalTheory.CompanionTheory.LFUDom
end

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_zpow_mem_integers_iff' : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (z : ℤ), (GLnLocal.uniformizer F : F) ^ z ∈ 𝒪[F] ↔ 0 ≤ z := by
  atlas_forward_decl GlobalTheory.CompanionTheory.LFUDom.uniformizer_zpow_mem_integers_iff
end

section
noncomputable section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom
open Ad3 Ad3.LFS

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

local notation "ϖ" => (GLnLocal.uniformizer F : F)

theorem mp_mul' (a b : Fˣ) (s : ℂ) : mp (a * b) s = mp a s * mp b s := by
  simpa [mp, GodementSectionLocal.modPow] using GodementSectionLocal.modPow_mul (a : F) (b : F) s


def f1 (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (k : GL (Fin 2) F) : ℂ :=
  s2 ψ ν (k * (torusPow F 2 ![l 0, l 1])⁻¹)⁻¹ *
    mp (GeneralLinearGroup.det (k * (torusPow F 2 ![l 0, l 1])⁻¹)) (3 / 2) *
    inn ψ (Φ0 F) (k * (torusPow F 2 ![l 0, l 1])⁻¹) (torusPow F 3 l)



abbrev V2 (ψ : AddChar F Circle) : ℝ := (vol2 ψ).real {x : Fin 2 → F | ∀ i, x i ∈ 𝒪[F]}


theorem det_kd (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    GeneralLinearGroup.det (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹) =
      uniformizerUnit F ^ ((i : ℤ) + j - l 0 - l 1) := by
  rw [map_mul, map_inv, GlobalTheory.T.det_row_rep, GlobalTheory.T.det_torus_power, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← _root_.zpow_neg, ← _root_.zpow_add]
  congr 1
  ring

theorem inv_kd (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹)⁻¹ =
      uni2 (-(digitSum F j c) * ϖ ^ (l 0 - l 1 - i)) * torusPow F 2 ![l 0 - i, l 1 - j] := by
  rw [_root_.mul_inv_rev, inv_inv, GlobalTheory.T.torus_row_rep_factorization]

theorem row_A (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) (b : Fin 2) :
    (((torusPow F 2 ![l 2, l 2] * (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹))⁻¹ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) 1 b = if b = 1 then ϖ ^ (l 1 - j - l 2) else 0 := by
  rw [_root_.mul_inv_rev, inv_kd, mul_assoc, ← torusPow_neg, ← torusPow_add]
  have e : (![l 0 - i, l 1 - j] + -![l 2, l 2] : Fin 2 → ℤ) = ![l 0 - i - l 2, l 1 - j - l 2] := by
    ext t; fin_cases t <;> simp <;> ring
  rw [e, Units.val_mul, coe_torusPow]
  simp only [uni2]
  fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem inn_rep {ψ : AddChar F Circle} (hψ : IsStd ψ) (l : Fin 3 → ℤ) (i j : ℕ) (c : Fin j → 𝓀[F]) :
    inn ψ (Φ0 F) (rowRep i j c * (torusPow F 2 ![l 0, l 1])⁻¹) (torusPow F 3 l) =
      if (j : ℤ) ≤ l 1 - l 2 then
        sqrtQ F ^ (2 * (2 * l 2 + i + j - l 0 - l 1)) * ((V2 ψ : ℝ) : ℂ) else 0 := by
  set k := rowRep i j c with hk
  set d := torusPow F 2 ![l 0, l 1] with hd
  set A := torusPow F 2 ![l 2, l 2] * (k * d⁻¹) with hA
  have hint : ∀ a b, (((k * d⁻¹ * d : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F] := by
    intro a b
    rw [inv_mul_cancel_right, hk, coe_rowRep]
    have h0 := (GLnLocal.uniformizer F).2
    fin_cases a <;> fin_cases b <;> simp
    · exact pow_mem h0 _
    · exact digitSum_mem _ _
    · exact pow_mem h0 _
  rw [(GlobalTheory.T.local_inner_product_support F ψ (k * d⁻¹) l).2 hint]
  have hrow : (∀ b, ((A⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 b ∈ 𝒪[F]) ↔ (j : ℤ) ≤ l 1 - l 2 := by
    rw [Fin.forall_fin_two, hA, hk, hd, row_A, row_A]
    simp only [zero_ne_one, if_false, if_true, Subring.zero_mem, true_and, GlobalTheory.T.uniformizer_zpow_mem_integers_iff']
    constructor <;> intro h <;> linarith
  split_ifs with hj
  · rw [GlobalTheory.T.lattice_character_integral_value F ψ hψ A (hrow.2 hj), GlobalTheory.T.lattice_volume_gl_two_translate F ψ hψ A]
    have hdet : GeneralLinearGroup.det A = uniformizerUnit F ^ (2 * l 2 + i + j - l 0 - l 1) := by
      rw [hA, map_mul, GlobalTheory.T.det_torus_power, det_kd, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← _root_.zpow_add]
      congr 1
      ring
    have hm := GlobalTheory.T.unramified_character_uniformizer_power F (2 * l 2 + i + j - l 0 - l 1) (-2)
    rw [← hdet] at hm
    have hm' : mp (GeneralLinearGroup.det A) (-1) = ((modulus ((GeneralLinearGroup.det A : Fˣ) : F) : ℝ) : ℂ)⁻¹ := by
      simp [mp, Complex.cpow_neg_one]
    have e1 : (((-2 : ℤ) : ℂ) / 2) = -1 := by norm_num
    rw [e1, hm'] at hm
    push_cast
    rw [hm]
    congr 2
    ring
  · exact GlobalTheory.T.lattice_character_integral_zero F ψ hψ A (fun h => hj (hrow.1 h))

def Cc (ψ : AddChar F Circle) (l : Fin 3 → ℤ) (i j : ℕ) : ℂ :=
  sqrtQ F ^ (-(3 * ((i : ℤ) + j - l 0 - l 1))) * sqrtQ F ^ (2 * (2 * l 2 + i + j - l 0 - l 1)) *
    ((V2 ψ : ℝ) : ℂ)

theorem unramified_vector_rep_formula {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (i j : ℕ)
    (c : Fin j → 𝓀[F]) :
    f1 ψ ν l (rowRep i j c) = if (j : ℤ) ≤ l 1 - l 2 then
      ((ψ (-(digitSum F j c) * ϖ ^ (l 0 - l 1 - i)) : Circle) : ℂ) *
        s2 ψ ν (torusPow F 2 ![l 0 - i, l 1 - j]) * Cc ψ l i j else 0 := by
  unfold f1
  rw [inv_kd, GlobalTheory.T.whittaker_unipotent_equivariant_holds F ψ hψ, det_kd, inn_rep hψ]
  have hm := GlobalTheory.T.unramified_character_uniformizer_power F ((i : ℤ) + j - l 0 - l 1) 3
  have e : (((3 : ℤ) : ℂ) / 2) = 3 / 2 := by norm_num
  rw [e] at hm
  rw [hm]
  split_ifs
  · simp only [Cc]
    ring
  · simp


theorem sum_rep {ψ : AddChar F Circle} (hψ : IsStd ψ) (ν : Fˣ →* ℂˣ) (l : Fin 3 → ℤ) (i j : ℕ)
    (hj : (j : ℤ) ≤ l 1 - l 2) :
    ∑ c : Fin j → 𝓀[F], f1 ψ ν l (rowRep i j c) = if (i : ℤ) ≤ l 0 - l 1 then
      (qF F : ℂ) ^ j * s2 ψ ν (torusPow F 2 ![l 0 - i, l 1 - j]) * Cc ψ l i j else 0 := by
  simp_rw [unramified_vector_rep_formula hψ, if_pos hj]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  split_ifs with hi
  · rw [(GlobalTheory.T.digit_character_sum_values F ψ hψ j _).1 (by linarith)]
  · by_cases h2 : l 1 - j ≤ l 0 - i
    · rw [(GlobalTheory.T.digit_character_sum_values F ψ hψ j _).2 (by linarith) (by linarith)]
      simp
    · rw [(GlobalTheory.T.whittaker_torus_value_formula_holds F ψ hψ ν _ _).2 (not_le.1 h2)]
      simp


end Main


end GlobalTheory.CompanionTheory.LFUDom
end
end
