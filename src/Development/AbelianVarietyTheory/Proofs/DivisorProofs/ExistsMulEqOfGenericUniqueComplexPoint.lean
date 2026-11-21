import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingsAgreeOnSubfieldNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqZeroOfForallLTensorEqZero
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22

section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range : ∀ (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] [CharZero L] (a : Ω), a ∉ Set.range (algebraMap L Ω) → ∃ (F : Type) (_ : Field F) (i₁ i₂ : Ω →+* F), i₁.comp (algebraMap L Ω) = i₂.comp (algebraMap L Ω) ∧ i₁ a ≠ i₂ a := by
  first | exact @GlobalTheory.exists_embeddings_agree_on_subfield_ne | exact GlobalTheory.exists_embeddings_agree_on_subfield_ne | (intros; apply GlobalTheory.exists_embeddings_agree_on_subfield_ne <;> assumption)
end

section
namespace GlobalTheory

theorem exists_ne_zero_forall_complexPoint_separate
    (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A]
    [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F)
    (h : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A))
    (hinj : Function.Injective (j₁.comp (algebraMap B A))) (a : A) (ha : j₁ a ≠ j₂ a) :
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ,
      y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  classical
  letI : Algebra B F := (j₁.comp (algebraMap B A)).toAlgebra
  let J₁ : A →ₐ[B] F := { j₁ with commutes' := fun _ => rfl }
  let J₂ : A →ₐ[B] F := { j₂ with commutes' := fun b => (RingHom.congr_fun h b).symm }
  let u : F := (j₁ a - j₂ a)⁻¹
  let D : Subalgebra B F := (Subalgebra.map J₁ ⊤ ⊔ Subalgebra.map J₂ ⊤) ⊔
    Algebra.adjoin B (({u} : Finset F) : Set F)
  have hA : (⊤ : Subalgebra B A).FG := Algebra.FiniteType.out
  have hD : D.FG := ((hA.map J₁).sup (hA.map J₂)).sup (Subalgebra.fg_adjoin_finset _)
  haveI : Algebra.FiniteType B D := (Subalgebra.fg_iff_finiteType D).1 hD
  have h1 : ∀ x, J₁ x ∈ D := fun x =>
    (le_sup_left.trans le_sup_left : Subalgebra.map J₁ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have h2 : ∀ x, J₂ x ∈ D := fun x =>
    (le_sup_right.trans le_sup_left : Subalgebra.map J₂ ⊤ ≤ D) ⟨x, trivial, rfl⟩
  have hu : u ∈ D := (le_sup_right : _ ≤ D) (Algebra.subset_adjoin (by simp))
  have hBD : Function.Injective (algebraMap B D) := fun x y hxy =>
    hinj (congrArg Subtype.val hxy)
  obtain ⟨q, hq, H⟩ := GlobalTheory.exists_ne_zero_forall_complexPoint_extend B D hBD
  refine ⟨q, hq, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := H φ hφ
  let K₁ : A →ₐ[B] D := J₁.codRestrict D h1
  let K₂ : A →ₐ[B] D := J₂.codRestrict D h2
  refine ⟨ψ.comp (K₁ : A →+* D), ψ.comp (K₂ : A →+* D), ?_, ?_, ?_⟩
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · rw [RingHom.comp_assoc, AlgHom.comp_algebraMap, hψ]
  · intro heq
    have hone : (⟨u, hu⟩ : D) * (K₁ a - K₂ a) = 1 :=
      Subtype.ext (inv_mul_cancel₀ (sub_ne_zero.2 ha))
    have h3 := congrArg ψ hone
    have heq' : ψ (K₁ a) = ψ (K₂ a) := heq
    rw [map_mul, map_sub, heq', sub_self, mul_zero, map_one] at h3
    exact zero_ne_one h3

end GlobalTheory
end

section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' : ∀ (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F), j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) → Function.Injective (j₁.comp (algebraMap B A)) → ∀ a : A, j₁ a ≠ j₂ a → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ, y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  atlas_forward_decl GlobalTheory.exists_ne_zero_forall_complexPoint_separate
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

theorem exists_mul_eq_of_generic_unique_complexPoint : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : K →+* ℂ) (A B : Subalgebra K Ω), A.FG → B.FG → B ≤ A → (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : K, x (algebraMap K A k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : K, y (algebraMap K A k) = σ k) → (∀ a : A, (a : Ω) ∈ B → y a = x a) → y = x) → ∀ a ∈ A, ∃ p ∈ B, ∃ q ∈ B, q ≠ 0 ∧ a * q = p := by
  intro K Ω _ _ _ σ A B hA hB hBA H a haA
  by_contra hne
  haveI : CharZero K := ⟨fun m n h => Nat.cast_injective (R := ℂ) (by simpa using congrArg σ h)⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L := IntermediateField.adjoin K (B : Set Ω)
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have haL : a ∉ Set.range (algebraMap L Ω) := by
    rintro ⟨l, hl⟩
    have hmem : a ∈ L := hl ▸ l.2
    obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hmem
    rw [Algebra.adjoin_eq] at hr hs
    apply hne
    by_cases hs0 : s = 0
    · exact ⟨0, B.zero_mem, 1, B.one_mem, one_ne_zero, by simp [hs0]⟩
    · exact ⟨r, hr, s, hs, hs0, div_mul_cancel₀ r hs0⟩
  obtain ⟨F, _, i₁, i₂, hi, hne2⟩ := GlobalTheory.T.exists_ringHom_pair_eq_on_subfield_ne_of_not_mem_range L Ω a haL
  letI : Algebra B A := (Subalgebra.inclusion hBA).toRingHom.toAlgebra
  haveI : IsScalarTower K B A := IsScalarTower.of_algebraMap_eq fun k => rfl
  haveI : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).1 hA
  haveI : Algebra.FiniteType K B := (Subalgebra.fg_iff_finiteType B).1 hB
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  haveI : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType K B A
  let j₁ : A →+* F := i₁.comp A.val.toRingHom
  let j₂ : A →+* F := i₂.comp A.val.toRingHom
  have hBL : ∀ b : B, (b : Ω) = algebraMap L Ω ⟨b, IntermediateField.subset_adjoin K _ b.2⟩ := fun b => rfl
  have hj : j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) := by
    ext b
    change i₁ (b : Ω) = i₂ (b : Ω)
    rw [hBL b]
    exact congrArg (fun f : L →+* F => f _) hi
  have hinj : Function.Injective (j₁.comp (algebraMap B A)) := by
    intro b c h
    exact Subtype.ext (i₁.injective h)
  obtain ⟨q, hq, Hq⟩ := GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' B A F j₁ j₂ hj hinj ⟨a, haA⟩ hne2
  obtain ⟨x, hxσ, hxq, hxu⟩ := H q q.2 (fun h => hq (Subtype.ext h))
  let φ : B →+* ℂ := x.comp (algebraMap B A)
  have hφq : φ q ≠ 0 := hxq (hBA q.2)
  obtain ⟨y₁, y₂, h₁, h₂, hy⟩ := Hq φ hφq
  have key : ∀ y : A →+* ℂ, y.comp (algebraMap B A) = φ → y = x := by
    intro y hy
    refine hxu y (fun k => ?_) (fun a' ha' => ?_)
    · have e1 : algebraMap K A k = algebraMap B A (algebraMap K B k) := rfl
      rw [e1, ← hxσ k, e1]
      exact congrArg (fun f : B →+* ℂ => f (algebraMap K B k)) hy
    · have e1 : a' = algebraMap B A ⟨a', ha'⟩ := rfl
      rw [e1]
      exact congrArg (fun f : B →+* ℂ => f ⟨a', ha'⟩) hy
  exact hy (by rw [key y₁ h₁, key y₂ h₂])

end GlobalTheory.DegVal
end
