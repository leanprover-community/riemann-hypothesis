module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.PolyRealU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_entry (τ : E →+* ℂ) (i j : Fin n) :
    Continuous fun x : infU E n => (cEmb τ x.1).val i j := by
  have h1 : Continuous (coord (E := E) τ) := by
    unfold coord
    split_ifs
    · exact continuous_apply _
    · exact Complex.continuous_conj.comp (continuous_apply _)
  have h2 : Continuous (pInf E) := continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst
  have h3 : Continuous fun x : infU E n => (x.1.1.val : Matrix (Fin n) (Fin n) (Ad E)) i j :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem i j
  exact h1.comp (h2.comp h3)

theorem poly_infU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, Continuous p) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, star p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ (∀ x y : infU E n, x ≠ y → ∃ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, p x ≠ p y) ∧ (∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, (fun x => p x⁻¹) ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ p ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}, ∃ (m : ℕ) (a b : Fin m → infU E n → ℂ), (∀ i, a i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ b i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) ∧ ∀ x k, p (x * k) = ∑ i, a i x * b i k := by
  intro E _ _ _ n
  have hstar : ∀ (τ : E →+* ℂ) (i j : Fin n), (fun x : infU E n => star ((cEmb τ x.1).val i j)) ∈
      Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} :=
    fun τ i j => Algebra.subset_adjoin
      ⟨ComplexEmbedding.conjugate τ, i, j, funext fun x => (coord_conj τ _).symm⟩
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun x y hxy => ?_, fun p hp => ?_, coprod_adjoin _ ?_⟩
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      exact continuous_entry τ i j
    | algebraMap c => exact continuous_const
    | add p q _ _ hp hq => exact hp.add hq
    | mul p q _ _ hp hq => exact hp.mul hq
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      exact hstar τ i j
    | algebraMap c => exact Subalgebra.algebraMap_mem _ (star c)
    | add p q _ _ hp hq => rw [star_add]; exact add_mem hp hq
    | mul p q _ _ hp hq => rw [star_mul]; exact mul_mem hq hp
  · by_contra h
    push Not at h
    exact hxy (eq_of_entry fun τ i j => h _ (Algebra.subset_adjoin ⟨τ, i, j, rfl⟩))
  · induction hp using Algebra.adjoin_induction with
    | mem p hp =>
      obtain ⟨τ, i, j, rfl⟩ := hp
      convert hstar τ j i using 2 with x
      exact entry_inv τ x.1 i j
    | algebraMap c => exact Subalgebra.algebraMap_mem _ c
    | add p q _ _ hp hq => exact add_mem hp hq
    | mul p q _ _ hp hq => exact mul_mem hp hq
  · rintro _ ⟨τ, i, j, rfl⟩
    refine ⟨n, fun l x => (cEmb τ x.1).val i l, fun l x => (cEmb τ x.1).val l j,
      fun l => ⟨Algebra.subset_adjoin ⟨τ, i, l, rfl⟩, Algebra.subset_adjoin ⟨τ, l, j, rfl⟩⟩, fun x k => ?_⟩
    change (cEmb τ (x.1 * k.1)).val i j = _
    rw [map_mul, Units.val_mul, Matrix.mul_apply]

end GlobalTheory.PolyRealU
