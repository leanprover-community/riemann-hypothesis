import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (Embeds isIrreducible_of_equiv mem_fixed)

namespace GlobalTheory.LocGL.Tests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem nonempty_equiv_parInd_zero {d : Fin 0 → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem nonempty_equiv_prodIrr_zero (x : Fin 0 → IrrGL k) (hd : ∑ a, (x a).1 = 0) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (prodIrr x hd)) :=
  nonempty_equiv_parInd_zero _ _ (PiTensorProduct.isEmptyEquiv (R := ℂ) (Fin 0) (s := fun a => (x a).2.rep.V)).symm

theorem empty_spec : IsZ (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ∧
    IsL (0 : Multiset (Segment k)) (detRep (Fin 0) (1 : kˣ →* ℂˣ)) := by
  obtain ⟨φ⟩ := nonempty_equiv_prodIrr_zero (k := k) Fin.elim0 rfl
  have ho : IsOrderedForm (k := k) (Fin.elim0 : Fin 0 → Segment k) 0 := ⟨rfl, fun i => i.elim0⟩
  exact ⟨⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isSocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩,
    ⟨0, Fin.elim0, rfl, ⟨_, ho, fun i => i.elim0⟩, (isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ⟩⟩






theorem not_isGeneric_detRep (χ : kˣ →* ℂˣ) : ¬ IsGeneric (detRep (Fin 2) χ) := by
  rintro ⟨ψ, -, hψ, h⟩
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra! h; exact hψ (AddChar.ext _ _ h)
  let u : GL (Fin 2) k := GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by simp)
  have hu : u ∈ unipB k (Fin 2) := (mem_unipB k).2 ⟨fun i j hij => by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) i j = 0
    fin_cases i <;> fin_cases j <;> simp at hij ⊢, fun i => by
    show (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) i i = 1
    fin_cases i <;> simp⟩
  have hw : (whitChar ψ 2 ⟨u, hu⟩ : ℂ) = ψ t := by
    show ((ψ (∑ p : Fin 2 × Fin 2 with (p.2 : ℕ) = p.1 + 1, (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) k) p.1 p.2) : Circle) : ℂ) = _
    simp [Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  have hdet : GeneralLinearGroup.det u = 1 := by ext; simp [u]
  refine Submodule.Quotient.nontrivial_iff.1 h (eq_top_iff.2 fun v _ => ?_)
  have hne : (1 : ℂ) - ψ t ≠ 0 := sub_ne_zero.2 fun e => ht (Circle.ext e.symm)
  refine Submodule.subset_span ⟨⟨u, hu⟩, v / (1 - ψ t), ?_⟩
  rw [hw]
  show v = ofChar _ u _ - _
  rw [ofChar_apply, detChar_apply, hdet, map_one]
  simp only [Units.val_one, smul_eq_mul]
  field_simp


end GlobalTheory.LocGL.Tests
