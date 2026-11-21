import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenspacesOfRingHomsIndependent

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem ringHom_independent_via_algebraMap :
    ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ],
      Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C),
        (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  intro C _ O _ _ Λ _ hinj S c hsum
  classical
  let φ : (Λ →+* O) → (Λ →* C) := fun σ => ((algebraMap O C).comp σ).toMonoidHom
  have hφ : Function.Injective φ := by
    intro σ τ h
    ext a
    apply hinj
    have := congrArg (fun f : Λ →* C => f a) h
    simpa [φ] using this
  have hli := (linearIndependent_monoidHom Λ C).comp φ hφ
  rw [linearIndependent_iff'] at hli
  intro σ hσ
  apply hli S c _ σ hσ
  funext a
  simpa [φ, Finset.sum_apply] using hsum a

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_homs_linearly_independent : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ], Function.Injective (algebraMap O C) → ∀ (S : Finset (Λ →+* O)) (c : (Λ →+* O) → C), (∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0) → ∀ σ ∈ S, c σ = 0 := by
  atlas_forward_decl GlobalTheory.ringHom_independent_via_algebraMap
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_eq_sum_eigenspaces : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite ∧ ∀ S : Finset (Λ →+* O), (∀ σ, eig C ρ σ ≠ ⊥ → σ ∈ S) → ∀ a : Λ, algebraMap O C (ρ a).trace = ∑ σ ∈ S, (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a) := by
  classical
  intro C _ O _ _ Λ _ h ρ hind htop
  have hfin : {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin, fun S hS a => ?_⟩
  set f : (Fin h → C) →ₗ[C] (Fin h → C) := Matrix.toLin' ((ρ a).map (algebraMap O C)) with hf
  have hact : ∀ (σ : Λ →+* O) (x : Fin h → C), x ∈ eig C ρ σ → f x = algebraMap O C (σ a) • x := by
    intro σ x hx
    have h1 := (Submodule.mem_iInf _).1 hx a
    exact Module.End.mem_eigenspace_iff.1 h1
  have hmaps : ∀ σ : Λ →+* O, Set.MapsTo f (eig C ρ σ) (eig C ρ σ) := by
    intro σ x hx
    have hx' : x ∈ eig C ρ σ := hx
    show f x ∈ eig C ρ σ
    rw [hact σ x hx']
    exact Submodule.smul_mem _ _ hx'
  have hint : DirectSum.IsInternal (fun σ : Λ →+* O => eig C ρ σ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htr := LinearMap.trace_eq_sum_trace_restrict' hint hfin hmaps
  have hrestrict : ∀ σ : Λ →+* O, LinearMap.trace C (eig C ρ σ) (f.restrict (hmaps σ))
      = (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a) := by
    intro σ
    have : f.restrict (hmaps σ) = algebraMap O C (σ a) • LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      show f x.1 = algebraMap O C (σ a) • x.1
      exact hact σ x.1 x.2
    rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  have hleft : algebraMap O C (ρ a).trace = LinearMap.trace C (Fin h → C) f := by
    rw [hf, Matrix.trace_toLin'_eq, Matrix.trace, Matrix.trace, map_sum]
    rfl
  rw [hleft, htr]
  simp only [hrestrict]
  refine Finset.sum_subset (fun σ hσ => hS σ (by simpa using hσ)) ?_
  intro σ _ hσ
  have hbot : eig C ρ σ = ⊥ := by
    by_contra hne
    exact hσ (by simpa using hne)
  rw [hbot]
  simp

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_eq_sum_eigen_multiplicities : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite ∧ ∀ S : Finset (Λ →+* O), (∀ σ, eig C ρ σ ≠ ⊥ → σ ∈ S) → ∀ a : Λ, algebraMap O C (ρ a).trace = ∑ σ ∈ S, (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a) := by
  atlas_forward_decl GlobalTheory.trace_eq_sum_eigenspaces
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem finrank_eig_eq_mul_of_trace_eq_mul :
    ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ]
      (h h' m : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (ρ' : Λ → Matrix (Fin h') (Fin h') O),
      Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C ρ σ) →
      (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) →
      (⨆ σ : Λ →+* O, eig C ρ' σ) = ⊤ → (∀ a, (ρ a).trace = (m : O) * (ρ' a).trace) →
      ∀ τ : Λ →+* O, Module.finrank C (eig C ρ τ) = m * Module.finrank C (eig C ρ' τ) := by
  intro C _ _ O _ _ Λ _ h h' m ρ ρ' hinj hind htop hind' htop' htr τ
  obtain ⟨hf, hsum⟩ := GlobalTheory.T.trace_eq_sum_eigen_multiplicities C O Λ h ρ hind htop
  obtain ⟨hf', hsum'⟩ := GlobalTheory.T.trace_eq_sum_eigen_multiplicities C O Λ h' ρ' hind' htop'
  classical
  let S : Finset (Λ →+* O) := insert τ (hf.toFinset ∪ hf'.toFinset)
  have hS : ∀ σ, eig C ρ σ ≠ ⊥ → σ ∈ S := fun σ hσ =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (hf.mem_toFinset.2 hσ))
  have hS' : ∀ σ, eig C ρ' σ ≠ ⊥ → σ ∈ S := fun σ hσ =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (hf'.mem_toFinset.2 hσ))
  let c : (Λ →+* O) → C := fun σ =>
    (Module.finrank C (eig C ρ σ) : C) - (m : C) * (Module.finrank C (eig C ρ' σ) : C)
  have key : ∀ a : Λ, ∑ σ ∈ S, c σ * algebraMap O C (σ a) = 0 := by
    intro a
    have e1 := hsum S hS a
    have e2 := hsum' S hS' a
    simp only [c, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rw [← e1, ← e2, htr a, map_mul, map_natCast, sub_self]
  have hc := GlobalTheory.T.ring_homs_linearly_independent C O Λ hinj S c key τ (Finset.mem_insert_self _ _)
  have : (Module.finrank C (eig C ρ τ) : C) = (m : C) * (Module.finrank C (eig C ρ' τ) : C) :=
    sub_eq_zero.1 hc
  exact_mod_cast this

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_decomposition_trace_multiple : ∀ (C : Type) [Field C] [CharZero C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h h' m : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O) (ρ' : Λ → Matrix (Fin h') (Fin h') O), Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → iSupIndep (fun σ : Λ →+* O => eig C ρ' σ) → (⨆ σ : Λ →+* O, eig C ρ' σ) = ⊤ → (∀ a, (ρ a).trace = (m : O) * (ρ' a).trace) → ∀ τ : Λ →+* O, Module.finrank C (eig C ρ τ) = m * Module.finrank C (eig C ρ' τ) := by
  atlas_forward_decl GlobalTheory.finrank_eig_eq_mul_of_trace_eq_mul
end

section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspaces_of_ring_homs_independent : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), Function.Injective (algebraMap O C) → iSupIndep (fun σ : Λ →+* O => eig C (⇑ρ) σ) := by
  first | exact @GlobalTheory.iSupIndep_eig | exact GlobalTheory.iSupIndep_eig | (intros; apply GlobalTheory.iSupIndep_eig <;> assumption)
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.RegEigen

theorem eig_leftMulMatrix_finrank : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O) (τ : Λ →+* O), τ.comp (algebraMap R Λ) = φ → Module.finrank C (eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ) = 1 := by
  intro C _ O _ _ R Λ _ _ _ n b φ τ hτ
  set ψ : R →+* C := (algebraMap O C).comp φ with hψ
  let f : (Fin n → C) → Λ → C := fun w x => ∑ i, ψ (b.repr x i) * w i
  have f_add : ∀ w x y, f w (x + y) = f w x + f w y := by
    intro w x y; simp [f, map_add, add_mul, Finset.sum_add_distrib]
  have f_smul : ∀ w (r : R) x, f w (r • x) = ψ r * f w x := by
    intro w r x; simp [f, map_mul, Finset.mul_sum, mul_assoc]
  have f_basis : ∀ w j, f w (b j) = w j := by
    intro w j; simp [f, Finsupp.single_apply]
  have f_sum : ∀ w (g : Fin n → Λ), f w (∑ i, g i) = ∑ i, f w (g i) := by
    intro w g
    exact map_sum (AddMonoidHom.mk' (f w) (f_add w)) g Finset.univ
  have mem : ∀ w, w ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ ↔
      ∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i := by
    intro w
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, funext_iff]
    refine forall_congr' fun a => forall_congr' fun i => ?_
    simp [f, Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul, hψ]
  have hτ' : ∀ r, τ (algebraMap R Λ r) = φ r := fun r => by rw [← hτ]; rfl
  set w0 : Fin n → C := fun i => algebraMap O C (τ (b i)) with hw0
  have f_w0 : ∀ x, f w0 x = algebraMap O C (τ x) := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    simp [f, hw0, map_sum, Algebra.smul_def, hτ', hψ]
  have f_mul : ∀ w, (∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i) →
      ∀ a x, f w (a * x) = algebraMap O C (τ a) * f w x := by
    intro w h a x
    conv_lhs => rw [← b.sum_repr x, Finset.mul_sum]
    rw [f_sum]
    simp_rw [mul_smul_comm, f_smul, h a]
    simp only [f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have cmHalfIntegralGenerator_mem_algebraicClosure : w0 ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ := by
    rw [mem]; intro a i; rw [f_w0]; simp [hw0]
  have w0_ne : w0 ≠ 0 := by
    intro h0
    have := f_w0 1
    rw [h0] at this
    simp [f] at this
  have heq : eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ = Submodule.span C {w0} := by
    apply le_antisymm
    · intro w hw
      rw [Submodule.mem_span_singleton]
      refine ⟨f w 1, funext fun i => ?_⟩
      have h := f_mul w ((mem w).1 hw) (b i) 1
      rw [mul_one, f_basis] at h
      simp [hw0, h, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact cmHalfIntegralGenerator_mem_algebraicClosure
  rw [heq, finrank_span_singleton w0_ne]

end GlobalTheory.RegEigen
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_mul_eigenspace_finrank_one : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O) (τ : Λ →+* O), τ.comp (algebraMap R Λ) = φ → Module.finrank C (eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ) = 1 := by
  atlas_forward_decl GlobalTheory.RegEigen.eig_leftMulMatrix_finrank
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem transposedRegularRep_ringHom_trace :
    ∀ (O : Type) [CommRing O] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ)
      (b : Module.Basis (Fin n) R Λ) (φ : R →+* O),
      (∃ ρ : Λ →+* Matrix (Fin n) (Fin n) O,
        ⇑ρ = fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) ∧
      ∀ a : Λ, (((Algebra.leftMulMatrix b a).transpose).map φ).trace
        = φ (Algebra.trace R Λ a) := by
  intro O _ R Λ _ _ _ n b φ
  refine ⟨⟨{ toFun := fun a => ((Algebra.leftMulMatrix b a).transpose).map φ
             map_one' := ?_
             map_mul' := ?_
             map_zero' := ?_
             map_add' := ?_ }, rfl⟩, ?_⟩
  · rw [map_one, Matrix.transpose_one]
    exact Matrix.map_one φ (map_zero φ) (map_one φ)
  · intro x y
    rw [mul_comm x y, map_mul, Matrix.transpose_mul, Matrix.map_mul]
  · ext i j
    simp
  · intro x y
    rw [map_add, Matrix.transpose_add]
    ext i j
    simp
  · intro a
    rw [Algebra.trace_eq_matrix_trace b a, ← Matrix.trace_transpose (Algebra.leftMulMatrix b a)]
    simp [Matrix.trace, map_sum]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.left_mul_matrix_ring_hom_trace : ∀ (O : Type) [CommRing O] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O), (∃ ρ : Λ →+* Matrix (Fin n) (Fin n) O, ⇑ρ = fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) ∧ ∀ a : Λ, (((Algebra.leftMulMatrix b a).transpose).map φ).trace = φ (Algebra.trace R Λ a) := by
  atlas_forward_decl GlobalTheory.transposedRegularRep_ringHom_trace
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

open Matrix

theorem jointEigen_ringHom_toIntegers (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (hv : v.Integers O)
    (ρ : Λ →+* Matrix (Fin h) (Fin h) O) (χ : Λ → C)
    (hne : (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) ≠ ⊥) :
    ∃ σ : Λ →+* O, ∀ a, algebraMap O C (σ a) = χ a := by
  obtain ⟨x, hxmem, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  set ψ : Λ →+* Matrix (Fin h) (Fin h) C := (algebraMap O C).mapMatrix.comp ρ with hψ
  have hψa : ∀ a, (ρ a).map (algebraMap O C) = ψ a := fun a => rfl
  have hE : ∀ a, ψ a *ᵥ x = χ a • x := by
    intro a
    have := (Submodule.mem_iInf _).1 hxmem a
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hψa] at this
    exact this
  have canc : ∀ c d : C, c • x = d • x → c = d := fun c d hcd => smul_left_injective C hx0 hcd
  have h1 : χ 1 = 1 := canc _ _ (by rw [← hE, map_one, Matrix.one_mulVec, one_smul])
  have hadd : ∀ a b, χ (a + b) = χ a + χ b := fun a b =>
    canc _ _ (by rw [← hE, map_add, Matrix.add_mulVec, hE, hE, add_smul])
  have hmul : ∀ a b, χ (a * b) = χ a * χ b := fun a b =>
    canc _ _ (by rw [← hE, map_mul, ← Matrix.mulVec_mulVec, hE, Matrix.mulVec_smul, hE, smul_smul, mul_comm])
  have h0 : χ 0 = 0 := canc _ _ (by rw [← hE, map_zero, Matrix.zero_mulVec, zero_smul])

  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx0 (funext hcon)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => v (x j)) ⟨i0, Finset.mem_univ _⟩
  have hvi : v (x i) ≠ 0 := by
    intro h'
    have := hi i0 (Finset.mem_univ _)
    rw [h'] at this
    exact hi0 ((Valuation.zero_iff v).1 (le_antisymm this (zero_le')))
  have hint : ∀ a, v (χ a) ≤ 1 := by
    intro a
    have hrow : χ a * x i = ∑ j, ψ a i j * x j := by
      have := congrFun (hE a) i
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]; rfl
    have hle : v (χ a * x i) ≤ v (x i) := by
      rw [hrow]
      apply Valuation.map_sum_le
      intro j _
      rw [map_mul]
      calc v (ψ a i j) * v (x j) ≤ 1 * v (x i) := by
            apply mul_le_mul' _ (hi j (Finset.mem_univ _))
            exact hv.map_le_one _
        _ = v (x i) := one_mul _
    rw [map_mul] at hle
    have hpos : 0 < v (x i) := lt_of_le_of_ne (zero_le') (Ne.symm hvi)
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos
  choose σf hσf using fun a => hv.exists_of_le_one (hint a)
  refine ⟨{ toFun := σf, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hσf⟩
  · exact hv.hom_inj (by rw [hσf, h1, map_one])
  · intro a b; exact hv.hom_inj (by rw [hσf, map_mul, hσf, hσf, hmul])
  · exact hv.hom_inj (by rw [hσf, h0, map_zero])
  · intro a b; exact hv.hom_inj (by rw [hσf, map_add, hσf, hσf, hadd])

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_hom_of_joint_eigenvalue : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ), v.Integers O → ∀ (ρ : Λ →+* Matrix (Fin h) (Fin h) O) (χ : Λ → C), (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) ≠ ⊥ → ∃ σ : Λ →+* O, ∀ a, algebraMap O C (σ a) = χ a := by
  atlas_forward_decl GlobalTheory.jointEigen_ringHom_toIntegers
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem iSup_jointEigenspace_eq_top_of_separable : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : Type) [AddCommGroup V] [Module C V] [FiniteDimensional C V] (I : Type) (T : I → Module.End C V), (∀ a b, Commute (T a) (T b)) → (∀ a, ∃ f : Polynomial C, f.Separable ∧ Polynomial.aeval (T a) f = 0) → (⨆ χ : I → C, ⨅ a : I, Module.End.eigenspace (T a) (χ a)) = ⊤ := by
  intro C _ _ V _ _ _ I T hc hs
  have hmax : ∀ a μ, (T a).maxGenEigenspace μ = (T a).eigenspace μ := by
    intro a μ
    obtain ⟨f, hf, h0⟩ := hs a
    exact (Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.squarefree h0).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have hcomm : Pairwise fun i j => Commute (T i) (T j) := fun i j _ => hc i j
  have hdiag : ∀ a, ⨆ μ, (T a).maxGenEigenspace μ = ⊤ := fun a =>
    Module.End.iSup_maxGenEigenspace_eq_top (T a)
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute T hcomm hdiag
  simpa only [hmax] using htop

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_semisimple_eigenspaces_span : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : Type) [AddCommGroup V] [Module C V] [FiniteDimensional C V] (I : Type) (T : I → Module.End C V), (∀ a b, Commute (T a) (T b)) → (∀ a, ∃ f : Polynomial C, f.Separable ∧ Polynomial.aeval (T a) f = 0) → (⨆ χ : I → C, ⨅ a : I, Module.End.eigenspace (T a) (χ a)) = ⊤ := by
  atlas_forward_decl GlobalTheory.iSup_jointEigenspace_eq_top_of_separable
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem action_commute_and_killed_by_polynomials
    (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ)
    (R : Type) [CommRing R] [Algebra R Λ] (φ : R →+* O)
    (ρ : Λ →+* Matrix (Fin h) (Fin h) O)
    (hρ : ∀ c : R, ρ (algebraMap R Λ c) = φ c • (1 : Matrix (Fin h) (Fin h) O)) :
    (∀ a b : Λ, Commute (Matrix.toLin' ((ρ a).map (algebraMap O C)))
      (Matrix.toLin' ((ρ b).map (algebraMap O C)))) ∧
    ∀ (a : Λ) (f : Polynomial R), Polynomial.aeval a f = 0 →
      Polynomial.aeval (Matrix.toLin' ((ρ a).map (algebraMap O C)))
        (f.map ((algebraMap O C).comp φ)) = 0 := by
  let Φ : Λ →+* Module.End C (Fin h → C) :=
    ((Matrix.toLinAlgEquiv' (R := C) (n := Fin h)).toRingEquiv.toRingHom).comp
      (((algebraMap O C).mapMatrix).comp ρ)
  have hΦ : ∀ a, Matrix.toLin' ((ρ a).map (algebraMap O C)) = Φ a := fun a => by
    ext i j
    simp [Φ, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  have hscal : (algebraMap C (Module.End C (Fin h → C))).comp ((algebraMap O C).comp φ)
      = Φ.comp (algebraMap R Λ) := by
    ext c : 1
    show _ = Φ (algebraMap R Λ c)
    rw [RingHom.comp_apply, ← hΦ, hρ]
    ext i j
    simp [Matrix.toLin'_apply, Matrix.one_apply, Pi.single_apply, Module.algebraMap_end_apply,
      Matrix.map_apply, Matrix.mulVec]
    split_ifs <;> simp
  refine ⟨fun a b => ?_, fun a f hf => ?_⟩
  · rw [hΦ, hΦ]
    exact (Commute.all a b).map Φ
  · rw [hΦ, Polynomial.aeval_def, Polynomial.eval₂_map, hscal, ← Polynomial.hom_eval₂,
      ← Polynomial.aeval_def, hf, map_zero]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_rep_commute_and_annihilate : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (R : Type) [CommRing R] [Algebra R Λ] (φ : R →+* O) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (∀ c : R, ρ (algebraMap R Λ c) = φ c • (1 : Matrix (Fin h) (Fin h) O)) → (∀ a b : Λ, Commute (Matrix.toLin' ((ρ a).map (algebraMap O C))) (Matrix.toLin' ((ρ b).map (algebraMap O C)))) ∧ ∀ (a : Λ) (f : Polynomial R), Polynomial.aeval a f = 0 → Polynomial.aeval (Matrix.toLin' ((ρ a).map (algebraMap O C))) (f.map ((algebraMap O C).comp φ)) = 0 := by
  atlas_forward_decl GlobalTheory.action_commute_and_killed_by_polynomials
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem exists_poly_aeval_eq_zero_map_separable :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (φ : ℤ_[p] →+* C) (Λ : Type)
      [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
      [FaithfulSMul ℤ_[p] Λ] (a : Λ),
      ∃ f : Polynomial ℤ_[p], Polynomial.aeval a f = 0 ∧ (f.map φ).Separable := by
  intro p _ C _ _ φ Λ _ _ _ _ _ a
  have hint : IsIntegral ℤ_[p] a := Algebra.IsIntegral.isIntegral a
  refine ⟨minpoly ℤ_[p] a, minpoly.aeval _ _, ?_⟩
  have hirr : Irreducible ((minpoly ℤ_[p] a).map (algebraMap ℤ_[p] ℚ_[p])) :=
    ((minpoly.monic hint).irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).1
      (minpoly.irreducible hint)
  have hsep := hirr.separable
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have hs := PadicInt.unitCoeff_spec h
    rw [hs, map_mul, map_pow, map_natCast] at hx
    rcases mul_eq_zero.1 hx with h1 | h1
    · exact (((PadicInt.unitCoeff h).isUnit).map φ).ne_zero h1
    · exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) h1
  let ψ : ℚ_[p] →+* C := IsFractionRing.lift (K := ℚ_[p]) hinj
  have hcomp : ψ.comp (algebraMap ℤ_[p] ℚ_[p]) = φ := by
    ext x
    exact IsFractionRing.lift_algebraMap hinj x
  have := hsep.map (f := ψ)
  rwa [Polynomial.map_map, hcomp] at this

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_annihilating_poly : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (φ : ℤ_[p] →+* C) (Λ : Type) [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (a : Λ), ∃ f : Polynomial ℤ_[p], Polynomial.aeval a f = 0 ∧ (f.map φ).Separable := by
  atlas_forward_decl GlobalTheory.exists_poly_aeval_eq_zero_map_separable
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem padicInt_ringHom_ext_of_separated (p : ℕ) [Fact p.Prime] (R : Type) [Ring R]
    (hsep : ∀ x : R, (∀ n : ℕ, ∃ y : R, x = (p : R) ^ n * y) → x = 0) :
    ∀ f g : ℤ_[p] →+* R, f = g := by
  intro f g
  ext c
  have key : f c - g c = 0 := by
    apply hsep
    intro n
    have h := PadicInt.appr_spec n c
    rw [Ideal.mem_span_singleton'] at h
    obtain ⟨c', hc'⟩ := h
    refine ⟨f c' - g c', ?_⟩
    have hc : c = (c.appr n : ℤ_[p]) + c' * (p : ℤ_[p]) ^ n := by rw [hc']; ring
    rw [hc, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    have hcomm1 : f c' * (p : R) ^ n = (p : R) ^ n * f c' := ((Nat.cast_commute p (f c')).pow_left n).symm
    have hcomm2 : g c' * (p : R) ^ n = (p : R) ^ n * g c' := ((Nat.cast_commute p (g c')).pow_left n).symm
    rw [hcomm1, hcomm2, mul_sub]
    abel
  exact sub_eq_zero.mp key

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ring_hom_from_padic_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [Ring R], (∀ x : R, (∀ n : ℕ, ∃ y : R, x = (p : R) ^ n * y) → x = 0) → ∀ f g : ℤ_[p] →+* R, f = g := by
  atlas_forward_decl GlobalTheory.padicInt_ringHom_ext_of_separated
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eq_zero_of_infinitely_p_divisible (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (x : O)
    (hx : ∀ n : ℕ, ∃ y : O, x = (p : O) ^ n * y) : x = 0 := by
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) x
  intro n
  obtain ⟨y, hy⟩ := hx n
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, hy]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem padic_ringHom_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], (∀ f : ℤ_[p] →+* O, f = padicToO p O) ∧ ∀ (h : ℕ) (f : ℤ_[p] →+* Matrix (Fin h) (Fin h) O) (c : ℤ_[p]), f c = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) := by
  intro p _ O _ _ _
  refine ⟨fun f => GlobalTheory.T.ring_hom_from_padic_unique_of_sep p O (eq_zero_of_infinitely_p_divisible p O) f _, fun h f c => ?_⟩
  have hsep : ∀ x : Matrix (Fin h) (Fin h) O,
      (∀ n : ℕ, ∃ y : Matrix (Fin h) (Fin h) O, x = ((p : ℕ) : Matrix (Fin h) (Fin h) O) ^ n * y) → x = 0 := by
    intro x hx
    ext i j
    apply eq_zero_of_infinitely_p_divisible p O
    intro n
    obtain ⟨y, hy⟩ := hx n
    refine ⟨y i j, ?_⟩
    rw [hy, ← Nat.cast_pow, ← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul, Nat.cast_pow]
  have := GlobalTheory.T.ring_hom_from_padic_unique_of_sep p (Matrix (Fin h) (Fin h) O) hsep f
    ((algebraMap O (Matrix (Fin h) (Fin h) O)).comp (padicToO p O))
  rw [this, RingHom.comp_apply, Algebra.algebraMap_eq_smul_one]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padic_ring_hom_unique_adic_complete : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], (∀ f : ℤ_[p] →+* O, f = padicToO p O) ∧ ∀ (h : ℕ) (f : ℤ_[p] →+* Matrix (Fin h) (Fin h) O) (c : ℤ_[p]), f c = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) := by
  atlas_forward_decl GlobalTheory.padic_ringHom_unique
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem eigenspaces_span_of_integral_action : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (⨆ σ : Λ →+* O, eig C (⇑ρ) σ) = ⊤ := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ h ρ
  have hscal : ∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = padicToO p O c • (1 : Matrix (Fin h) (Fin h) O) :=
    fun c => (GlobalTheory.T.padic_ring_hom_unique_adic_complete p O).2 h (ρ.comp (algebraMap ℤ_[p] Λ)) c
  have hkill := GlobalTheory.T.scalar_rep_commute_and_annihilate C O Λ h ℤ_[p] (padicToO p O) ρ hscal
  have hdiag := GlobalTheory.T.commuting_semisimple_eigenspaces_span C (Fin h → C) Λ
    (fun a => Matrix.toLin' ((ρ a).map (algebraMap O C))) hkill.1 (fun a => by
      obtain ⟨f, hf, hsep⟩ := GlobalTheory.T.exists_separable_annihilating_poly p C ((algebraMap O C).comp (padicToO p O)) Λ a
      exact ⟨f.map ((algebraMap O C).comp (padicToO p O)), hsep, hkill.2 a f hf⟩)
  refine eq_top_iff.2 (hdiag ▸ iSup_le fun χ => ?_)
  by_cases hne : (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) = ⊥
  · rw [hne]; exact bot_le
  · obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_ring_hom_of_joint_eigenvalue C v O Λ h hv ρ χ hne
    have hχ : χ = fun a => algebraMap O C (σ a) := funext fun a => (hσ a).symm
    subst hχ
    exact le_iSup_of_le σ le_rfl

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_rep_eigenspaces_span_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (⨆ σ : Λ →+* O, eig C (⇑ρ) σ) = ⊤ := by
  atlas_forward_decl GlobalTheory.eigenspaces_span_of_integral_action
end

section
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem finrank_eig_of_trace_eq_mul_trace : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (∀ a, (ρ a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a)) → ∀ τ : Λ →+* O, Module.finrank C (eig C (⇑ρ) τ) = N := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _ N h ρ hρ τ
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : Module.Free ℤ_[p] Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ_[p] Λ
  obtain ⟨⟨ρ', hρ'⟩, htr⟩ := GlobalTheory.T.left_mul_matrix_ring_hom_trace O ℤ_[p] Λ _ b (padicToO p O)
  have key := GlobalTheory.T.eigen_decomposition_trace_multiple C O Λ h _ N (⇑ρ) (⇑ρ') hinj
    (GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ h ρ hinj)
    (GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ h ρ)
    (GlobalTheory.T.eigenspaces_of_ring_homs_independent C O Λ _ ρ' hinj)
    (GlobalTheory.T.dvr_rep_eigenspaces_span_top p C v O hv Λ _ ρ')
    (fun a => by rw [hρ a, hρ', htr a]) τ
  have hτ : τ.comp (algebraMap ℤ_[p] Λ) = padicToO p O := (GlobalTheory.T.padic_ring_hom_unique_adic_complete p O).1 _
  have one := GlobalTheory.T.left_mul_eigenspace_finrank_one C O ℤ_[p] Λ _ b (padicToO p O) τ hτ
  rw [key, hρ', one, mul_one]

end GlobalTheory
end

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rep_trace_eq_mul_algebra_trace_dvr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ) (ρ : Λ →+* Matrix (Fin h) (Fin h) O), (∀ a, (ρ a).trace = (N : O) * padicToO p O (Algebra.trace ℤ_[p] Λ a)) → ∀ τ : Λ →+* O, Module.finrank C (eig C (⇑ρ) τ) = N := by
  atlas_forward_decl GlobalTheory.finrank_eig_of_trace_eq_mul_trace
end
