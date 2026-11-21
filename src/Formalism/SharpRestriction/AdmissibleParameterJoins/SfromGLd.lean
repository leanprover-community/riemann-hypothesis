import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.PrimeDegreeVariant

theorem del_int {N : ℕ} (lam : DomWeight N) :
    ∀ f0 ∈ delSq ℤ N lam, MvPolynomial.map (Int.castRingHom ℂ) f0 ∈ delSq ℂ N lam := by
  intro f0 hf0
  unfold delSq Formalism.GradedWeylDivisibility.weyl at hf0 ⊢
  induction hf0 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w, ?_⟩
    simp only
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  simp only [DomWeight.natW]
  omega

theorem del_eq_nabla {N : ℕ} (lam : DomWeight N) : delSq ℂ N lam = nablaSq ℂ N lam := by
  apply le_antisymm
  · exact Formalism.GradedWeylDivisibility.weylLeDual ℂ N N le_rfl lam.natW (natW_anti lam)
  · unfold nablaSq
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℂ N N lam.natW, Submodule.span_le]
    rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
    have h1 : Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I ∈ Formalism.GradedWeylDivisibility.dualWeyl ℤ N N lam.natW :=
      hsh ▸ Formalism.GradedWeylDivisibility.bidetMem ℤ N N K sz hsz I
    obtain ⟨c, hc, h2⟩ := Formalism.GradedWeylDivisibility.weylRational N N le_rfl lam.natW (natW_anti lam) _ h1
    have h3 := del_int lam _ h2
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
      Formalism.GradedWeylDivisibility.ldlat_map_bidet] at h3
    have hc' : ((Int.castRingHom ℂ) c) ≠ 0 := by simpa using hc
    have h4 := Submodule.smul_mem (delSq ℂ N lam) ((Int.castRingHom ℂ) c)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at h4

theorem del_stable {N : ℕ} (lam : DomWeight N) :
    ∀ g : GL (Fin N) ℂ, ∀ f ∈ delSq ℂ N lam, sqAct ℂ N lam g f ∈ delSq ℂ N lam := by
  intro g f hf
  rw [del_eq_nabla] at hf ⊢
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)


variable {D : D7} {u : D.what₂.Word}

def BrTie (P : product_first_zeroth_parts.Pend D u) : Prop :=
  ∀ τ io br, IsIota (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io →
    IsBr (product_first_zeroth_parts.Nm_succ D.R) (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) br →
    IsTranspose (product_first_zeroth_parts.lamTr D u τ) (product_first_zeroth_parts.sgTr D u τ) io br →
    Set.EqOn (P.br τ) br (delSq ℂ _ (product_first_zeroth_parts.lamTr D u τ) : Set _)


end Formalism.MainNotions.J

end
