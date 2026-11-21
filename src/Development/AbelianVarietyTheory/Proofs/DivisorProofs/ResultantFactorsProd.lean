import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharFinprodLocKMulInfEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMInfinityComponentGlobalUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjResultantOfEllPolys
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOne

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finprod_locK_mul_inf_eq_one : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (k : Eˣ), (Function.mulSupport fun w : Pl E => χ.locK w k).Finite ∧ (∏ᶠ w : Pl E, χ.locK w k) * χ.inf k = 1 := by
  first | exact @GlobalTheory.HCharUnit.finprod_locK_mul_inf | exact GlobalTheory.HCharUnit.finprod_locK_mul_inf | (intros; apply GlobalTheory.HCharUnit.finprod_locK_mul_inf <;> assumption)
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_infinityComponent_globalUnit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ v : InfinitePlace E, (v.embedding (k : E) / (‖v.embedding (k : E)‖ : ℂ)) ^ e v := by
  first | exact @GlobalTheory.BCT.inf_mu_unit | exact GlobalTheory.BCT.inf_mu_unit | (intros; apply GlobalTheory.BCT.inf_mu_unit <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absHalf_eq_sqrt_norm (w : Pl E) {y : w.adicCompletion E} (hy : y ≠ 0) :
    absHalf w y = ((Real.sqrt ‖y‖ : ℝ) : ℂ) := by
  have hv : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  unfold absHalf
  congr 2
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, ordL, dif_neg hv, neg_neg]
  simp [qV]

theorem absHalf_prodFormula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E), x ≠ 0 →
    (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)).Finite ∧
      (∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x)) * ∏ v : InfinitePlace E, (‖v.embedding x‖ : ℂ) = 1 := by
  intro E _ _ _ x hx
  have key : ∀ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
      ((Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := fun w =>
    absHalf_eq_sqrt_norm w ((_root_.map_ne_zero _).mpr hx)
  have hfin : (Function.mulSupport fun w : Pl E => FinitePlace.mk w x).Finite := by
    have h0 := FinitePlace.hasFiniteMulSupport (K := E) hx
    have he : (fun w : Pl E => FinitePlace.mk w x) =
        (fun u : FinitePlace E => u x) ∘ FinitePlace.equivHeightOneSpectrum.symm := rfl
    rw [he, Function.mulSupport_comp_eq_preimage]
    exact Set.Finite.preimage (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn) h0
  have hsup : (Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x)) =
      Function.mulSupport fun w : Pl E => FinitePlace.mk w x := by
    ext w
    simp [Real.sqrt_eq_one]
  refine ⟨?_, ?_⟩
  · have hs : (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)) =
        Function.mulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
      ext w
      simp only [Function.mem_mulSupport, key, ne_eq, Complex.ofReal_eq_one]
    rw [hs, hsup]
    exact hfin
  · have hA : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) ^ 2 = ∏ᶠ w : Pl E, FinitePlace.mk w x := by
      have hfs : Function.HasFiniteMulSupport fun w : Pl E => Real.sqrt (FinitePlace.mk w x) := by
        unfold Function.HasFiniteMulSupport; rw [hsup]; exact hfin
      rw [finprod_pow hfs]
      congr 1
      funext w
      exact Real.sq_sqrt (apply_nonneg _ _)
    have hF : ∏ᶠ w : Pl E, FinitePlace.mk w x = ∏ᶠ u : FinitePlace E, u x :=
      finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm (f := fun u : FinitePlace E => u x)
    have hP : (∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = ∏ v : InfinitePlace E, v x ^ v.mult := by
      rw [← Finset.prod_pow]
      congr 1
      funext v
      rw [InfinitePlace.norm_embedding_eq, InfinitePlace.mult,
        if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
    have hprod := prod_abs_eq_one (K := E) hx
    have hsq : ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖) ^ 2 = 1 := by
      rw [mul_pow, hA, hP, hF, mul_comm]
      exact hprod
    have h1 : (∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x)) * ∏ v : InfinitePlace E, ‖v.embedding x‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (mul_nonneg (finprod_nonneg fun w => Real.sqrt_nonneg _)
        (Finset.prod_nonneg fun v _ => norm_nonneg _)) two_ne_zero).mp hsq
    have hc : ∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x) =
        ((∏ᶠ w : Pl E, Real.sqrt (FinitePlace.mk w x) : ℝ) : ℂ) := by
      simp_rw [key]
      exact (Complex.ofRealHom.toMonoidHom.map_finprod_of_injective Complex.ofReal_injective _).symm
    rw [hc]
    exact_mod_cast h1

end GlobalTheory.ProdForm
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prodFormula_sqrt_normalizedAbsValues_CMField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : E), x ≠ 0 → (Function.mulSupport fun w : Pl E => absHalf w (algebraMap E (w.adicCompletion E) x)).Finite ∧ (∏ᶠ w : Pl E, absHalf w (algebraMap E (w.adicCompletion E) x)) * ∏ v : InfinitePlace E, (‖v.embedding x‖ : ℂ) = 1 := by
  atlas_forward_decl GlobalTheory.ProdForm.absHalf_prodFormula
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_eq_finprod_mem_fibres_of_section :
    ∀ {α γ M : Type} [CommMonoid M] (p : α → γ) (S : Set α) (f : α → M),
      (∀ x, ∃! s, s ∈ S ∧ p s = p x) → (Function.mulSupport f).Finite →
        ∏ᶠ x, f x = ∏ᶠ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x := by
  intro α γ M _ p S f hS hf
  choose g hg using fun x => (hS x).exists
  have key : ∀ s ∈ S, ∀ x, p x = p s ↔ g x = s := by
    intro s hs x
    constructor
    · intro h
      exact (hS x).unique (hg x) ⟨hs, h.symm⟩
    · rintro rfl
      exact (hg x).2.symm
  set T := hf.toFinset with hT
  have hin : ∀ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x = ∏ x ∈ T with g x = s, f x := by
    intro s hs
    apply finprod_mem_eq_prod_of_subset
    · rintro x ⟨hx1, hx2⟩
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hT, Set.Finite.mem_toFinset]
      exact ⟨hx2, (key s hs x).1 hx1⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact (key s hs x).2 hx.2
  rw [finprod_mem_congr rfl hin, finprod_eq_prod_of_mulSupport_subset f (s := T) (by simp [hT])]
  rw [finprod_mem_eq_prod_of_subset (t := T.image g)]
  · exact (Finset.prod_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi) f).symm
  · rintro s ⟨_, hs⟩
    rw [Function.mem_mulSupport] at hs
    obtain ⟨u, hu, _⟩ := Finset.exists_ne_one_of_prod_ne_one hs
    rw [Finset.mem_filter] at hu
    rw [Finset.coe_image]
    exact ⟨u, hu.1, hu.2⟩
  · intro s hs
    rw [Finset.coe_image] at hs
    obtain ⟨u, _, rfl⟩ := hs
    exact (hg u).1

end GlobalTheory
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finprod_eq_finprod_mem_fibres_of_section' : ∀ {α γ M : Type} [CommMonoid M] (p : α → γ) (S : Set α) (f : α → M), (∀ x, ∃! s, s ∈ S ∧ p s = p x) → (Function.mulSupport f).Finite → ∏ᶠ x, f x = ∏ᶠ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x := by
  atlas_forward_decl GlobalTheory.finprod_eq_finprod_mem_fibres_of_section
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ProdForm
theorem resNe : ∀ (K : Type) [Field K] (P Q : K[X]), P.Monic → Q.Monic → IsCoprime P Q → resultant P Q ≠ 0 := by
  intro K _ P Q _ _ hc
  exact Polynomial.resultant_ne_zero P Q hc

theorem resMap : ∀ (K L : Type) [Field K] [Field L] (f : K →+* L) (P Q : K[X]),
    resultant (P.map f) (Q.map f) = f (resultant P Q) := by
  intro K L _ _ f P Q
  rw [Polynomial.natDegree_map, Polynomial.natDegree_map]
  exact Polynomial.resultant_map_map P Q _ _ f
end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

end GlobalTheory.ProdForm
end
end
