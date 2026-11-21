import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
import CompanionTheory.RealGroups.BaseChange.ArchimedeanBaseChange.TensorCompletions.SkewFieldFrames.CountLit

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_norm_class_count : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L], NumberField.IsTotallyReal K → NumberField.IsTotallyComplex L → ∀ x : GlobalTheory.QuadSymbol.FinFam K, GlobalTheory.QuadSymbol.AlmostNorm K L x → Nat.card {q : Kˣ ⧸ GlobalTheory.QuadSymbol.globalNorms K L // ∃ t : Kˣ, q = QuotientGroup.mk t ∧ ∀ u, x u / GlobalTheory.QuadSymbol.finDiag K t u ∈ GlobalTheory.QuadSymbol.normGroup K L (u.adicCompletion K)} * 2 = 2 ^ Fintype.card (InfinitePlace K) := by
  first | exact @GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two | exact GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two | (intros; apply GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two <;> assumption)
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.BCT.FacCl.main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → ∃ (ι : Type) (_ : Fintype ι) (K L : ι → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Field (L i)) (_ : ∀ i, NumberField (L i)) (_ : ∀ i, Algebra (K i) (L i)) (_ : ∀ i, Algebra.IsQuadraticExtension (K i) (L i)) (x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i)), Fintype.card ι = nfac P ∧ (∀ i, NumberField.IsTotallyReal (K i)) ∧ (∀ i, NumberField.IsTotallyComplex (L i)) ∧ (∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i)) ∧ ∑ i, Fintype.card (InfinitePlace (K i)) = n * Fintype.card (InfinitePlace E) ∧ Nonempty ({c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} ≃ ∀ i, {q : (K i)ˣ ⧸ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) // ∃ t : (K i)ˣ, q = QuotientGroup.mk t ∧ ∀ u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) t u ∈ GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i))}) :=
  CompanionTheory.Rg.BcB.G3.param_lit
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.twisted_class_count_torus_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → ∃ (ι : Type) (_ : Fintype ι) (K L : ι → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Field (L i)) (_ : ∀ i, NumberField (L i)) (_ : ∀ i, Algebra (K i) (L i)) (_ : ∀ i, Algebra.IsQuadraticExtension (K i) (L i)) (x : ∀ i, GlobalTheory.QuadSymbol.FinFam (K i)), Fintype.card ι = nfac P ∧ (∀ i, NumberField.IsTotallyReal (K i)) ∧ (∀ i, NumberField.IsTotallyComplex (L i)) ∧ (∀ i, GlobalTheory.QuadSymbol.AlmostNorm (K i) (L i) (x i)) ∧ ∑ i, Fintype.card (InfinitePlace (K i)) = n * Fintype.card (InfinitePlace E) ∧ Nonempty ({c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} ≃ ∀ i, {q : (K i)ˣ ⧸ GlobalTheory.QuadSymbol.globalNorms (K i) (L i) // ∃ t : (K i)ˣ, q = QuotientGroup.mk t ∧ ∀ u, x i u / GlobalTheory.QuadSymbol.finDiag (K i) t u ∈ GlobalTheory.QuadSymbol.normGroup (K i) (L i) (u.adicCompletion (K i))}) := by
  atlas_forward_decl GlobalTheory.BCT.FacCl.main
end

section
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.TwClassCount

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → Nat.card {c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} * 2 ^ nfac P = 2 ^ (n * Fintype.card (InfinitePlace E)) := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    GlobalTheory.T.twisted_class_count_torus_decomposition E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.T.almost_norm_class_count (K i) (L i) (hR i) (hC i) (x i) (hA i)

end GlobalTheory.BCT.TwClassCount
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.twisted_class_count_char_poly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ y : ∀ w : Pl E, GLw n w, (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) → (∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n) → Nat.card {c : TwCl (thE E n) // (c.rep * thE E n c.rep).val.charpoly = P ∧ ∀ w ∈ S, ∃ g, locEl n w c.rep = g⁻¹ * y w * thL n w g} * 2 ^ nfac P = 2 ^ (n * Fintype.card (InfinitePlace E)) := by
  atlas_forward_decl GlobalTheory.BCT.TwClassCount.main
end
