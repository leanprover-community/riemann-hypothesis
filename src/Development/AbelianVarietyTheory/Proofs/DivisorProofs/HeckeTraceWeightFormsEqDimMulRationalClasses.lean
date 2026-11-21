import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsEqDimMulKernelSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClasses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegral

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_geom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  rw [GlobalTheory.T.heckeTrace_forms_eq_dim_mul_kernelSum E hU n hn S hS lam K' hK f hf, GlobalTheory.T.kernelSum_eq_finsum_regular_rationalClasses E hU n hn S hS lam K' hK f hf hreg]
  congr 1
  unfold geomURat
  refine finsum_congr fun c => ?_
  split_ifs with h
  · rw [GlobalTheory.T.classSum_eq_mass_mul_orbitalIntegral E hU n hn S hS lam K' hK f hf c.rep h]; ring
  · rfl

end GlobalTheory.BCT
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  atlas_forward_decl GlobalTheory.BCT.trOn_forms_hop_eq_geom
