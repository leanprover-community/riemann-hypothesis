import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGLStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardLeUnramifiedTwistsCuspidalSupportJacquet

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_block_vector_jacquet_nonzero : GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (e : (Σ a : Fin (t + 1), Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) a)) ≃ Fin (r + t)) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), x ≠ 0 ∧ ∀ (j : Fin t) (g : GL (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) k), g ∈ GlobalTheory.SplitWeil.KO k (Fin ((Fin.cons r (fun _ => 1) : Fin (t + 1) → ℕ) j.succ)) → GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j.succ g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x := by
  first | exact @GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec | exact GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec | (intros; apply GlobalTheory.JacBlock.exists_jacquet_ne_zero_of_isBlockVec <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_le_unramifiedTwists_cuspidalSupport_jacquet : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s s' : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k n) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)) (d' : Fin s' → ℕ) (e : (Σ j, Fin (d' j)) ≃ Fin n) (A : Finset (Fin s')) (x : GlobalTheory.PRep.Jacquet π.π (GlobalTheory.SmGL.unipRad k e)), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) → (∀ j ∈ A, d' j = 1) → x ≠ 0 → (∀ j ∈ A, ∀ g ∈ GlobalTheory.SplitWeil.KO k (Fin (d' j)), GlobalTheory.SmGL.jac e π.π (Pi.mulSingle j g) x = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • x) → A.card ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  first | exact @GlobalTheory.JacSuppCount.card_le_ncard_unrTwist | exact GlobalTheory.JacSuppCount.card_le_ncard_unrTwist | (intros; apply GlobalTheory.JacSuppCount.card_le_ncard_unrTwist <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BlockSupp

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) ∧ t ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  intro hBZ hGL _ hDZ k _ _ _ _ r t χ π v hχs hχt hv hbv
  obtain ⟨s, d, σ, hsupp⟩ := GlobalTheory.T.exists_cuspidalSupport_irreducibleSmoothGL hBZ hGL k (r + t) π
  obtain ⟨e, x, hx, hxe⟩ := GlobalTheory.T.tame_block_vector_jacquet_nonzero hDZ k r t χ π v hχt hv hbv
  refine ⟨s, d, σ, hsupp, ?_⟩
  have h := GlobalTheory.T.card_le_unramifiedTwists_cuspidalSupport_jacquet hBZ hGL k (r + t) s (t + 1) χ π d σ _ e (Finset.univ.map (Fin.succEmb t)) x hχs hsupp
    (by intro j hj; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; rfl) hx
    (by intro j hj g hg; obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj; exact hxe i g hg)
  simpa using h

end GlobalTheory.BlockSupp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.SplitWeil.IsTame χ → v ≠ 0 → IsBlockVec χ π.π v → ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), GlobalTheory.SmGL.IsCuspSupport π.π d (fun a => (σ a).π) ∧ t ≤ Set.ncard {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (GlobalTheory.SmGL.detRep (Fin (d a)) (χ * GlobalTheory.SmGL.unrChar k α)))} := by
  atlas_forward_decl GlobalTheory.BlockSupp.main
end
