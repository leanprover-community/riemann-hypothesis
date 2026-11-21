import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
open Formalism.MainNotions.N

open scoped Matrix in
private theorem ker_pair {Γ K : Type} [Group Γ] [Field K] {a b : ℕ} (ρ : Γ →* GL (Fin a) K)
    (ρ' : Γ →* GL (Fin b) K) (s : Γ) (h : Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' s = 1) : ρ s = 1 ∧ ρ' s = 1 := by
  constructor
  · apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => funext fun i => ?_
    have h1 := GlobalTheory.EigTwist.sumRep_mulVec_inl ρ ρ' s (Sum.elim v 0 ∘ finSumFinEquiv.symm) i
    have e : (Sum.elim v (0 : Fin b → K) ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv ∘ Sum.inl = v := by
      funext j; simp
    rw [h, e, Units.val_one, Matrix.one_mulVec] at h1
    simpa using h1.symm
  · apply Units.ext
    rw [Units.val_one]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => funext fun i => ?_
    have h1 := GlobalTheory.EigTwist.sumRep_mulVec_inr ρ ρ' s (Sum.elim 0 v ∘ finSumFinEquiv.symm) i
    have e : (Sum.elim (0 : Fin a → K) v ∘ finSumFinEquiv.symm) ∘ finSumFinEquiv ∘ Sum.inr = v := by
      funext j; simp
    rw [h, e, Units.val_one, Matrix.one_mulVec] at h1
    simpa using h1.symm



