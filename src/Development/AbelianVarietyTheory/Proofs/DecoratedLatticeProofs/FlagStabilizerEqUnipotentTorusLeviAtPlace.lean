module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IwaFlag

variable {D : D7}

theorem cA_mem_idAt' {v : Pl D} {y : AE D} (h : y ∈ idAt D (· = v)) : cA D y ∈ idAt D (· = v) := by
  obtain ⟨ε, -, hc, -, hε, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  rw [hε] at h ⊢
  have := congrArg (cA D) h
  rwa [map_mul, hc] at this

theorem mul_left_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} (A : Matrix (Fin l) (Fin m) R)
    {M : Matrix (Fin m) (Fin k) R} (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (A * M) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (h x j)

theorem mul_right_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} {M : Matrix (Fin l) (Fin m) R}
    (B : Matrix (Fin m) (Fin k) R) (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (M * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (h i x)

end GlobalTheory.IwaFlag

namespace GlobalTheory.IwaFlag

variable {D : D7}

end GlobalTheory.IwaFlag

end
