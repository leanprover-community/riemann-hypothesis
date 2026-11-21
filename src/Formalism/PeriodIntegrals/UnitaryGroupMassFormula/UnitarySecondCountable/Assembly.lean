import Mathlib
import Formalism.PeriodIntegrals.UMultOne

noncomputable section

namespace PI.UMultOne.UnitaryGroupMassFormula

open Matrix Set

instance unitaryGroup_compactSpace (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi univ fun _ : Fin m => Set.pi univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)

instance matrix_secondCountable (m : ℕ) : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))

instance unitaryGroup_secondCountable (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

def tr (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ → Matrix.unitaryGroup (Fin m) ℂ :=
  Matrix.UnitaryGroup.transpose

lemma tr_val (m : ℕ) (g : Matrix.unitaryGroup (Fin m) ℂ) :
    ((tr m g : Matrix.unitaryGroup (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ) =
      (g : Matrix (Fin m) (Fin m) ℂ)ᵀ := rfl


lemma tr_mul (m : ℕ) (x y : Matrix.unitaryGroup (Fin m) ℂ) : tr m (x * y) = tr m y * tr m x := by
  apply Subtype.ext
  simp only [tr_val, Matrix.UnitaryGroup.mul_val, Matrix.transpose_mul]

lemma tr_tr (m : ℕ) (x : Matrix.unitaryGroup (Fin m) ℂ) : tr m (tr m x) = x := by
  apply Subtype.ext
  simp only [tr_val, Matrix.transpose_transpose]

lemma emb_continuous (n : ℕ) (ι : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hι : ∀ g, ((ι g : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))) :
    Continuous ι := by
  apply continuous_induced_rng.2
  have h : (Subtype.val ∘ ι) = fun g : Matrix.unitaryGroup (Fin n) ℂ =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    funext g; exact hι g
  rw [h]
  exact (continuous_subtype_val.matrix_fromBlocks continuous_const continuous_const
    continuous_const).matrix_reindex _ _



end PI.UMultOne.UnitaryGroupMassFormula
