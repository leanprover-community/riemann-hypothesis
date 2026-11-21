import Mathlib
import Formalism.PeriodIntegrals.ParahoricIdxZ
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.LemmaU
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.MeasureUniformizerMatrixSetMulCard
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure

noncomputable section

open MeasureTheory Matrix ComplexConjugate Finset

namespace PI.ParahoricIdxZ.W

def IdxStep : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ (a t : ℕ) (J' : Subgroup (GL (Fin a) F)),
    Formalism.DoubleCosetMeasures.congSub O ϖ a ≤ J' → J' ≤ Formalism.DoubleCosetMeasures.GLint O a →
    ∀ (J : Subgroup (GL (Fin (a + t)) F)), (∀ A, A ∈ J ↔ blockCond O ϖ J' A) →
    (J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index *
        Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') *
        Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) ^ (a * t) * Nat.card (GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) =
      Nat.card (GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ))

def CardStep : Prop :=
  ∀ (F : Type) [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O), ϖ ≠ 0 → Formalism.DoubleCosetMeasures.IsLocalAt O ϖ →
    Finite (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : ℝ) =
      (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) : ℝ) ^ (n * n) * qE (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) 1 n




end PI.ParahoricIdxZ.W
