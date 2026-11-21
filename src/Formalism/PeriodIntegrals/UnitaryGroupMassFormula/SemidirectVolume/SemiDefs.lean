import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def NormStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∀ h ∈ Hsub (AF F) σ J P, ∀ n ∈ FrameUnipotentSubgroup (AF F) σ J P, h * n * h⁻¹ ∈ FrameUnipotentSubgroup (AF F) σ J P

def ProjStep : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (r : ℕ) (P : Frame E M r) (T : F), 2 * r + 3 ≤ M → P.IsStd σ J T →
    ∃ π : S0 (AF F) σ J P →* Hsub (AF F) σ J P, Continuous π ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ Hsub (AF F) σ J P →
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) = s) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ FrameUnipotentSubgroup (AF F) σ J P → π s = 1) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) *
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J)⁻¹ ∈ FrameUnipotentSubgroup (AF F) σ J P) ∧
      (∀ s : S0 (AF F) σ J P, (s : HA (AF F) σ J) ∈ HFinIn (AF F) σ J →
        ((π s : Hsub (AF F) σ J P) : HA (AF F) σ J) ∈ HFinIn (AF F) σ J)

theorem heisenberg_le_stabilizer {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ}
    (P : Frame E M r) : Hsub R σ J P ≤ S0 R σ J P := by
  intro g hg
  rw [Hsub, mem_stabT] at hg
  rw [S0, mem_stabT]
  intro b
  have := hg (Fin.castAdd r b)
  simpa [tupH, Fin.append_left] using this


end PI.VolSemiDirect.W
