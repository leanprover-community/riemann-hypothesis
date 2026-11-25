module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.SnMass.SkewVol

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cm_sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem mem_range_of_cm_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hne := cm_sigma_ne_id h
  have hxS : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
  have hle : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) ≤ 2 := by
    rw [← Subalgebra.finrank_toSubmodule, ← h.2.2.1]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) := Module.finrank_pos
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    rcases (by omega : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 1 ∨
        Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 2) with h1 | h2
    · exact Subalgebra.finrank_eq_one_iff.1 h1
    · exfalso
      apply hne
      have htop : Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Subalgebra.finrank_toSubmodule, h2, h.2.2.1])
      ext z
      have hz : z ∈ Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) :=
        htop ▸ Submodule.mem_top
      exact hz
  rw [hS] at hxS
  exact Algebra.mem_bot.1 hxS

end Fixed

end GlobalTheory.SnMass.SkewVol
