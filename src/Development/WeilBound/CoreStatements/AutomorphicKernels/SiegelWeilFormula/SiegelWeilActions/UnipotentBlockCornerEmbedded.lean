module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PartialDerivativeAlgebra
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ShiftCoordinatesColumn
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.SigmaSigmaOfGood
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.G2HaarMeasure.ContinuousInFrame
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem fixed_in_F (hcm : IsCMExt F E σ) (z : E) (hz : σ z = z) : ∃ f : F, algebraMap F E f = z := by
  obtain ⟨_, htc, hdeg, hconj⟩ := hcm
  classical
  have hz' : z ∈ AlgHom.equalizer σ (AlgHom.id F E) := (AlgHom.mem_equalizer _ _ _).2 hz
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    have hp : (Module.finrank F E).Prime := by
      rw [hdeg]
      exact Nat.prime_two
    have := Subalgebra.isSimpleOrder_of_finrank_prime F E hp
    rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h | h
    · exact h
    · exfalso
      have hid : ∀ x, σ x = x := fun x => by
        have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h ▸ Algebra.mem_top
        exact (AlgHom.mem_equalizer _ _ _).1 hx
      obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace E) := inferInstance
      have hreal : NumberField.ComplexEmbedding.IsReal w.embedding := by
        rw [NumberField.ComplexEmbedding.isReal_iff]
        ext x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
        have hx := hconj w.embedding x
        rw [hid x] at hx
        exact hx.symm
      exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (htc.isComplex w))
        (NumberField.InfinitePlace.isReal_iff.2 hreal)
  rw [hS] at hz'
  exact Algebra.mem_bot.1 hz'

end PositivityTheory.SiegelWeilFormula.Act.C6

end
