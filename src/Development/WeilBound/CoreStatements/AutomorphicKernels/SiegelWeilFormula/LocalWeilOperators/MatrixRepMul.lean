module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD

variable (d : SD σ)

theorem incM_mul' {p : Type} [Fintype p] (M N : Matrix p p E) : incM F (M * N) = incM F M * incM F N := by
  unfold incM
  exact Matrix.map_mul

theorem incM_one' {p : Type} [DecidableEq p] : incM F (1 : Matrix p p E) = 1 := by
  unfold incM
  exact Matrix.map_one _ (map_zero _) (map_one _)

end SD

end PositivityTheory.SiegelWeilFormula

end
