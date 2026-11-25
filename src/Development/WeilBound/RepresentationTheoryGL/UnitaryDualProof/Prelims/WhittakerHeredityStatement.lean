module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

theorem _root_.GlobalTheory.T.whittaker_heredity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.whitHeredity | exact GlobalTheory.CompanionTheory.Rodier.whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Rodier.whitHeredity <;> assumption)
