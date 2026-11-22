module

public import Formalism.LocalToGlobal.Divisibility.JetBounds.Statement
public import Formalism.GaussJetBounds.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.FinalFree
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.HasSubstBlock
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.GramFrameCompositionMvExpFact
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.IntOpTwoFreeOf
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Inertia
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.AgreeOnAdjoin
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenCompatOf
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFrameEOf
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Tensor
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.EigenFinal

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (OwOK TrDual beMean xOfZ sumE phFF thetaS NormRel expF PV)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob at1)

def CurveAt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) : Prop :=
  5 ≤ l ∧ ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsLawOfLog l F ∧
    (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) ∧
    ‖(g2 : ℂ_[l]) ^ 3 - 27 * (g3 : ℂ_[l]) ^ 2‖ = 1

def HostInt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {n : Type} [Fintype n] (Θ : MvPowerSeries n ℂ_[l]) : Prop :=
  Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum (Formalism.L2.Th1.Top.phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) * Θ)

end Formalism.L2.DIV.C
