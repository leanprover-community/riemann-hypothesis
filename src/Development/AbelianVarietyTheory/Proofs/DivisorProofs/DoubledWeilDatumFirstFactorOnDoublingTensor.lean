module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace DoublingFirstFactorDivisor
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.DoublingFirstFactor

theorem doubled_first_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  intro D ψ _ S T χS χT ω hω ωd hωd g f₁ f₂ h₁ h₂
  have key := ((GlobalTheory.DoublingTheta.thetaClause D ψ S T χS χT ω ωd hω hωd f₁ f₂ h₁ h₂).2 g 1 1).1
  have e : ω ((1 : GA D S), (1 : GA D T)) = 1 := map_one ω
  rw [key, e, map_one, map_one, inv_one, Circle.coe_one, one_smul]
  rfl

end GlobalTheory.CompanionTheory.DoublingFirstFactor

end

end DoublingFirstFactorDivisor
section


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledWeilDatum_firstFactor_on_doublingTensor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
    ∀ ωd : GA D (GlobalTheory.Doubling.dblSp S) × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO (GlobalTheory.Doubling.dblSp S) T → ℂ),
      Formalism.IndefR.Datum.IsWeilDatumO ψ (GlobalTheory.Doubling.dblSp S) T 1 χT ωd →
    ∀ (g : GA D S) (f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ),
      Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
      ωd (GlobalTheory.Doubling.io S (g, 1), 1) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T f₁ f₂) =
        GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (ω (g, 1) f₁) f₂ := by
  first | exact @DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | exact DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor | (intros; apply DoublingFirstFactorDivisor.GlobalTheory.CompanionTheory.DoublingFirstFactor.doubled_first_factor <;> assumption)

end
