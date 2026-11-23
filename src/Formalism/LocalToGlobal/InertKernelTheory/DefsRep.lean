module

public import Formalism.LocalToGlobal.InertKernelTheory.FirstKernelGeneratorOfOrthogonal
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ConditionIffAdditiveMaps
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.Rep

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top Formalism.L2.KerInert.K1
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC Frm thA thFOf)
open Formalism.MainNotions.FormalGroupSystem (Sys)

def CurveAt (l : ℕ) [Fact l.Prime] (be : MvPowerSeries (Fin 2) (K0 l)) (g2 g3 ε s2 : MaximalUnramifiedExtension l) : Prop :=
  ‖g2‖ ≤ 1 ∧ ‖g3‖ ≤ 1 ∧ ‖ε‖ = 1 ∧ (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) ∧
    (∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
      ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) ∧
    MvPowerSeries.constantCoeff be = 0 ∧
    ∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F ∧
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
        (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))

def OrthInt (l : ℕ) [Fact l.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension l) {ι : Type} [Fintype ι] [DecidableEq ι]
    (Th : MvPowerSeries (ι ⊕ ι) ℂ_[l]) : Prop :=
  ∃ (r : ℕ) (Θ : MvPowerSeries (Fin r) ℂ_[l]) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (f f' : ι → Fin r → MaximalUnramifiedExtension l),
    UnrOK (MaximalUnramifiedExtension l) l σ ∧ IsHypPair σ f f' ∧ Th = MvPowerSeries.subst (hypLin l f f') Θ ∧
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[l]) *
      @inParamK l _ (Fin r) ℂ_[l] _ (wittFractionAlgebraCp l) Θ)

section Glob

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

def thOrth (D : D7) {N N' r : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (c : ℂ_[p])
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (F₀ : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  MvPowerSeries.subst (fun k : D.what₂.Tau × Fin N' × Fin N =>
    ∑ i, MvPowerSeries.C (c * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) * MvPowerSeries.X i) F₀

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : Formalism.L2.G.Pend.CEmbC X.G)
    (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
    (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))
    (F : ∀ j, X.Lt j → X.Lt (j + 1) →
      MvPowerSeries (D.what₂.Tau × Fin ((X.Pj (j + 1)).m + 1) × Fin ((X.Pj j).m + 1)) ℂ_[p])

end Glob

def DictInt (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ) (c : ℂ_[p])
    (g2 g3 s2 ε : MaximalUnramifiedExtension p) : Prop :=
  ∃ (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]),
    Formalism.MainNotions.TaylorLogMetric.IsModel lam Λ C ∧ Formalism.MainNotions.TaylorLogMetric.IsWq (C • Formalism.MainNotions.TaylorLogMetric.wModel lam Λ) wq ∧
    ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
      (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]),
      Formalism.MainNotions.TaylorLogMetric.IntegralMv (Formalism.MainNotions.TaylorLogMetric.atLog D lam Λ C wq b G * Formalism.MainNotions.TaylorLogMetric.ePh lam Λ C wq r) →
      Integral (mvExp (Formalism.L2.Th1.E.phSum (phL p g2 g3 s2 ε) : MvPowerSeries (Fin r) ℂ_[p]) *
        @inParamK p _ (Fin r) ℂ_[p] _ (wittFractionAlgebraCp p) (thOrth D lam c b G))

end Formalism.L2.KerInert.Rep
