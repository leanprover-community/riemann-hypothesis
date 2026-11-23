module

public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionAlgebraCp
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.UniformGaussModelCondition
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

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert.K1

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.Th1.Top
open Formalism.L2.G.Pend (k0ToC wittFractionAlgebraCp OcC)
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF cob UnrOK IsLawOfLog)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def sumBe (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)) :
    MvPowerSeries (ι ⊕ ι) (K0 p) :=
  ∑ e : ι, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))

def FirstKernelGeneratorOfSum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (ι ⊕ ι) K1),
    BeProp p be →
    Formalism.MainNotions.FormalGroupSystem.Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be) :
      MvPowerSeries (ι ⊕ ι) (K0 p)) (sumBe p be) →
    IntR R1 (inParamK p K1 (Th * MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (sumBe p be)))) →
    ExtensionGeneratorCondition p K1 R1 be Th

def SumBeEven : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (ι : Type) [Fintype ι] (be : MvPowerSeries (Fin 2) (K0 p)),
    BeProp p be →
    Formalism.MainNotions.FormalGroupSystem.Simeq p (MvPowerSeries.subst (fun i => -MvPowerSeries.X i) (sumBe p be) :
      MvPowerSeries (ι ⊕ ι) (K0 p)) (sumBe p be)

def hypLin (l : ℕ) [Fact l.Prime] {ι n : Type} [Fintype ι] (f f' : ι → n → MaximalUnramifiedExtension l) (i : n) :
    MvPowerSeries (ι ⊕ ι) ℂ_[l] :=
  ∑ e : ι, (MvPowerSeries.C (f e i : ℂ_[l]) * MvPowerSeries.X (Sum.inl e) +
    MvPowerSeries.C (f' e i : ℂ_[l]) * MvPowerSeries.X (Sum.inr e))

def HypOfOrth : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε s2 : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (ι n : Type) [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (f f' : ι → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ be : MvPowerSeries (Fin 2) (K0 l), MvPowerSeries.constantCoeff be = 0 →
    Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.map (k0ToC l) (inParam l be))
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε))) →
  ∀ Θ : MvPowerSeries n ℂ_[l],
    Integral (mvExp (Formalism.L2.Th1.E.phSum (phL l g2 g3 s2 ε) : MvPowerSeries n ℂ_[l]) *
      @inParamK l _ n ℂ_[l] _ (wittFractionAlgebraCp l) Θ) →
    IntR (OcC l) (@inParamK l _ (ι ⊕ ι) ℂ_[l] _ (wittFractionAlgebraCp l)
      (MvPowerSeries.subst (hypLin l f f') Θ * MvPowerSeries.map (k0ToC l) (expS l (sumBe l be))))

end Formalism.L2.KerInert.K1
