module

public import Formalism.EllipticTorsion.WSeriesUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

def WEqAt {R : Type u} [CommRing R] (W : WeierstrassCurve R) {σ : Type}
    (s v : MvPowerSeries σ R) : Prop :=
  v = s ^ 3 + W.a₁ • (s * v) + W.a₂ • (s ^ 2 * v) + W.a₃ • v ^ 2 + W.a₄ • (s * v ^ 2)
      + W.a₆ • v ^ 3

def WSubstUnique : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (w : PowerSeries R), WFixed W w →
    ∀ (σ : Type) [Finite σ] (s : MvPowerSeries σ R), MvPowerSeries.constantCoeff s = 0 →
      WEqAt W s (w.subst s) ∧
      ∀ v : MvPowerSeries σ R, MvPowerSeries.constantCoeff v = 0 → WEqAt W s v → v = w.subst s

def ChordAt {K : Type u} [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) {σ : Type}
    (s t r : MvPowerSeries σ K) : Prop :=
  let W' := (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine
  let ℓ := (yOf w s - yOf w t) / (xOf w s - xOf w t)
  xOf w r = W'.addX (xOf w s) (xOf w t) ℓ ∧ yOf w r = W'.addY (xOf w s) (xOf w t) (yOf w s) ℓ

def WChordSeries : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∃ F₂ : MvPowerSeries (Fin 2) K,
      (∀ d, MvPowerSeries.coeff d F₂ ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) ∧
      MvPowerSeries.constantCoeff F₂ = 0 ∧
      MvPowerSeries.coeff (Finsupp.single 0 1) F₂ = 1 ∧ MvPowerSeries.coeff (Finsupp.single 1 1) F₂ = 1 ∧
      ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂

def WChordSubst : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K), WFixed W w →
    ∀ F₂ : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F₂ = 0 →
      ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂ →
      ∀ (σ : Type) [Finite σ] (s t : MvPowerSeries σ K),
        MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff t = 0 → s ≠ 0 → t ≠ 0 →
        xOf w s ≠ xOf w t → ChordAt W w s t (MvPowerSeries.subst ![s, t] F₂)

end Formalism.ELL
