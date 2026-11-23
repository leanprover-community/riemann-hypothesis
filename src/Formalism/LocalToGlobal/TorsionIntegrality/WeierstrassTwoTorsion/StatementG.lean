module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CompInv
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

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

abbrev U₁ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0

abbrev U₂ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1

def FglMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    MvPowerSeries.map φ (fgl W) = fgl (W.map φ)

def FglChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    lam W * (U₂ - U₁) = (wSer W).subst (U₂ : MvPowerSeries (Fin 2) R) - (wSer W).subst (U₁ : MvPowerSeries (Fin 2) R) ∧
    MvPowerSeries.constantCoeff (uThird W) = 0 ∧
    wThird W = (wSer W).subst (uThird W) ∧
    fgl W = (iSer W).subst (uThird W) ∧
    MvPowerSeries.constantCoeff (fgl W) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (fgl W) = 1 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (fgl W) = 1

def FglSum : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K),
    Formalism.ELL.ChordAt W (wSer W) U₁ U₂ (fgl W)

def FglGroup : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ F : FormalGroup R, F.toPowerSeries = fgl W ∧ F.IsComm

def FglLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (fgl W) = (logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K) ∧
    fgl W = (expSer W).subst ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K))

def FglInv : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    MvPowerSeries.subst (![X, iSer W] : Fin 2 → R⟦X⟧) (fgl W) = 0

def ZSerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    (∀ n : ℤ, constantCoeff (zSer W n) = 0 ∧ coeff 1 (zSer W n) = (n : R)) ∧
    zSer W 0 = 0 ∧ zSer W 1 = X ∧ zSer W (-1) = iSer W ∧
    (∀ n : ℕ, zSer W (n : ℤ) = nSer W n) ∧
    (∀ m n : ℤ, MvPowerSeries.subst (![zSer W m, zSer W n] : Fin 2 → R⟦X⟧) (fgl W)
      = zSer W (m + n)) ∧
    (∀ m n : ℤ, (zSer W m).subst (zSer W n) = zSer W (m * n))

def ZSerMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (n : ℤ), PowerSeries.map φ (zSer W n) = zSer (W.map φ) n

def ZSerLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℤ),
    (logSer W).subst (zSer W n) = C (n : K) * logSer W

def HalfSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), IsUnit (2 : R) →
    constantCoeff (halfSer W) = 0 ∧ 2 * coeff 1 (halfSer W) = 1 ∧
    (nSer W 2).subst (halfSer W) = X ∧ (halfSer W).subst (nSer W 2) = X ∧
    MvPowerSeries.subst (![halfSer W, halfSer W] : Fin 2 → R⟦X⟧) (fgl W) = X

def HalfLog : Prop :=
  (∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    2 * (logSer W).subst (halfSer W) = logSer W) ∧
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    IsUnit (2 : R) → PowerSeries.map φ (halfSer W) = halfSer (W.map φ)

end Formalism.L2.Th1.A
