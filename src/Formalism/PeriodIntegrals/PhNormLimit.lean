module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.PowerSeries.Substitution
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Classical

namespace PI.PhNormLimit

def IsIntP {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ‖x‖ ≤ 1

def IntegralMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, IsIntP (MvPowerSeries.coeff n F)

def expMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

section Ops

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def mulBy (l ex : PowerSeries ℂ_[p]) (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex

def phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst a ph

end Ops

def Target : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (T : Set (ℂ_[p] × ℂ_[p])),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    (∀ α ∈ T, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    (∀ α ∈ T, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))) →
    ∀ α ∈ closure T, Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))

end PI.PhNormLimit
