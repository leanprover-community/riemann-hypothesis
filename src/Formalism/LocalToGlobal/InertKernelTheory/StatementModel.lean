module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.KerInert

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

def GenusOneWittExists : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime (Ideal.absNorm cc) p → 5 ≤ p → InertK D p →
    ∀ lam : Qbar →+* ℂ_[p], ∃ g : G1 p, g.lam = lam ∧ At D cc δ g ∧ ModelOverW g.lam g.abelian₂ g.C

def EndIntInertAll : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p →
    ∀ α ∈ OKp D g.lam, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

def BiaddInertAll : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    Simeq (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2))

def PhNormOKInertAll : Prop :=
  ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p →
    ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
      Simeq (g.phAt (g.mulBy (tauK D g.lam (a : D.host.K)) (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (tauK D g.lam (a : D.host.K) * tauKc D g.lam (a : D.host.K)) * g.phAt (Xv ()))

end Formalism.L2.KerInert
