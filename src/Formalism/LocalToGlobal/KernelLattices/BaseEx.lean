module

public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.PeriodIntegrals.KerIso
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

noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.MainNotions

section HostFacts

variable (D : D7)

def thetaC : ℂ := (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2

def KQuad : Prop := Module.finrank ℚ D.host.K = 2

def ConjOnK : Prop := PI.KerIso.IsConj D.host.K D.host.conj

def TrPos : Prop := ∀ x : D.host.E, x ≠ 0 → 0 < Algebra.trace ℚ D.host.E (x * D.host.conj x)

def CardTau : Prop := Fintype.card D.what₂.Tau = Module.finrank D.host.K D.host.E

def EmbInj : Prop := Function.Injective (TaylorLogMetric.embT D)

def EmbOnK : Prop :=
  ∀ (τ : D.what₂.Tau) (k : D.host.K), TaylorLogMetric.embT D τ (algebraMap D.host.K D.host.E k) = D.host.φ₀ (k : D.host.E)

def PhiNonReal : Prop := ∃ k : D.host.K, (D.host.φ₀ (k : D.host.E)).im ≠ 0

def DMod8 : Prop := D.host.d % 8 = 7

def SqrtInK : Prop :=
  ∃ s : D.host.K, s * s = -(D.host.d : D.host.K) ∧
    D.host.conj (algebraMap D.host.K D.host.E s) = -algebraMap D.host.K D.host.E s

def LatStable : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), ∀ w ∈ TaylorLogMetric.lamOf D cc δ, thetaC D * w ∈ TaylorLogMetric.lamOf D cc δ

def ConjIdeal : Prop :=
  ∀ x : 𝓞 D.host.E, x ∈ D.host.conj • D.host.𝔟 ↔ ∃ y ∈ D.host.𝔟, D.host.conj (y : D.host.E) = (x : D.host.E)

def HostFacts : Prop :=
  KQuad D ∧ ConjOnK D ∧ TrPos D ∧ CardTau D ∧ EmbInj D ∧ EmbOnK D ∧ PhiNonReal D ∧ DMod8 D ∧ SqrtInK D ∧ LatStable D ∧ ConjIdeal D

def MMSelfDual : Prop := PI.KerIso.SelfDualI D.host.K D.host.conj D.host.AA0

def SplitKSplits : Prop := ∀ p : ℕ, p.Prime → SplitK D p → PI.KerIso.SplitsAt D.host.K D.host.conj p

def PeriodExists : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∃ L : PeriodPair, L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ

end HostFacts

end Formalism.L2.Ker
