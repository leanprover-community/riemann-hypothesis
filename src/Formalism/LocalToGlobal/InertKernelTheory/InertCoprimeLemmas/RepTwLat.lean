module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.InertKernelTheory.DefsRepFrame
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DescentCore

@[expose] public section

noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepTwLat

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Defs

variable (D : D7)

def IntAtP (p : ℕ) (e : D.host.E) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def hStd {N : ℕ} (x y : Fin N → D.host.E) : D.host.E := ∑ k, D.host.conj (x k) * y k

def SelfDualP (p : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, IntAtP D p (hStd D x y)) ∧
  ∀ y : Fin N → D.host.E, (∀ x ∈ L, IntAtP D p (hStd D x y)) → ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • y ∈ L

def locSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Submodule R (Fin N → K) :=
  Submodule.span R ((fun x : Fin N → D.host.E => fun k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))

end Defs

section Ties

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Ties

section Glob

variable (D : D7) {p : ℕ} {N N' : ℕ}

end Glob

section Loc

variable (D : D7) {p : ℕ} {N N' : ℕ}

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

end Loc

section Main

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Main

end Formalism.L2.KerInert.RepTwLat

set_option pp.fullNames true
