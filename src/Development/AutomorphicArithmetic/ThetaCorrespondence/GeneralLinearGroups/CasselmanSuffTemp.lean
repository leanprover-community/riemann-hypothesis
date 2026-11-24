module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace UpperTheory.Lit.Cas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def jm {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) : ℕ∞ :=
  jhMult (piTensor fun a => (x a).rep) (jac (stdBlocks (fun a => (x a).1) hd) π)

def ScalarBy (x : IrrGL (k := k)) (t : kˣ) (c : ℂ) : Prop :=
  ∀ v, x.rep (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) v = c • v

def ExpStrict {h : ℕ} (x : Fin h → IrrGL (k := k)) : Prop :=
  ∀ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → ∀ c : Fin h → ℂ, (∀ i, ScalarBy (x i) t (c i)) →
    (∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), ‖c i‖ < 1) ∧ ∏ i, ‖c i‖ = 1

def ExpWeak {h : ℕ} (x : Fin h → IrrGL (k := k)) : Prop :=
  ∀ t : kˣ, Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → ∀ c : Fin h → ℂ, (∀ i, ScalarBy (x i) t (c i)) →
    (∀ j : Fin h, j.val + 1 < h → ∏ i ∈ Finset.univ.filter (· ≤ j), ‖c i‖ ≤ 1) ∧ ∏ i, ‖c i‖ = 1


variable (k) in
def CasselmanNecSq : Prop :=
  ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π →
      ∀ (h : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → jm x hd π ≠ 0 → ExpStrict x

def UnitaryCentral {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ (t : kˣ) (c : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → ‖c‖ = 1

def MaxExpWeak {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∀ (x : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ a, 0 < (x a).1) → jm x hd π ≠ 0 → ExpWeak x


variable (k) in
def CasselmanSuffTemp : Prop :=
  ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    1 ≤ N → IsSmooth π → π.IsIrreducible → UnitaryCentral π → MaxExpWeak π → IsTemperedCoeff π

end UpperTheory.Lit.Cas

end
