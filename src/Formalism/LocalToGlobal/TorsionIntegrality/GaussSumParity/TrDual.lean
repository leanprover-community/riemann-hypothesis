module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.IsLawOfLog
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
open scoped BigOperators

namespace Formalism.L2.Th1.D

open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2)

section Alg

variable {K : Type} [Field K]


open Classical in
def expF (K : Type) [Field K] (l : ℕ) : PowerSeries K :=
  if h : IsUnit (PowerSeries.coeff 1 (lgF K l)) then PowerSeries.substInvOfIsUnit (lgF K l) h else 0

def IsMul (l : ℕ) (c : K) (e : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff e = 0 ∧ PowerSeries.subst e (lgF K l) = PowerSeries.C c * lgF K l

def addC (l : ℕ) (be0 : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![at1 (0 : Fin 2) (expF K l), at1 (1 : Fin 2) (expF K l)] be0

variable {d : ℕ} [NeZero d]

def linE (σ : K →+* K) (c : K) : MvPowerSeries (ZMod d) K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then MvPowerSeries.C (σ^[s.val] c) * MvPowerSeries.X s else 0

def linO (σ : K →+* K) (c : K) : MvPowerSeries (ZMod d) K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then 0 else MvPowerSeries.C (σ^[s.val] c) * MvPowerSeries.X s

def beTil {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (om oms : ι → K) : MvPowerSeries (ZMod d) K :=
  ∑ r, MvPowerSeries.subst ![linE σ (oms r), linO σ (om r)] (addC l be0)

def beMean {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (om oms : ι → K) (ζ : K) : MvPowerSeries (ZMod d) K :=
  MvPowerSeries.C (((l ^ d - 1 : ℕ) : K)⁻¹) *
    ∑ k ∈ Finset.range (l ^ d - 1), MvPowerSeries.subst (torus l (ζ ^ k)) (beTil l σ be0 om oms)

def letLog (l : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0

def zXY {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (om oms : ι → K) (s : ZMod d) :
    MvPowerSeries (Bool × ι) K :=
  if s.val % 2 = 0 then ∑ r, MvPowerSeries.C (σ^[s.val] (om r)) * at1 (false, r) (lgF K l)
  else ∑ r, MvPowerSeries.C (σ^[s.val] (oms r)) * at1 (true, r) (lgF K l)

def mXY {ι : Type} (σ : K →+* K) (om oms : ι → K) (s : ZMod d) (x : Bool × ι) : K :=
  if s.val % 2 = 0 then (if x.1 = false then σ^[s.val] (om x.2) else 0)
  else (if x.1 = true then σ^[s.val] (oms x.2) else 0)

def beXY {ι : Type} [Fintype ι] (be0 : MvPowerSeries (Fin 2) K) : MvPowerSeries (Bool × ι) K :=
  ∑ r : ι, MvPowerSeries.subst
    ![(MvPowerSeries.X (false, r) : MvPowerSeries (Bool × ι) K), MvPowerSeries.X (true, r)] be0

def TrDual {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ) [NeZero d] (σ : K →+* K)
    (om oms : ι → K) : Prop :=
  2 * Fintype.card ι = d ∧
  ∀ r r' : ι, (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r * oms r') else 0) =
    if r = r' then 1 else 0

end Alg

section Normed

variable {K : Type} [NormedField K]

def F1 [CharZero K] (F be0 : MvPowerSeries (Fin 2) K) : Prop :=
  DivAB be0 ∧ Simeq (d1 F be0) 0 ∧ Simeq (d1 F (swap2 be0)) 0

def F2 [CharZero K] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α → ∀ e e' : PowerSeries K, IsMul l α e → IsMul l (σ α) e' →
    Simeq (MvPowerSeries.subst ![at1 (0 : Fin 2) e, MvPowerSeries.X 1] be0)
      (MvPowerSeries.subst ![MvPowerSeries.X 0, at1 (1 : Fin 2) e'] be0)

def OwOK {ι : Type} (d : ℕ) (σ : K →+* K) (om oms : ι → K) : Prop :=
  (∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1) ∧ ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r

end Normed

end Formalism.L2.Th1.D
