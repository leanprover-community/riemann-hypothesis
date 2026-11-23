module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.DSExist
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Zuckerman
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeries₂.Poulsen
public import Formalism.PeriodIntegrals.DSInfCharCap
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.SubmatrixMemUJsetIff
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace BranchingSupport

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

def Hyps : Prop :=
  ThreeDimData.Inputs ∧ PI.SmoothCyc ∧ PI.DSInfCharCap.DSInfCharCap ∧ DSExist ∧ Zuckerman ∧ Poulsen ∧
    GlobalTheory.FormalDegree.HarishChandra

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def eZ {n : ℕ} (I : Finset (Fin n)) : Fin n → ℤ := fun i => if i ∈ I then 1 else 0

def n1 {n : ℕ} (x : Fin n → ℤ) : ℕ := ∑ i, (x i).natAbs

def IsCoef {k r : ℕ} (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) : Prop :=
  ∃ (m : ℕ) (x y : Fin m → R.H) (X : Fin m → (Wq →L[ℂ] Wp)), (∀ i, x i ∈ R.TK ∧ y i ∈ R.TK) ∧
    (∀ g ∈ GG k r, F g = ∑ i, ⟪x i, R.σ g (y i)⟫_ℂ • X i) ∧ s = ∑ i, ⟪l (x i), X i (l' (y i))⟫_ℂ

def Hsq (r : ℕ) (T b : ℝ) : ℝ := max 1 T * b ^ (20 * (r + 1))

def SideFam {k r : ℕ} [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r)
    (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) : Prop :=
  ∀ ν, n1 ν ≤ q0 → IsBeL (R ν) z π μW μN (l ν) ∧ 0 < dg ν ∧
    ∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH μG (R ν).σ w = dg ν

def Setup {k r : ℕ} [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r))
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) : Prop :=
  Num k r lam u b bv ga h q0 ∧ IsFam lam q0 R ∧ SideG k r z π u μW μN μG νq ∧ SideFam z π μW μN μG q0 R l dg

end BranchingSupport
