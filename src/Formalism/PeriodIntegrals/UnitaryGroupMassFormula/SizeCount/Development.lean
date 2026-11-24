module

public import Formalism.LocalRingCardinality.DataErr
public import Formalism.LocalRingCardinality.DataParams
public import Formalism.SharpRestriction.ElevenLe
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

def RowA : Prop :=
  ∀ (D : D7) (L : SizeData₂ D), ∀ j ∈ SizeData₂.lifts D, ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    nuAbs D u j τ - (DV.nuRow D u j τ 0 - DV.nuRow D u j τ 1) ≤
      (D.R.k : ℝ) * (L.Sc + wj D j τ) + 2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz

def RowB : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_P : ParameterChoice' D L), ∀ j ∈ SizeData₂.lifts D, ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    nuAbs D u j τ ≤ ((D.R.k : ℝ) + 2) * L.Sc + (D.R.k : ℝ) * wj D j τ +
      2 * (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz

def RowC : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_P : ParameterChoice' D L), ∀ j ∈ SizeData₂.lifts D, ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    (D.eTau τ : D.R.GG) ∉ D.host.topPlaces →
    DV.nuRow D u j τ 0 ≤ 3 * L.Sc + wj D j τ

def SizeFacts : Prop :=
  ∀ (D : D7) (L : SizeData₂ D), Formalism.MainNotions.SizesAt L → 3 ≤ L.sc.x →
    (∀ t : D.host.TT, (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b') ∧
    L.etaSz ≤ L.sc.w'' D.R.n / L.sc.x ∧
    (D.R.k : ℝ) * L.Sc ≤ L.sc.w'' D.R.n ∧
    L.sc.w'' D.R.n ≤ L.sc.b' / L.sc.x ∧
    (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ L.sc.w'' D.R.n ∧
    1 ≤ L.sc.b ∧ 0 ≤ L.sc.b'

def PlaceFacts : Prop :=
  ∀ D : D7,
    (∀ t : HH D, (D.eTau (tauPl D (false, t)) : D.R.GG) = D.R.tau1 t) ∧
    (∀ t : HH D, t ∉ D.host.TT → D.host.IsThin (D.eTau (tauPl D (false, t)) : D.R.GG)) ∧
    (∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) ∉ D.host.topPlaces) ∧
    (∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) ∈ D.host.thickPlaces ∨
      D.host.IsThin (D.eTau (tauPl D (true, t)) : D.R.GG))

end PI.SzCt.UnitaryGroupMassFormula
