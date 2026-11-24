module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory Matrix Set

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

def kM {n : ℕ} (a b : Matrix (Fin n) (Fin n) ℂ) : M2 n :=
  fromBlocks ((1 / 2 : ℂ) • (a + b)) ((Complex.I / 2) • (a - b)) (-((Complex.I / 2) • (a - b))) ((1 / 2 : ℂ) • (a + b))

def KIso : Prop := ∀ n : ℕ,
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, a ∈ unitaryGroup (Fin n) ℂ → b ∈ unitaryGroup (Fin n) ℂ →
      ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b) ∧
  (∀ a b a' b' : Matrix (Fin n) (Fin n) ℂ, kM a b * kM a' b' = kM (a * a') (b * b')) ∧ kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 ∧
  (∀ a b : Matrix (Fin n) (Fin n) ℂ, u1 (kM a b) = a ∧ u2 (kM a b) = b) ∧
  (∀ a : Matrix (Fin n) (Fin n) ℂ, (kM a a).toBlocks₂₁ = 0) ∧
  ∀ k : GR n, k ∈ KR n → u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
    mR k = kM (u1 (mR k)) (u2 (mR k))

def RepKer : Prop := ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
  [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure] (V : Submodule ℂ (H → ℂ)), FiniteDimensional ℂ V →
    (∀ φ ∈ V, Continuous φ) → (∀ φ ∈ V, ∀ a : H, (fun x => φ (a * x)) ∈ V) →
    ∃ κ : H → ℂ, Continuous κ ∧ (∀ f : H → ℂ, Continuous f → (fun x => ∫ v, κ v * f (x * v) ∂μ) ∈ V) ∧
      ∀ φ ∈ V, ∀ x, ∫ v, κ v * φ (x * v) ∂μ = φ x

end PositivityTheory.Rg.Sw.AbsSt.Proj
