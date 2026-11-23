module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
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

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.NoPr

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.CellAmp

def AmpKF0 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end GlobalTheory.NoPr

end
