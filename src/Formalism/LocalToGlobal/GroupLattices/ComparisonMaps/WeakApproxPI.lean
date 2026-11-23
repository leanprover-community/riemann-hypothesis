module

public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanOfWeak
public import Formalism.PeriodIntegrals.WeakApproxDVR
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeakApproxDVR
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.MainNotions.G

theorem weakApprox_of_dvr (h : PI.WeakApproxDVR) {p : ℕ} (G : GAtP p) {E : Type} [Field E]
    (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)
    (hfr : ∀ v, IsFractionRing (G.P.W v) (G.P.Qq v))
    (hp : ∀ v, (p : G.P.Qq v) ≠ 0) (hpu : ∀ v, ¬ IsUnit (p : G.P.W v))
    (hden : ∀ v (x : G.P.Qq v) (N : ℕ), ∃ a : E, ∃ c : G.P.W v,
      iw v a = x + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c)
    (hdist : ∀ v v', v ≠ v' → ∃ a : E, iw v a ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      iw v' a ∉ Set.range (algebraMap (G.P.W v') (G.P.Qq v'))) :
    Formalism.L2.G.Cmp.WeakApprox G iw := by
  unfold PI.WeakApproxDVR at h
  unfold Formalism.L2.G.Cmp.WeakApprox
  have := hfr
  exact h E (Fin G.P.nV) G.P.W G.P.Qq iw p hp hpu hden hdist

theorem Formalism.L2.G.Cmp.weakApprox_of_approx_and_separation {p : ℕ} (G : GAtP p) {E : Type} [Field E]
    (iw : ∀ v : Fin G.P.nV, E →+* G.P.Qq v)
    (hfr : ∀ v, IsFractionRing (G.P.W v) (G.P.Qq v))
    (hp : ∀ v, (p : G.P.Qq v) ≠ 0) (hpu : ∀ v, ¬ IsUnit (p : G.P.W v))
    (hden : ∀ v (x : G.P.Qq v) (N : ℕ), ∃ a : E, ∃ c : G.P.W v,
      iw v a = x + (p : G.P.Qq v) ^ N * algebraMap (G.P.W v) (G.P.Qq v) c)
    (hdist : ∀ v v', v ≠ v' → ∃ a : E, iw v a ∈ Set.range (algebraMap (G.P.W v) (G.P.Qq v)) ∧
      iw v' a ∉ Set.range (algebraMap (G.P.W v') (G.P.Qq v'))) :
    Formalism.L2.G.Cmp.WeakApprox G iw :=
  weakApprox_of_dvr weak_approximation_dvr G iw hfr hp hpu hden hdist
