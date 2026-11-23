module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdeal
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PullIopOf
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.ReductionOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of (B : Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hL : B.LatAll)
    (h0 : ∀ N N', Even N → Even N' → B.ThZeroMem N N')
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) : B.EqP χ :=
  reduction_of (detMul D) (detSmul D) (norm_one_unit_ideal D) (smulSD D) χ hχ hL h0 hSq hTL hTR (pullIop_of hL) hJ1 hJ2

theorem eqP (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSq : SqP D B.tor) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) (hJ1 : J1 B) (hJ2 : J2 B) : B.EqP χ :=
  eqP_of B χ hχ (B.latAll hcc hδ hδ0) (fun N N' _ _ => B.thZeroMem hS N N') hSq hTL hTR hJ1 hJ2

end Formalism.L2.PairingIndexBounds.Eq
