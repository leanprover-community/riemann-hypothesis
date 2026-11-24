module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.FinprodSplitAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfSubsetCpt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactSupportDcos
import GroundTheory.GlobalFields.LocalFieldAtPlace
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

theorem unitHecke : UnitHecke := by
  intro E _ _ _ n a b w
  have hG : ∀ m : ℕ, IsOpen (KGL w (n := m) : Set (GLw m w)) ∧ IsCompact (KGL w (n := m) : Set (GLw m w)) :=
    fun m => GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w m
  have hKLo : IsOpen (KL n w : Set (UL n w)) := (hG n).1.preimage continuous_subtype_val
  have hKLc : IsCompact (KL n w : Set (UL n w)) := GlobalTheory.LocFinU.isCompact_KL n w
  refine ⟨hKLo, ⟨?_, ?_⟩, (hG n).1, (hG n).2, ?_, ?_, ?_⟩
  · have hcl : IsClosed (KL n w : Set (UL n w)) := Subgroup.isClosed_of_isOpen _ hKLo
    refine hKLc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hcl)
    exact Set.support_indicator_subset
  · intro k hk x
    constructor
    · simp [Set.indicator, Subgroup.mul_mem_cancel_left _ hk]
    · simp [Set.indicator, Subgroup.mul_mem_cancel_right _ hk]
  · exact (hG a).1.prod (hG b).1
  · exact (hG a).2.prod (hG b).2
  · intro k hk
    unfold thL
    split_ifs
    · exact hk
    · exact GlobalTheory.CompanionTheory.IwFacts.thetaGL_mem_KGL w n hk

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
