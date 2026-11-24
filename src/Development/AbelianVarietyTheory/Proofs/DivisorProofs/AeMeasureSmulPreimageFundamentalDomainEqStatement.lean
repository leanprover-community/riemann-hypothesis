module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AeMeasureSmulPreimageFundamentalDomainEq
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ENNReal Pointwise


theorem _root_.GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq : ∀ (S X : Type) [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X] [MeasurableSMul₂ S X] [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν] [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ] (Γ : Subgroup S) [Countable Γ] (D : Set X), MeasurableSet D → IsFundamentalDomain Γ D μ → ∀ (E : Set S), IsFundamentalDomain Γ E ν → ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E := by
  first | exact @GlobalTheory.CovolIndep.ae_measure_slice_eq | exact GlobalTheory.CovolIndep.ae_measure_slice_eq | (intros; apply GlobalTheory.CovolIndep.ae_measure_slice_eq <;> assumption)
