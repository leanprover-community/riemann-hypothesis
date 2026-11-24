module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInter
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter : ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund A : Set I.GA), I.IsFundDom (I.muA μf) fund → MeasurableSet A → (∀ γ ∈ I.GFset, ∀ x ∈ A, γ * x ∈ A) → covol I.GFset (I.muA μf) A = I.muA μf (A ∩ fund) ∧ 0 < I.muA μf fund := by
  first | exact @GlobalTheory.CovolRat.covol_eq_inter_fund | exact GlobalTheory.CovolRat.covol_eq_inter_fund | (intros; apply GlobalTheory.CovolRat.covol_eq_inter_fund <;> assumption)
