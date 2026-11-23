module

public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdemAtUniqueOrth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeZeroOfIsIdemAt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowBesZeroE
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.IdemSumSet

theorem subset_of_isIdemSum {D : D7} {e : Formalism.L2.Theta.AE D} {P P' : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : Formalism.IndefR.Datum.IsIdemSum e P) (h' : Formalism.IndefR.Datum.IsIdemSum e P') : P ⊆ P' := by
  intro w hw
  obtain ⟨⟨es, hes, he⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, hf⟩, -⟩ := h'
  have hw' := hes w hw

  have hpick : es w * e = es w := by
    rw [he, Finset.mul_sum, Finset.sum_eq_single w]
    · exact hw'.1.1
    · intro v hv hvw
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hes v hv)).2 (Ne.symm hvw)
    · intro hn
      exact absurd hw hn

  by_contra hout
  apply GlobalTheory.LevelPlaces.ne_zero_of_isIdemAt hw'
  rw [← hpick, hf, Finset.mul_sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hfs v hv)).2 ?_
  rintro rfl
  exact hout hv

theorem places_eq_of_isIdemSum : ∀ (D : D7) (e : AE D) (P P' : Finset (Pl D.host.E)), IsIdemSum e P → IsIdemSum e P' → P = P' := by
  intro D e P P' h h'
  ext w
  exact ⟨fun hw => subset_of_isIdemSum h h' hw, fun hw => subset_of_isIdemSum h' h hw⟩

end GlobalTheory.IdemSumSet
