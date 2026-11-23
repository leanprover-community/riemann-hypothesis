module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatrices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KapLatSupp

theorem mxAt_embed_kappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S T A : HSp D) (o : OrthDec T A L') (P : Pl D → Prop) (x : WO S L'), MxAt P x → MxAt P ((B.o.resS S).symm (0, l.κ S x)) ∧ MxAt P ((o.resT S).symm (0, x)) := by
  intro D ρ B L' ζ' l S T A o P x hx
  refine ⟨?_, ?_⟩
  · rw [OrthDec.resS_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_r GlobalTheory.LastOpPf.mxAt_zero _)
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LinkKapMx.mxAt_linkKappa D ρ B L' ζ' l S P x hx) _)
  · rw [OrthDec.resT_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_l _ GlobalTheory.LastOpPf.mxAt_zero) (GlobalTheory.LastOpPf.mxAt_mul_l _ hx)

end GlobalTheory.KapLatSupp
