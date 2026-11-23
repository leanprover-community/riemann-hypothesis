module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportValStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalOfArtinReciprocity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthsModuloSubmoduleAgreeStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.StepGlobalPf
variable {D : D7} (i : D.nd.Loc)
variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)


theorem main_alt_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.GlobalStatement := by
  intro hA D i r ρ π Xs eρ eχ hr _ _ hG4 hG5 hG5x hG6 hDec _ hS hZ hπ hl hsel hsha
  obtain ⟨S, hS⟩ := hS
  rw [GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal]
  exact GlobalTheory.CutCore.main hA D i r ρ π Xs eρ eχ S hr hS hZ hπ (noChiOff i r Xs hG6) (unrOut i r ρ π Xs hG4 hDec)
    (atS i r π Xs hG5 hG5x) (atQ i r Xs hG5 hG5x)
    (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eρ).1 (hl w hw).2.1,
      fun c hc => (GlobalTheory.T.lengths_modulo_submodule_agree.2 D i w hw r Xs _ _ eχ).1 ((hl w hw).2.2 c hc)⟩) hsel hsha
end GlobalTheory.StepGlobalPf
end
