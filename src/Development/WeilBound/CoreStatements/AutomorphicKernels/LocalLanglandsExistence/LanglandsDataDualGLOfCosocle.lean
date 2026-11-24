module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideRest
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExistsClassIsLSeg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.MultiProdCompInvTranspose
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace PositivityTheory.Pf1.LocalLanglands.LDual

theorem lExists_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL (k := k), IsL 𝔪 x.rep :=
  fun k _ _ _ _ _ => GlobalTheory.LocGL.LExist.main k hS (PositivityTheory.Exh.exists_class_isLSeg k)

theorem langlandsDataDualGL_of_clauses (hS : GlobalTheory.Published.StandardCosocleGL)
    (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (l : List (Segment k)) (x y : IrrGL (k := k)), IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
        ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep) :
    GlobalTheory.Published.LanglandsDataDualGL :=
  fun k _ _ _ _ _ => ⟨lExists_of_cosocle hS k, hD k⟩

theorem langlandsDataDualGL_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) : GlobalTheory.Published.LanglandsDataDualGL :=
  langlandsDataDualGL_of_clauses hS PositivityTheory.Pf1.LDual2.langlandsDataDualGL_dual

end PositivityTheory.Pf1.LocalLanglands.LDual
