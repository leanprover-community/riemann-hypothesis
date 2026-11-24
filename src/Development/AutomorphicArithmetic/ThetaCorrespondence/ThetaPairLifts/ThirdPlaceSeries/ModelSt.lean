module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRunModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingOfRunModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitsCompletelyTypePrime
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelDvdBadN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RunModelArch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypePrimesGtThreeR
import Formalism.LocalRingCardinality.NFLeTwoMulTSq
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
namespace GlobalTheory.ShareOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modelSt_alt : _root_.GlobalTheory.ShareOn.ModelStatement := by
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and _root_.GlobalTheory.ShareOn.p0_extreme_or_archOn_of_runModel _root_.GlobalTheory.BigOn.typePrimes_gt_three_r_alt) ?_
  intro eps Fm CH _ hx0
  obtain ⟨x0, hx0⟩ := _root_.GlobalTheory.BigTop.EventuallyAtPoints.and hx0.1 hx0.2
  refine ⟨x0, fun x hx hle ι p hrows hmore r hr hown i => ?_⟩
  obtain ⟨harch, hg⟩ := hx0 x hx hle ι p hrows
  obtain ⟨C, hfin, hact, M, ka, hRM⟩ := exists_runModel p hmore r hr hown i
  have hb0 : 0 < badN (Fm.D x ι) := by
    obtain ⟨v, -⟩ := hRM
    exact (GlobalTheory.TrivLevel.badN_pos_iff _).2 (hmore.2.1.fieldAt v).bad
  obtain ⟨hcard, ρ, σ, f, h1, h2, h3, h4⟩ :=
    Reading.reading_of_runModel p r hr i M ka hb0 (Fm.parT x hx ι).nV_ge hRM
  exact ⟨C, hfin, hact, M, ka, ρ, σ, f, h1, h2, h3, h4, levelCondition_restrict_of_halfUnipotent p r hr i M ka (hg hmore) hRM, hcard,
    harch hmore r hr hown i C M ka hRM⟩
end GlobalTheory.ShareOn
end
end
