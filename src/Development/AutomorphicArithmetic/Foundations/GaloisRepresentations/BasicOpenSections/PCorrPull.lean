module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

theorem UpperTheory.Gal.Mod.corrPull :
    CorrPull := by
  intro p Y S B O g s bS β hS T w hw hr
  have hsq : (pullback.fst T.p s ≫ T.r) ≫ g = (pullback.snd T.p s ≫ bS) ≫ β := by
    rw [Category.assoc, hr, ← Category.assoc, pullback.condition, Category.assoc, hS.w,
      Category.assoc]
  haveI := T.fin
  refine ⟨⟨pullback T.p s, pullback.snd T.p s, hS.lift _ _ hsq, Wt.comap (pullback.fst T.p s) w,
    inferInstance,
    TranscendenceTraces.wtBC_holds _ _ _ _ w (IsPullback.of_hasPullback T.p s) hw⟩,
    pullback.fst T.p s, IsPullback.of_hasPullback T.p s, hS.lift_fst _ _ _, ?_, rfl⟩
  exact hS.lift_snd _ _ _
