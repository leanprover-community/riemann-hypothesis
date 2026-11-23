module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingJointDataTwistRatioAtDetRoots
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unfoldingJointData_twist_ratio_at_detRoots : Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t t' : T) (M M' : Vol ch.G) (hM : M.Is t) (hM' : M'.Is t') (P : PolDown ch.G) (h : Pts ch.G) (x : ℕ → (AE D)ˣ), (∀ k, IsDetRoot _ (h k) (x k)) → h D.R.m = 1 → ∀ j, Even j → j < D.R.m → conAt ch.W hM' (fockD ch.W t' (fun j => ch.rm.vT D.R.m j) P) h j = ((((R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x j))⁻¹ * (R.toLevCh.xi t' * (R.toLevCh.xi t)⁻¹) (x (j + 2)) : Circle) : ℂ) • conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) h j := by
  first | exact @GlobalTheory.ConTwist.conAt_twist_big | exact GlobalTheory.ConTwist.conAt_twist_big | (intros; apply GlobalTheory.ConTwist.conAt_twist_big <;> assumption)
