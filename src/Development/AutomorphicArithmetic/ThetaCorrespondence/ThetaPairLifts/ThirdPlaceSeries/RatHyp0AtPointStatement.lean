module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut

@[expose] public section



section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.ratHyp0_of_bad_prime_mem_S0 : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i), p.PointConditions' → More p →
  ∀ t : (Fm.D x i).ntw.Tw, (Fm.D x i).ntw.NonzeroIndexPlace t →
  (∀ P : Pl (Fm.D x i).host.E, (((Fm.D x i).host.QS * (Fm.D x i).host.q * Ideal.absNorm (Fm.D x i).host.ccK * ((Fm.D x i).host.g 0 * (Fm.D x i).host.g 1 *
    (Fm.D x i).host.pde * (Fm.D x i).host.pde') : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal → P ∈ (Fm.D x i).ntw.S0 t) →
  ∀ j : Fin (Fm.D x i).R.m, RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt | exact _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt <;> assumption)
end
