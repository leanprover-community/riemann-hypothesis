module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAnalyticFrameOfUnitUniformisationFrame
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_analytic_frame_of_unit_uniformisation_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), letI : Algebra c.F ℂ := σ.toAlgebra; ∃ Φ : AnPt (Xo := Xo) (c := c) (U.un k x) W.g (fun j => relab c σ (W.e j).1) W.e, Φ.OfFam W.F (W.ik k) W.Pm ∧ Φ.Hm = Wu.Hm ∧ Φ.χ = Wu.χl ∧ Φ.fr = Wu.fr ∧ Φ.toAnFr.Rd 1 (U.un k x).s Wu.θ ∧ (∀ kk F θ, Φ.toAnFr.Rd kk F θ ↔ IsFrRd W Wu kk F θ) ∧ (∀ (α : 𝓞 E) a, W.Pm (W.F.t (W.ik k) (α • a)) = tyAct (fun j => relab c σ (W.e j).1) α (W.Pm (W.F.t (W.ik k) a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo (U.un k x).x a = Φ.e ((l.M : ℂ)⁻¹ • W.Pm (W.F.t (W.ik k) a)) := by
  first | exact @GlobalTheory.AnVal.exists_anPt_of_unitAt | exact GlobalTheory.AnVal.exists_anPt_of_unitAt | (intros; apply GlobalTheory.AnVal.exists_anPt_of_unitAt <;> assumption)
