module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAffineChartBoundaryZeroSet
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

theorem _root_.GlobalTheory.T.exists_smooth_affine_chart_boundary_zero_set : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw), IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, ∃ (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (p : Γ(Y₀ TF.X Z, W)), y ∈ W ∧ W ≤ (L₀ TF.X Z la).U i ∧ IsDomain Γ(Y₀ TF.X Z, W) ∧ RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ str₀ TF.X Z)).hom ∧ p ≠ 0 ∧ ∀ y' ∈ W, (y' ∈ bd₀ TF.X Z ↔ y' ∉ (Y₀ TF.X Z).basicOpen p) := by
  first | exact @GlobalTheory.CompHS.ChartBd.exists_chart_bd | exact GlobalTheory.CompHS.ChartBd.exists_chart_bd | (intros; apply GlobalTheory.CompHS.ChartBd.exists_chart_bd <;> assumption)
