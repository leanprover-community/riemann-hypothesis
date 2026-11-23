module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLaw

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

theorem curve_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 := by
  intro E _ _ _ H ρ Z hz
  obtain ⟨Hm, χ, Ef, -, -, hT2, -⟩ := Z.theta
  have hd : Z.u.IsDiff 0 Z.C'.v := by
    have h := Z.diff
    rw [hz, mul_zero] at h
    exact h
  have ht : IsTangent Z.C'.v := Z.C'.basis.1 0
  have h1 : IsTangent (1 : epsR ℂ ⟶ Z.C'.P.A) := (ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff _).1 ReciprocityTheory.ChartRestriction.G.Chart.isTan_one
  have hd1 : Z.u.IsDiff 0 (1 : epsR ℂ ⟶ Z.C'.P.A) := GlobalTheory.UnifDifferential.isDiff_one Z.u
  have e : Z.C'.v = 1 := (hT2 0).unique ⟨ht, hd⟩ ⟨h1, hd1⟩
  have hb := Z.C'.basis.2 Z.C'.v ht
  have c0 : IsLieComb ![(0 : ℂ)] ![Z.C'.v] Z.C'.v := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff, ReciprocityTheory.ChartRestriction.G.Chart.prodPts, e]
    simp
  have c1 : IsLieComb ![(1 : ℂ)] ![Z.C'.v] Z.C'.v := by
    rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff, ReciprocityTheory.ChartRestriction.G.Chart.prodPts]
    simp only [Matrix.cons_val_fin_one, ReciprocityTheory.ChartRestriction.G.Chart.scaleD_one, ReciprocityTheory.ChartRestriction.G.Chart.spMap_id,
      Category.id_comp, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil]
    exact (_root_.mul_one _).symm
  have h01 := congrFun (hb.unique c0 c1) 0
  simp at h01

end PositivityTheory.Xgf
