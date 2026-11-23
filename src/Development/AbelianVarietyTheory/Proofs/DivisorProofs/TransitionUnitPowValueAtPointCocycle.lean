module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem trV_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  intro X L hL A _ y a b c n ha hb hc
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c) := fun q hq => ⟨⟨ha hq, hb hq⟩, hc hq⟩
  have e := congrArg (fun u => ((u ^ n : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ) : Γ(X, L.U a ⊓ L.U b ⊓ L.U c))) (hL.cocycle a b c)
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at e
  have e' := congrArg (valR y (L.U a ⊓ L.U b ⊓ L.U c)) e
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hT] at e'
  unfold trV
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) hT]
  exact e'

end GlobalTheory.MBLow.TanGauge
end
