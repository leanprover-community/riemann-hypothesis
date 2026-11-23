module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RepJetAugCompTrunc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem isMapOf_pow_mulF : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by
  intro R _ G _ d x hx F hF N
  induction N with
  | zero =>
    refine ⟨gp_zero₂, fun n a y h => ?_⟩
    have h0 := (repSt_of_jetAlgSt jetAlg R G d x hx (Fin n × Fin d)).2.2.2.1
    have e : comp1 (mulF F 0) a = 0 := evP_zero ![a] (single_point_zero_constant h.1)
    rw [e, pow_zero]
    simpa only [MonObj.comp_one] using h0
  | succ N ih =>
    refine ⟨gp_addOf F hF.1 _ _ ih.1 (gp_pt 0), fun n a y h => ?_⟩
    have e : comp1 (mulF F (N + 1)) a = addOf F (comp1 (mulF F N) a) a := by
      have e1 := evP_addOf ![a] (single_point_zero_constant h.1) F (mulF F N) (pt R d 0) ih.1 (gp_pt 0)
      rw [evP_pt _ (single_point_zero_constant h.1)] at e1
      exact e1
    rw [e, pow_succ]
    simpa only [MonObj.comp_mul, Category.comp_id] using hF.2 n _ _ _ _ (ih.2 n a y h) h

end GlobalTheory.JetSer
