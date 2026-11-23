module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiRegularAlongOfEtale
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

open TopologicalSpace Opposite H0

theorem exists_local_lift_H0On : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (B : LB Y), B.IsLB → ∀ (I : Y.IdealSheafData) (g : sectionsOnClosedSubscheme p B I) (y : Y), ∃ (W : Y.Opens) (_ : y ∈ W) (b : Vanishing.H0 p B W), ∀ (z : I.subscheme) (hz : I.subschemeι z ∈ W) (j : (B.pull I.subschemeι).ι) (hj : z ∈ (B.pull I.subschemeι).U j), Vanishing.H0.germ j z (TopologicalSpace.Opens.mem_top z) hj g = (I.subschemeι.stalkMap z).hom (Vanishing.H0.germ (j PUnit.unit) (I.subschemeι z) hz (mem_pull.1 hj) b) := by
  intro k _ Y p B hB I g y
  obtain ⟨i, hi⟩ := exists_chart hB y
  obtain ⟨W, hyW, hWi⟩ := exists_affine hi
  obtain ⟨J, rfl⟩ : ∃ J : (B.pull I.subschemeι).ι, J PUnit.unit = i := ⟨fun _ => i, rfl⟩
  have hJ (z : I.subscheme) (hz : I.subschemeι z ∈ W.1) : z ∈ (B.pull I.subschemeι).U J :=
    mem_pull.2 (hWi hz)
  have hle : I.subschemeι ⁻¹ᵁ W.1 ≤ ⊤ ⊓ (B.pull I.subschemeι).U J :=
    fun z hz => ⟨trivial, hJ z hz⟩
  obtain ⟨a, ha⟩ := I.subschemeι_app_surjective W (resG I.subscheme hle (g.loc J))
  let b : H0 p B W.1 := (LB.chartEquiv hB (J PUnit.unit) hWi).symm a
  have hb (x : Y) (hx : x ∈ W.1) : germ (J PUnit.unit) x hx (hWi hx) b = ger x hx a := by
    conv_rhs =>
      rw [← (LB.chartEquiv hB (J PUnit.unit) hWi).apply_symm_apply a, LB.chartEquiv_apply,
        ger_resG]
    rfl
  refine ⟨W.1, hyW, b, fun z hz j hj => ?_⟩
  have h0 : germ J z (Opens.mem_top z) (hJ z hz) g =
      (I.subschemeι.stalkMap z).hom (germ (J PUnit.unit) (I.subschemeι z) hz (hWi hz) b) := by
    rw [hb, germ_apply, ← ger_resG hle z hz, ← ha]
    exact (Scheme.Hom.germ_stalkMap_apply _ _ z hz a).symm
  rw [germ_change j J z _ hj (hJ z hz), h0,
    germ_change (j PUnit.unit) (J PUnit.unit) _ hz (mem_pull.1 hj) (hWi hz), map_mul,
    tr_pull B I.subschemeι z hj (hJ z hz), Units.coe_map]
  rfl

end GlobalTheory.Vanishing
