module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilSpaceVEqSpaceP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionShiftCommSingleMonomialStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPowMemAndSpaceVLe
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem totFil_deepest : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K), X.IsGood s → IsNef K X.LA → IsBig K X.LA → X.MulStable → totFil X s (X.T - X.D) = ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (LinearMap.range (incl X X.D)).map (pw (shift X.toGeo) s α.1) := by
  intro hF K _ _ X s hs hn hb hm
  have hP := filP hF K X s hs hn hb
  have hVT : spaceP X s ≤ X.V X.T := le_sup_right.trans (mulPow_mem_and_spaceV_le K X s hm).2
  have hL : totFil X s (X.T - X.D) = (spaceP X s).map (LinearMap.single K (fun j => X.Sec j) X.T) := by
    show ((Fil (X.ideal s) (X.T - X.D) (spaceV X s)).comap (X.V X.T).subtype).map
        (LinearMap.single K _ X.T ∘ₗ (X.V X.T).subtype) = _
    rw [hP, Submodule.map_comp, Submodule.map_comap_subtype, inf_of_le_right hVT]
  have hR : ∀ α : MonoDeg (Fin X.D) (X.T - X.D),
      (LinearMap.range (incl X X.D)).map (pw (shift X.toGeo) s α.1) =
        ((X.V X.D).map (mulPow X.toGeo s (add_sub_D X) α)).map (LinearMap.single K (fun j => X.Sec j) X.T) := by
    intro α
    have he : pw (shift X.toGeo) s α.1 ∘ₗ LinearMap.single K (fun j => X.Sec j) X.D =
        LinearMap.single K (fun j => X.Sec j) X.T ∘ₗ mulPow X.toGeo s (add_sub_D X) α := by
      refine LinearMap.ext fun m => ?_
      simp only [LinearMap.comp_apply, LinearMap.coe_single]
      exact (GlobalTheory.T.hilbertSamuelSectionShift_comm_single_monomial K X.toGeo).2.2 s (X.T - X.D) X.D X.T (add_sub_D X) α m
    rw [show incl X X.D = LinearMap.single K (fun j => X.Sec j) X.D ∘ₗ (X.V X.D).subtype from rfl,
      LinearMap.range_comp, Submodule.range_subtype, ← Submodule.map_comp, he, Submodule.map_comp]
  rw [hL, iSup_congr hR, ← Submodule.map_iSup]
  rfl

end GlobalTheory.HSShort
