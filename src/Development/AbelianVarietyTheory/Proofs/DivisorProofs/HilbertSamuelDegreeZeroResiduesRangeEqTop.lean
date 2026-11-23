module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToOneOfStalkMap
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

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSShort

theorem totRes_incl_zero {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s} {δ : ℕ}
    (Co : Coord X.toGeo hs δ) (x : X.V 0) : totRes Co (incl X 0 x) = Co.ev 0 (hs.res 0 x.1) := by
  have h : incl X 0 x 0 = x.1 := Pi.single_eq_same (M := fun j => X.toGeo.Sec j) 0 x.1
  simp only [totRes, LinearMap.comp_apply, LinearMap.proj_apply, h, LinearEquiv.coe_coe]

theorem map_totRes_range_incl_zero : Quoted → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), IsNef K X.L₂ → IsBig K X.L₂ → (LinearMap.range (incl X 0)).map (totRes Co) = ⊤ := by
  intro Q K _ _ X s hs δ Co hnef hbig
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨f, hf⟩ := GlobalTheory.HSResOnto.res_onto Q K X.toGeo hnef hbig s hs ((Co.ev 0).symm v)
  have hf' : hs.res 0 (X.toGeo.mulE 0 f) = (Co.ev 0).symm v := hf
  have hm : X.toGeo.mulE 0 f ∈ X.V 0 := X.global_le 0 (Nat.zero_le _) (X.toGeo.mulE_mem_global 0 f)
  refine Submodule.mem_map.2 ⟨incl X 0 ⟨_, hm⟩, LinearMap.mem_range_self _ _, ?_⟩
  rw [totRes_incl_zero, hf', LinearEquiv.apply_symm_apply]

end GlobalTheory.HSShort
