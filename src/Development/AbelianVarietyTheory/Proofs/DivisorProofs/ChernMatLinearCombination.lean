module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem chernMat_tens (L M : HermLB p) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    chernMat ((L.tens M).φ σ) c y = chernMat (L.φ σ) c y + chernMat (M.φ σ) c y := by
  have ha := mem_pick (L.φ σ).isLB y
  have hb := mem_pick (M.φ σ).isLB y
  unfold chernMat
  rw [c.hess_eq ((L.tens M).cInf σ) hy (i := (pick (L.φ σ).isLB y, pick (M.φ σ).isLB y))
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (mem_pick _ y)]
  change c.hess ((L.φ σ).tens (M.φ σ)) _ y = _
  exact FlatMass.hess_tens (L.cInf σ) (M.cInf σ) hy ha hb

def chernHom (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    HermLB.IsomClass p →+ Matrix (Fin D) (Fin D) ℂ :=
  AddMonoidHom.mk' (M := HermLB.IsomClass p)
    (Quotient.lift (s := HermLB.isometrySetoid p) (fun L => chernMat (L.φ σ) c y)
    fun _ _ h => chernMat_congr h c hy) (by rintro ⟨L⟩ ⟨M⟩; exact chernMat_tens L M c hy)

theorem chernHom_icls (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) (L : HermLB p) :
    chernHom c hy L.icls = chernMat (L.φ σ) c y := rfl

theorem chernMat_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (κ : Type)
    [Fintype κ] (L : κ → HermLB p) (n : κ → ℤ) (c : AlgChart p σ D), ∀ y ∈ c.e.source,
    chernMat ((ArInt.comb L n).φ σ) c y = ∑ j, (n j : ℂ) • chernMat ((L j).φ σ) c y := by
  intro k _ X p σ D κ _ L n c y hy

  rw [← chernHom_icls c hy, icls_comb, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, chernHom_icls, Int.cast_smul_eq_zsmul]

end GlobalTheory.MixDens
