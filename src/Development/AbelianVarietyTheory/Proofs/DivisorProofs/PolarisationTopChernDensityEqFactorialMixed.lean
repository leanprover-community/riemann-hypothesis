module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatLinearCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDetStatement
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem pol_chernDens_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → HermLB p) (c : AlgChart p σ D), ∀ y ∈ c.e.source, FibreProj.pol (fun n => c.chernDens ((ArInt.comb L n).φ σ) y) = D.factorial * dens (fun i => MLine.ofHerm (L i) σ) c y := by
  intro k _ X p σ D L c y hy
  set H : Fin D → Matrix (Fin D) (Fin D) ℂ := fun j => MixDens.chernMat ((L j).φ σ) c y with hH
  have hc (n : Fin D → ℤ) : c.chernDens ((ArInt.comb L n).φ σ) y =
      D.factorial / Real.pi ^ D * (∑ j, (n j : ℂ) • H j).det.re := by
    rw [← MixDens.chernMat_comb k X p σ D (Fin D) L n c y hy]
    rfl
  have key := GlobalTheory.T.sum_neg_one_pow_card_det_sum_eq_sum_perm_det D H
  simp only [FibreProj.pol, hc, dens, MLine.ofHerm]
  have e2 : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => c.hess ((L (τ l)).φ σ) (pick ((L (τ l)).φ σ).isLB y) y j l).det)
      = ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := rfl
  rw [e2, ← key, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have : ((-1 : ℂ) ^ S.card) = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  trans (-1) ^ S.card * (D.factorial / Real.pi ^ D * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det.re)
  · simp only [apply_ite (Int.cast : ℤ → ℂ), Int.cast_neg, Int.cast_one, Int.cast_zero]
  · ring

end GlobalTheory.Mix
