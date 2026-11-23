module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.formVanish_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  intro Rg _ A₀ T X N mA mB a φ p t c d F hF z q q' hq hq'
  have hV : φ z ∈ N.U q ⊓ N.U q' := ⟨hq, hq'⟩
  have hsec : ∀ i, gs φ z (N.U q) ((a i).f q) =
      (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * gs φ z (N.U q') ((a i).f q') := by
    intro i
    rw [← gs_res φ z (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q) hV, (a i).compat q q', gs_mul φ z _ hV,
      gs_unit φ z _ hV, gs_res φ z (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q') hV]
  have hcomb : comb a φ p c z q = fun j => (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    funext j
    simp only [comb, hsec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hev : ∀ (w : X.presheaf.stalk z) (y : Fin mB → X.presheaf.stalk z),
      MvPolynomial.eval₂Hom (gc (p ≫ t) z) (fun j => w * y j) F = w ^ d * MvPolynomial.eval₂Hom (gc (p ≫ t) z) y F := by
    intro w y
    simp only [MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hd := hF (MvPolynomial.mem_support_iff.mp hm)
    have hs : ∑ i ∈ m.support, m i = d := by
      rw [← hd]; simp [Finsupp.weight_apply, Finsupp.sum]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs]
    ring
  rw [hcomb, hev]
  exact IsUnit.mul_right_eq_zero ((gm φ z (N.U q ⊓ N.U q') (N.g q q')).isUnit.pow d)
