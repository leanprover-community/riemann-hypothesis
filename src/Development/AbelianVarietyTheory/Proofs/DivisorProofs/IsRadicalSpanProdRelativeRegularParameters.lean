module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.EqZeroIffSubsingleton
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelParamRad

theorem prod_dvd_of_forall_dvd {R : Type} [CommMonoidWithZero R] :
    ∀ (m : ℕ) (t : Fin m → R), (∀ k, Prime (t k)) → (∀ i j, t i ∣ t j → i = j) →
      ∀ x : R, (∀ k, t k ∣ x) → ∏ k, t k ∣ x := by
  intro m
  induction m with
  | zero => intro t _ _ x _; simp
  | succ m ih =>
    intro t hp hd x hx
    obtain ⟨y, rfl⟩ := hx 0
    rw [Fin.prod_univ_succ]
    refine mul_dvd_mul_left _ (ih (fun k => t k.succ) (fun k => hp _) (fun i j h => Fin.succ_injective _ (hd _ _ h)) y
      fun k => ?_)
    refine ((hp k.succ).dvd_or_dvd (hx k.succ)).resolve_left fun h => ?_
    exact Fin.succ_ne_zero k (hd _ _ h)

theorem isRadical_span_prod : ∀ (o R : Type) [CommRing o] [CommRing R] [IsRegularLocalRing R] [IsDomain R] (b : o →+* R)
    (m : ℕ) (t : Fin m → R), IsRelParam b t → (Ideal.span {∏ k, t k}).IsRadical := by
  intro o R _ _ _ _ b m t h
  have hp : ∀ k, Prime (t k) := fun k => prime_of_not_mem_sq (h.1 k) (h.notMem_sq k)
  intro x hx
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 hx
  rw [Ideal.mem_span_singleton] at hn ⊢
  exact prod_dvd_of_forall_dvd m t hp (fun i j hij => h.eq_of_dvd hij) x
    fun k => (hp k).dvd_of_dvd_pow ((Finset.dvd_prod_of_mem t (Finset.mem_univ k)).trans hn)

end GlobalTheory.RelParamRad
