module

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.BcMapFst
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {m j : X.ι} {k h : G}
    (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.admitted m j (k * h) := by
  refine ⟨X.Δ.mul_mem (X.K_le j k hk) hh.1, fun u hu => ?_⟩
  have h3 := (X.K j).mul_mem ((X.K j).mul_mem hk (hh.2 u hu)) ((X.K j).inv_mem hk)
  have e : k * h * u * (k * h)⁻¹ = k * (h * u * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact h3

private theorem pl_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : Th.{u} B F)
    {m j : X.ι} {k h : G} (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.pl T m j (k * h) = X.pl T m j h := by
  have a := isAdmissible_flagPair_of_unitriangular_left_automorphism X hk hh
  have e : X.tr m j (k * h) a.1 a.2 = X.tr m j h hh.1 hh.2 := by
    rw [← X.tr_mul m j j h k hh.1 hh.2 (X.K_le j k hk)
      (fun u hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)) a.1 a.2,
      X.tr_self j k _ _ hk, Category.comp_id]
  unfold Tower.pl
  rw [dite_eq_left a, dite_eq_left hh]
  simp only [e]
