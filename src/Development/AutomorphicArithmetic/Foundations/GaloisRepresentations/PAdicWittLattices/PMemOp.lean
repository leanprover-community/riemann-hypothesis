module

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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGrRefl
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.BcMapFst
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem cos_bij {G : Type} [Group G] (K V U : Subgroup G) (hVK : V ≤ K) (hUV : U ≤ V) :
    Function.Bijective (fun p : (K ⧸ V.subgroupOf K) × (V ⧸ U.subgroupOf V) =>
      (((⟨(p.1.out : G) * (p.2.out : G), K.mul_mem p.1.out.2 (hVK p.2.out.2)⟩ : K)) : K ⧸ U.subgroupOf K)) := by
  constructor
  · rintro ⟨c, y⟩ ⟨c', y'⟩ h
    have h1 : ((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G)) ∈ U := by
      have := QuotientGroup.eq.1 h
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((c.out)⁻¹ * c'.out : K) : G) =
          (y.out : G) * (((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G))) * (y'.out : G)⁻¹ := by
        push_cast; group
      rw [e]
      exact V.mul_mem (V.mul_mem y.out.2 (hUV h1)) (V.inv_mem y'.out.2)
    subst hc
    have hy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((y.out)⁻¹ * y'.out : V) : G) =
          ((c.out : G) * (y.out : G))⁻¹ * ((c.out : G) * (y'.out : G)) := by
        push_cast; group
      rw [e]; exact h1
    rw [hy]
  · intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf K) a
      have hvV : ((v : K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
      let b : V := ⟨((v : K) : G)⁻¹, V.inv_mem hvV⟩
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf V) b
      have hwU : ((w : V) : G) ∈ U := Subgroup.mem_subgroupOf.1 w.2
      refine ⟨((a : K ⧸ V.subgroupOf K), (b : V ⧸ U.subgroupOf V)), ?_⟩
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((((⟨(((a : K ⧸ V.subgroupOf K).out : K) : G) * (((b : V ⧸ U.subgroupOf V).out : V) : G),
          K.mul_mem (a : K ⧸ V.subgroupOf K).out.2 (hVK (b : V ⧸ U.subgroupOf V).out.2)⟩ : K))⁻¹ * a : K) : G) =
          ((w : V) : G)⁻¹ := by
        simp only [hv, hw, b]
        push_cast
        group
      rw [e]; exact U.inv_mem hwU
