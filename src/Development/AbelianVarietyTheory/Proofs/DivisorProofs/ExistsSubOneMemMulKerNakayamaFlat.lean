module

public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem mem_map_mul_ker_of_flat {R' A C' : Type} [CommRing R'] [CommRing A] [CommRing C']
    [Algebra R' A] [Algebra R' C'] [Module.Flat R' C'] (f : A →ₐ[R'] C')
    (hf : Function.Surjective f) (J : Ideal R') {x : A}
    (hx : x ∈ J.map (algebraMap R' A)) (hfx : f x = 0) :
    x ∈ J.map (algebraMap R' A) * RingHom.ker f := by
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, c, g, rfl⟩ := hx
  have hg : ∀ i, ∃ j ∈ J, algebraMap R' A j = (g i : A) := fun i => (g i).2
  choose j hjJ hjg using hg
  have hsum : ∑ i, j i • f (c i) = 0 := by

    rw [← hfx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, map_mul, AlgHom.commutes, Algebra.smul_def, _root_.mul_comm]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R') (M := C') (f := j)
    (x := fun i => f (c i)) hsum
  choose z hz using fun l => hf (y l)
  have hd : ∀ i, c i - ∑ l, a i l • z l ∈ RingHom.ker f := by
    intro i
    rw [RingHom.mem_ker]
    change f (c i - ∑ l, a i l • z l) = 0

    rw [map_sub, map_sum]
    simp only [map_smul, hz]
    rw [← hy i, sub_self]
  have h0 : ∑ i, algebraMap R' A (j i) * ∑ l, a i l • z l = 0 := by
    have hl : ∀ l, ∑ i, algebraMap R' A (j i) * (a i l • z l) = 0 := by
      intro l
      have : ∑ i, algebraMap R' A (j i) * (a i l • z l) = (∑ i, j i * a i l) • z l := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
      rw [this, ha l, zero_smul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun l _ => hl l
  have key : ∑ i, c i • (g i : A) =
      ∑ i, algebraMap R' A (j i) * (c i - ∑ l, a i l • z l) := by
    simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, _root_.mul_comm]
  rw [key]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hjJ i)) (hd i)

theorem exists_sub_one_mem_mul_ker_le :
    ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C']
      [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f →
      ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f →
        RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) →
          ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  intro R' A C' _ _ _ _ _ _ _ f hf I J hI hK
  have hle : RingHom.ker f ≤ I ⊔ (J.map (algebraMap R' A)) • RingHom.ker f := by
    intro G hG
    obtain ⟨i, hi, x, hx, rfl⟩ := Submodule.mem_sup.1 (hK hG)
    have hfx : f x = 0 := by
      have h1 : f (i + x) = 0 := hG
      have h2 : f i = 0 := hI hi
      rw [map_add (f := _), h2, zero_add] at h1
      exact h1
    exact Submodule.add_mem_sup hi (mem_map_mul_ker_of_flat f hf J hx hfx)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian (RingHom.ker f)) le_rfl hle
  refine ⟨r, hr1, fun G hG => ?_⟩
  exact hr (Submodule.smul_mem_pointwise_smul G r _ hG)

end GlobalTheory.Pinch
