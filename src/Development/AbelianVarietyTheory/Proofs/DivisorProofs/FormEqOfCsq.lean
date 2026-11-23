module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
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
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopRankPowers
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

noncomputable section

namespace GlobalTheory.IsoDeg

open Module
open scoped ComplexConjugate

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem form_eq_of_csq (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W)
    (hc : ∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i))
    (σ : K →+* ℂ) (x y : V) : n'.form σ (e x) (e y) = n.form σ x y := by
  have h1 := hc σ 2 ![1, 1] ![x, y]
  have h2 := hc σ 2 ![1, Complex.I] ![x, y]
  have hx := hc σ 1 ![1] ![x]
  have hy := hc σ 1 ![1] ![y]
  simp only [csq, Fin.sum_univ_two, Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.head_cons, map_one, one_mul, mul_one, Complex.add_re] at h1 h2 hx hy
  rw [← n.conj_symm σ x y, ← n'.conj_symm σ (e x) (e y)] at h1 h2
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
    Complex.conj_I, Complex.neg_re, Complex.neg_im, Complex.mul_im] at h1 h2
  apply Complex.ext
  · linarith
  · nlinarith

theorem deg_map_eq : ∀ (K V W : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (n : HermFam K V) (n' : HermFam K W) (e : V ≃ₗ[K] W), (∀ σ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → V), csq n σ c g = csq n' σ c fun i => e (g i)) → ∀ L : Submodule (𝓞 K) V, L.FG → deg n' (L.map (e.toLinearMap.restrictScalars (𝓞 K))) = deg n L := by
  intro K V W _ _ _ _ _ _ _ _ _ _ n n' e hc L hL
  set f := e.toLinearMap.restrictScalars (𝓞 K) with hf
  have hfi : Function.Injective f := e.injective
  obtain ⟨v, hv⟩ := exists_isFrame L hL
  have hfv : IsFrame K (L.map f) (fun i => e (v i)) := by
    refine ⟨fun i => ⟨v i, hv.1 i, rfl⟩, hv.2.1.map' e.toLinearMap e.ker, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h0 : e x ∈ (Submodule.span K (Set.range v)).map e.toLinearMap := ⟨x, hv.2.2 hx, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at h0
    exact h0
  rw [arakelovDegree_eq_degreeOfFamily n' (hL.map f) hfv, arakelovDegree_eq_degreeOfFamily n hL hv]
  unfold degreeOfFamily
  have hs : Submodule.span (𝓞 K) (Set.range fun i => e (v i)) =
      (Submodule.span (𝓞 K) (Set.range v)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hidx : (Submodule.span (𝓞 K) (Set.range fun i => e (v i))).toAddSubgroup.relIndex
      (L.map f).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex L.toAddSubgroup := by
    have key : ∀ P : Submodule (𝓞 K) V, (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom :=
      fun P => by
        ext y
        simp only [Submodule.mem_toAddSubgroup, Submodule.mem_map, AddSubgroup.mem_map,
          LinearMap.toAddMonoidHom_coe]
    rw [hs, key, key]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hfi
  have hg : ∀ σ, n'.gram σ (fun i => e (v i)) = n.gram σ v := fun σ => by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply]
    exact GlobalTheory.IsoDeg.form_eq_of_csq n n' e hc σ (v i) (v j)
  simp only [hidx, hg]

end GlobalTheory.IsoDeg
