module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Field.ProperSpace
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SqrtNearOne

theorem exists_sq_eq_inv_near_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∀ U ∈ 𝓝 (1 : A.K), ∀ᶠ v in 𝓝 (1 : A.K), ∃ s ∈ U, ∃ s' ∈ U, s * s' = 1 ∧ s ^ 2 = v := by
  intro F E _ _ _ _ hU A U hUm
  haveI : CharZero F := hU.charZero
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let V := Fin (Module.finrank F A.K) → F
  let b := Module.finBasis F A.K
  let eL : A.K ≃ₗ[F] V := b.equivFun
  have hc : Continuous eL := IsModuleTopology.continuous_of_linearMap eL.toLinearMap
  have hcs : Continuous eL.symm := IsModuleTopology.continuous_of_linearMap eL.symm.toLinearMap
  let L₂ : V →ₗ[F] V →ₗ[F] V := LinearMap.mk₂ F (fun x y => eL (eL.symm x * eL.symm y))
    (by intros; simp [add_mul]) (by intros; simp [smul_mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp [mul_smul_comm])
  let B : V →L[F] V →L[F] V :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (V →ₗ[F] V) ≃ₗ[F] (V →L[F] V)).toLinearMap ∘ₗ L₂)
  have hB : ∀ x y, B x y = eL (eL.symm x * eL.symm y) := fun x y => rfl
  let H : V × V → V × V := fun p => (B p.1 p.1, B p.1 p.2)
  let p0 : V × V := (eL 1, eL 1)
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let D : (V × V) ≃L[F] (V × V) := ContinuousLinearEquiv.equivOfInverse
    (((2 : F) • ContinuousLinearMap.fst F V V).prod (ContinuousLinearMap.fst F V V + ContinuousLinearMap.snd F V V))
    (((2 : F)⁻¹ • ContinuousLinearMap.fst F V V).prod (ContinuousLinearMap.snd F V V - (2 : F)⁻¹ • ContinuousLinearMap.fst F V V))
    (by intro p; ext1 <;> simp [smul_smul, h2])
    (by intro p; ext1 <;> simp [smul_smul, h2] <;> abel)
  have hd1 : HasStrictFDerivAt (fun p : V × V => B p.1 p.1)
      ((B p0.1).comp (ContinuousLinearMap.fst F V V) + ((B.comp (ContinuousLinearMap.fst F V V))).flip p0.1) p0 := by
    have := ((B.comp (ContinuousLinearMap.fst F V V))).hasStrictFDerivAt (x := p0)
    exact this.clm_apply (ContinuousLinearMap.fst F V V).hasStrictFDerivAt
  have hd2 : HasStrictFDerivAt (fun p : V × V => B p.1 p.2)
      ((B p0.1).comp (ContinuousLinearMap.snd F V V) + ((B.comp (ContinuousLinearMap.fst F V V))).flip p0.2) p0 := by
    have := ((B.comp (ContinuousLinearMap.fst F V V))).hasStrictFDerivAt (x := p0)
    exact this.clm_apply (ContinuousLinearMap.snd F V V).hasStrictFDerivAt
  have hd : HasStrictFDerivAt H (D : V × V →L[F] V × V) p0 := by
    refine (hd1.prodMk hd2).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun q => Prod.ext ?_ ?_
    · simp [D, p0, hB, two_smul]
    · simp [D, p0, hB]; exact add_comm _ _
  have hmap := hd.map_nhds_eq_of_equiv
  have hH0 : H p0 = p0 := by simp [H, p0, hB]
  rw [hH0] at hmap
  have hU' : eL.symm ⁻¹' U ∈ 𝓝 (eL 1) := hcs.continuousAt.preimage_mem_nhds (by simpa using hUm)
  have himg : H '' ((eL.symm ⁻¹' U) ×ˢ (eL.symm ⁻¹' U)) ∈ 𝓝 p0 := by
    rw [← hmap]; exact image_mem_map (prod_mem_nhds hU' hU')
  have hg : Continuous fun v : A.K => ((eL v, eL 1) : V × V) := hc.prodMk continuous_const
  have hev := hg.continuousAt (x := (1 : A.K)) |>.preimage_mem_nhds (t := H '' ((eL.symm ⁻¹' U) ×ˢ (eL.symm ⁻¹' U))) himg
  filter_upwards [hev] with v hv
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hv
  simp only [H, hB, Prod.mk.injEq] at hxy
  refine ⟨eL.symm x, hx, eL.symm y, hy, eL.injective hxy.2, ?_⟩
  rw [sq]; exact eL.injective hxy.1

end GlobalTheory.JR.SqrtNearOne
