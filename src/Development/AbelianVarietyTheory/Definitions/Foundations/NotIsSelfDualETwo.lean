module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params

@[expose] public section

open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.TestLat.Model

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
theorem _root_.GlobalTheory.TestLat.Model.mem_sumLat (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (T : C → Submodule (𝓞 K) (_root_.Formalism.L2.DIV.VV K lam))
    (u : Fin N → K) : u ∈ _root_.GlobalTheory.TestLat.sumLat lam e T ↔
      ∀ c, _root_.GlobalTheory.TestLat.valAt lam e c u ∈ T c := by
  simp only [_root_.GlobalTheory.TestLat.sumLat, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]



open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
omit [NumberField K] in
theorem _root_.GlobalTheory.TestLat.Model.valAt_bijective (lam : ι → _root_.Formalism.BasicNotions.DomWeight n) (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam) :
    Function.Bijective fun (u : Fin N → K) (c : C) => _root_.GlobalTheory.TestLat.valAt lam e c u := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun f a => (_root_.Formalism.L2.DIV.bVV K lam).equivFun (f (e a).1) (e a).2, fun u => ?_, fun f => ?_⟩
  · ext a
    simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Prod.mk.eta, Equiv.symm_apply_apply]
  · ext c
    simp [_root_.GlobalTheory.TestLat.valAt, LinearMap.funLeft_apply]


open NumberField in
open scoped Matrix ComplexOrder in
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type} in
omit [NumberField K] in
theorem _root_.GlobalTheory.TestLat.Model.sumGram_form [StarRing K] [Fintype C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (G : ι → Matrix (Fin n) (Fin n) K) (u w : Fin N → K) :
    star u ⬝ᵥ (_root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ w) =
      ∑ c, _root_.Formalism.L2.DIV.pairK lam G (_root_.GlobalTheory.TestLat.valAt lam e c u)
        (_root_.GlobalTheory.TestLat.valAt lam e c w) := by
  classical
  simp only [dotProduct, Matrix.mulVec, _root_.GlobalTheory.TestLat.sumGram, Matrix.of_apply, Pi.star_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_

  simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
  LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, map_sum, map_smulₛₗ,
  LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos rfl]
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring


end GlobalTheory.TestLat.Model
