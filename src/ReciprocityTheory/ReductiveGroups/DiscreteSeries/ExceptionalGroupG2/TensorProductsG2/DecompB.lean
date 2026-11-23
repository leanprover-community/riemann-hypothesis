module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompB
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem dc_tensF_single_false {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF false E a b (Pi.single c v) = Pi.single c (E a b v) + (if b = c then Pi.single a v else 0) := by
  funext c'
  simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.single_apply]
  by_cases h1 : c' = c <;> by_cases h2 : c' = a <;> by_cases h3 : b = c <;> subst_vars <;> simp_all

theorem dc_tensF_single_true {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (a b c : Fin n) (v : M) :
    tensF true E a b (Pi.single c v) = Pi.single c (E a b v) - (if a = c then Pi.single b v else 0) := by
  funext c'
  simp only [tensF, cond_true, tensVd_coord, Pi.sub_apply, Pi.single_apply]
  by_cases h1 : c' = c <;> by_cases h2 : c' = b <;> by_cases h3 : a = c <;> subst_vars <;> simp_all

theorem dc_mem_tensSub {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} {f : Fin n → M} :
    f ∈ tensSub S ↔ ∀ c, f c ∈ S := by
  simp [tensSub, Submodule.mem_pi]

theorem dc_tens_gen_le {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {V : Submodule ℂ M} (dual : Bool) {T : Submodule ℂ (Fin n → M)} (hVT : tensSub V ≤ T)
    (hT : ∀ a b, ∀ f ∈ T, tensF dual E a b f ∈ T) : tensSub (genSub E V) ≤ T := by
  apply ReciprocityTheory.ChartRestriction.DS.dc_tens_gen_le <;> assumption

section Ambient
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
  {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {E : Fin n → Fin n → Module.End ℂ D}
  {S : Submodule ℂ D} {dual : Bool}

theorem dc_kDiag_add (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → H) :
    kDiag dual σ k (fun c => x c + y c) = fun c => kDiag dual σ k x c + kDiag dual σ k y c := by
  funext c
  simp only [kDiag, map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem dc_kDiag_smul (k : Matrix (Fin n) (Fin n) ℂ) (a : ℂ) (x : Fin n → H) :
    kDiag dual σ k (fun c => a • x c) = fun c => a • kDiag dual σ k x c := by
  funext c
  simp only [kDiag, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun d _ => smul_comm _ _ _

theorem dc_isGKEndo_add' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A + B) := by
  apply ReciprocityTheory.ChartRestriction.DS.dc_isGKEndo_add' <;> assumption

theorem dc_isGKEndo_smul' {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (a : ℂ) :
    IsGKEndo dual ε σ E S (a • A) := by
  refine ⟨fun f hf => (tensSub S).smul_mem a (hA.1 f hf), fun x y f hf => ?_,
    fun k hk f hf f' hf' h => ?_⟩
  · simp only [LinearMap.smul_apply, map_smul, hA.2.1 x y f hf]
  · have e1 := hA.2.2 k hk f hf f' hf' h
    simp only [LinearMap.smul_apply, Pi.smul_apply, Submodule.coe_smul]
    rw [dc_kDiag_smul, ← e1]

theorem dc_isGKEndo_mul' {A B : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A)
    (hB : IsGKEndo dual ε σ E S B) : IsGKEndo dual ε σ E S (A * B) := by
  refine ⟨fun f hf => hA.1 _ (hB.1 f hf), fun a b f hf => ?_, fun k hk f hf f' hf' h => ?_⟩
  · simp only [Module.End.mul_apply, hB.2.1 a b f hf, hA.2.1 a b _ (hB.1 f hf)]
  · exact hA.2.2 k hk _ (hB.1 f hf) _ (hB.1 f' hf') (hB.2.2 k hk f hf f' hf' h)

theorem dc_isGKEndo_one' : IsGKEndo dual ε σ E S 1 :=
  ⟨fun f hf => hf, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ h => h⟩

theorem dc_isGKEndo_zero' : IsGKEndo dual ε σ E S 0 := by
  refine ⟨fun _ _ => (tensSub S).zero_mem, fun _ _ _ _ => by simp, fun k _ _ _ _ _ _ => ?_⟩
  funext c
  simp [kDiag]

theorem dc_isGKEndo_aeval {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E S A) (p : ℂ[X]) :
    IsGKEndo dual ε σ E S (aeval A p) := by
  apply ReciprocityTheory.ChartRestriction.DS.dc_isGKEndo_aeval <;> assumption

end Ambient

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section


namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

def dc_wsh (dual : Bool) (μ : Fin n → ℝ) (c : Fin n) : Fin n → ℝ :=
  if dual then μ + Pi.single c 1 else μ - Pi.single c 1

section
variable {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem dc_top_coord_false {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF false E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh false μ c) (f c) := by
  apply ReciprocityTheory.ChartRestriction.DS.dc_top_coord_false <;> assumption

theorem dc_top_coord_true {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF true E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh true μ c) (f c) := by
  apply ReciprocityTheory.ChartRestriction.DS.dc_top_coord_true <;> assumption

theorem dc_top_coord {dual : Bool} {μ : Fin n → ℝ} {f : Fin n → M} (hf : IsKHWVec ε (tensF dual E) μ f)
    (h0 : f ≠ 0) : ∃ c, f c ≠ 0 ∧ IsKHWVec ε E (dc_wsh dual μ c) (f c) := by
  cases dual
  · exact dc_top_coord_false hf h0
  · exact dc_top_coord_true hf h0

end

section Pi
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

abbrev dc_TX (n : ℕ) (D : Type*) [NormedAddCommGroup D] [InnerProductSpace ℂ D] := PiLp 2 (fun _ : Fin n => D)

def dc_eqv : dc_TX n D ≃ₗ[ℂ] (Fin n → D) := WithLp.linearEquiv 2 ℂ (Fin n → D)

theorem dc_eqv_apply (x : dc_TX n D) : dc_eqv x = x.ofLp := rfl

theorem dc_eqv_symm_apply (f : Fin n → D) : (dc_eqv (n := n)).symm f = WithLp.toLp 2 f := rfl

def dc_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) : Module.End ℂ (dc_TX n D) :=
  dc_eqv.symm.conj (tensF dual E a b)

theorem dc_tensX_apply (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_tensX dual E a b x = dc_eqv.symm (tensF dual E a b (dc_eqv x)) := by
  simp [dc_tensX, LinearEquiv.conj_apply]

theorem dc_eqv_tensX (dual : Bool) (E : Fin n → Fin n → Module.End ℂ D) (a b : Fin n) (x : dc_TX n D) :
    dc_eqv (dc_tensX dual E a b x) = tensF dual E a b (dc_eqv x) := by
  rw [dc_tensX_apply, LinearEquiv.apply_symm_apply]

theorem dc_tensX_isGlRep {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hE : IsGlRep E) :
    IsGlRep (dc_tensX dual E) := by
  apply ReciprocityTheory.ChartRestriction.DS.dc_tensX_isGlRep <;> assumption

theorem dc_sum_inner_ite_left (a : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (if i = a then u else 0) (g i) = inner ℂ u (g a) := by
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_sum_inner_ite_right (b : Fin n) (u : D) (g : Fin n → D) :
    ∑ i, inner ℂ (g i) (if i = b then u else 0) = inner ℂ (g b) u := by
  rw [Finset.sum_eq_single b (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem dc_tensX_isKUnitary {dual : Bool} {E : Fin n → Fin n → Module.End ℂ D} (hU : IsKUnitary ε E) :
    IsKUnitary ε (dc_tensX dual E) := by
  apply ReciprocityTheory.ChartRestriction.DS.dc_tensX_isKUnitary <;> assumption

end Pi

end ReciprocityTheory.ChartRestriction.DS.G2

end
