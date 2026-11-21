import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPowPolAVPowPolOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixOrderActionOnPower

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat.Model

section Sign

variable {O C : Type} [CommRing O] [Field C] [Algebra O C]
  {U : Type} [AddCommGroup U] [Module C U] [Module O U] [IsScalarTower O C U] {N : ℕ}
  (v : Valuation C ℝ≥0)



variable {U' : Type} [AddCommGroup U'] [Module C U'] [Module O U'] [IsScalarTower O C U']


end Sign

section Sides

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
  [Algebra ℤ_[p] C] [IsAlgClosed C] [CharZero C]

theorem pairV_eq_zero {τ τ' : Λ →+* O} {x y : P.V} (hx : x ∈ P.eigV τ) (hy : y ∈ P.eigV τ') (a : Λ)
    (ha : algebraMap O C (τ a) ≠ algebraMap O C (τ' (star a))) : P.pairV x y = 0 := by
  have h := P.pairV_act a x y
  rw [mem_eigenSub.1 hx a, mem_eigenSub.1 hy (star a), map_smul, LinearMap.smul_apply, map_smul,
    smul_eq_mul, smul_eq_mul] at h
  exact (mul_eq_mul_right_iff.1 h).resolve_left ha

variable {J : Type} [DecidableEq J] {σ : J → Λ →+* O} (h : IsSplitting (embC C σ))

theorem pairV_proj (i : J) (x : P.V) {y : P.V} (hy : y ∈ P.eigV ((σ i).comp (starRingEnd Λ))) :
    P.pairV (proj h P.actV i x) y = P.pairV x y := by
  have key : ∀ t : C ⊗[ℤ] Λ, P.pairV (tensorAction P.actV t x) y =
      splitMap (embC C σ) t i * P.pairV x y := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht, Pi.add_apply, add_mul]
    | tmul c a =>
      rw [tensorAction_tmul, map_smul, LinearMap.smul_apply, P.pairV_act,
        mem_eigenSub.1 hy (star a), map_smul, splitMap_tmul]
      simp only [smul_eq_mul, RingHom.comp_apply, starRingEnd_apply, star_star, _root_.mul_assoc]
  rw [proj, key, splitMap_idem, Pi.single_eq_same, _root_.one_mul]

variable [Algebra ℤ_[p] O] [IsScalarTower ℤ_[p] O C]

theorem mem_latTSub_iff (i : J) {y : P.V} (hy : y ∈ P.eigV ((σ i).comp (starRingEnd Λ))) :
    y ∈ P.latTSub ((σ i).comp (starRingEnd Λ)) ↔
      ∀ x ∈ P.latTQuot h i, ∃ c : O, algebraMap O C c = P.pairV x y := by
  constructor
  · rintro ⟨hT, -⟩ _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change ∃ c : O, algebraMap O C c = P.pairV (proj h P.actV i _) y
    rw [pairV_proj P h i _ hy]
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x x' hx hx' =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨d, hd⟩ := hx'
      exact ⟨c + d, by rw [map_add, map_add, map_add, LinearMap.add_apply, hc, hd]⟩
    | tmul c s =>
      obtain ⟨d, hd⟩ := (P.mem_latT_iff y).1 hT s
      refine ⟨-(c * d), ?_⟩
      have : (algebraMap O C c ⊗ₜ s : P.V) = algebraMap O C c • (1 : C) ⊗ₜ s := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [P.inclT_tmul, this, map_smul, LinearMap.smul_apply, P.pairV_swap, ← hd, map_neg, map_mul,
        smul_eq_mul, mul_neg]
  · intro H
    refine ⟨(P.mem_latT_iff y).2 fun t => ?_, hy⟩
    obtain ⟨c, hc⟩ := H _ ⟨_, P.one_tmul_mem_latT t, rfl⟩
    change _ = P.pairV (proj h P.actV i _) y at hc
    rw [pairV_proj P h i _ hy, P.pairV_swap] at hc
    exact ⟨-c, by rw [map_neg, hc, neg_neg]⟩

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]




end Sides

section Gaussian

def gaussMat : GaussianInt →+* Matrix (Fin 2) (Fin 2) ℤ where
  toFun z := !![z.re, -z.im; z.im, z.re]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' a b := by ext i j; fin_cases i <;> fin_cases j <;> simp [add_comm]


def gaussBasis : Module.Basis (Fin 2) ℤ GaussianInt :=
  Module.Basis.ofEquivFun (AddEquiv.toIntLinearEquiv
    { toFun := fun z => ![z.re, z.im]
      invFun := fun x => ⟨x 0, x 1⟩
      left_inv := fun _ => rfl
      right_inv := fun x => by ext i; fin_cases i <;> rfl
      map_add' := fun a b => by ext i; fin_cases i <;> simp })



end Gaussian

end GlobalTheory.HTLat.Model
