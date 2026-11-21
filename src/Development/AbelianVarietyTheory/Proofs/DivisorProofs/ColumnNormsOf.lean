import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSeventh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEighth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantNinth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTenthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEleventhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantTwelfthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ErrorUnitExponentialEstimate

section
noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain
open Formalism.L2.DIV Formalism.L2.Col GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (v : InfinitePlace K)

theorem pairAt_add_left (x y z : S.V) : S.pairAt v (x + y) z = S.pairAt v x z + S.pairAt v y z := by
  simp only [GSD.pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (x y z : S.V) : S.pairAt v x (y + z) = S.pairAt v x y + S.pairAt v x z := by
  simp only [GSD.pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (a : K) (x y : S.V) :
    S.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (a : K) (x y : S.V) :
    S.pairAt v x (a • y) = v.embedding a * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pairAt_zero_left (y : S.V) : S.pairAt v 0 y = 0 := by
  simp [GSD.pairAt]

theorem pairAt_zero_right (y : S.V) : S.pairAt v y 0 = 0 := by
  simp [GSD.pairAt]

theorem pairAt_sum_left {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v (∑ i ∈ s, x i) y = ∑ i ∈ s, S.pairAt v (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_left, ih]

theorem pairAt_sum_right {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v y (∑ i ∈ s, x i) = ∑ i ∈ s, S.pairAt v y (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_right, ih]

theorem pairAt_self_nonneg (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have h1 := h.dotProduct_mulVec_nonneg (fun i => v.embedding (S.bV.repr x i))
  have h2 : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      (S.gramV.map v.embedding) *ᵥ (fun i => v.embedding (S.bV.repr x i)) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, mul_assoc]
    rfl
  rw [h2]
  exact (Complex.nonneg_iff.mp h1).1

theorem pairAt_smul_self (a : K) (x : S.V) :
    (S.pairAt v (a • x) (a • x)).re = ‖v.embedding a‖ ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_left, pairAt_smul_right, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem pairAt_inv_nat_smul_self (n : ℕ) (x : S.V) :
    (S.pairAt v (((n : K))⁻¹ • x) (((n : K))⁻¹ • x)).re = ((n : ℝ)⁻¹) ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_self]
  simp

theorem pairAt_cross_le (h : PosAt S v) (x y : S.V) :
    (S.pairAt v x y).re + (S.pairAt v y x).re ≤ (S.pairAt v x x).re + (S.pairAt v y y).re := by
  have h1 := pairAt_self_nonneg S v h (x + (-1 : K) • y)
  rw [pairAt_add_left, pairAt_add_right, pairAt_add_right, pairAt_smul_left, pairAt_smul_left,
    pairAt_smul_right, pairAt_smul_right] at h1
  simp at h1
  linarith

theorem pairAt_sum_le (h : PosAt S v) {α : Type*} (s : Finset α) (x : α → S.V) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ (s.card : ℝ) * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re := by
  have e1 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x i) (x j)).re := by
    rw [pairAt_sum_left, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pairAt_sum_right, Complex.re_sum]
  have e2 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x j) (x i)).re := by
    rw [e1, Finset.sum_comm]
  have e3 : ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x j)).re + (S.pairAt v (x j) (x i)).re) ≤
      ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x i)).re + (S.pairAt v (x j) (x j)).re) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pairAt_cross_le S v h _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at e3
  linarith

theorem ipAt_re (h : S.Ok) (φ ψ : S.D → S.V) :
    (S.ipAt h v φ ψ).re = ∑ c ∈ @Finset.univ _ h.fintypeCl,
      (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)

theorem ipAt_self_nonneg (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) : 0 ≤ (S.ipAt h v φ φ).re := by
  rw [ipAt_re]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (pairAt_self_nonneg S v hp _)

theorem ipAt_self_le (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) (B : ℝ)
    (hB : ∀ d, (S.pairAt v (φ d) (φ d)).re ≤ B) : (S.ipAt h v φ φ).re ≤ (Nat.card S.Cl : ℝ) * B := by
  rw [ipAt_re]
  letI := h.fintypeCl
  calc _ ≤ ∑ _c : S.Cl, B := Finset.sum_le_sum fun c _ => by
        have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
        exact ((mul_le_mul_of_nonneg_right (inv_nat_le_one _) h0).trans (by rw [one_mul])).trans (hB _)
    _ = _ := by simp [Nat.card_eq_fintype_card]

variable {S} in

theorem appOf_le {S' : GSD K} (A : ClsKer S S') (h : S.Ok) (hp : PosAt S v) (hp' : PosAt S' v) (t : ℝ) (ht : 0 ≤ t)
    (φ : S.D → S.V) (d' : S'.D) (hA : ∀ d, OpLe S S' v (A.k d d') t) :
    (S'.pairAt v (A.appOf h S.outSec φ d') (A.appOf h S.outSec φ d')).re ≤
      (Nat.card S.Cl : ℝ) * (t * (S.ipAt h v φ φ).re) := by
  letI := h.fintypeCl
  unfold ClsKer.appOf
  refine (pairAt_sum_le S' v hp' _ _).trans ?_
  rw [Finset.card_univ, Nat.card_eq_fintype_card, ipAt_re, Finset.mul_sum _ _ t]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by positivity)
  rw [pairAt_inv_nat_smul_self]
  have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
  have h1 := hA (S.outSec.rep c) (φ (S.outSec.rep c))
  have h2 := inv_nat_le_one ((S.toCSD h).wt c)
  have h3 : (0 : ℝ) ≤ (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ := by positivity
  change (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ ^ 2 * _ ≤ _
  generalize (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ = w at *
  calc _ ≤ w ^ 2 * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ w * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by ring

end GlobalTheory.ColNorms.SumBound
end
end

section
section
noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem mat_opOf_apply {F F' : GFam K} (M : GFam.Mat F F') (hF : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) (b' : F'.β)
    (d' : F'.D b') :
    ((M.opOf hF s φ b' : (F'.mem b').EqFun) : F'.D b' → F'.V) d' =
      ∑ b, (M b b').appOf (hF b) (s b) (φ b : (F.mem b).D → F.V) d' := by
  simp only [GFam.Mat.opOf, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem step_le (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ)
    (ht : 0 ≤ t) (hh : 0 ≤ h) (hh' : 0 ≤ h') (hp : ∀ b, PosAt ((Q.F i).mem b) v) (hp' : ∀ b, PosAt ((Q.F (i + 1)).mem b) v)
    (hc : ∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) (hc' : ∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h')
    (hk : ∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) (φ : (Q.F i).Forms) :
    (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t *
        (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  have hN : (famIpAt (Q.F i) (Q.hF i) v φ φ).re =
      ∑ b, (((Q.F i).mem b).ipAt (Q.hF i b) v (φ b : ((Q.F i).mem b).D → (Q.F i).V) (φ b : ((Q.F i).mem b).D → (Q.F i).V)).re := by
    unfold famIpAt
    rw [Complex.re_sum]
  have hN0 : 0 ≤ (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
    rw [hN]
    exact Finset.sum_nonneg fun b _ => ipAt_self_nonneg _ v _ (hp b) _
  have hB : ∀ b' d', (((Q.F (i + 1)).mem b').pairAt v ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')
      ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d')).re ≤
      (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by
    intro b' d'
    have e := mat_opOf_apply (Q.kk i) (Q.hF i) (fun b => ((Q.F i).mem b).outSec) φ b' d'
    change ((Q.step i φ b' : ((Q.F (i + 1)).mem b').D → (Q.F (i + 1)).V) d') = _ at e
    rw [e]
    refine (pairAt_sum_le ((Q.F (i + 1)).mem b') v (hp' b') _ _).trans ?_
    rw [Finset.card_univ, hN, Finset.mul_sum _ _ t, Finset.mul_sum _ _ h]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => ?_) (by positivity)
    refine (appOf_le v (Q.kk i b b') (Q.hF i b) (hp b) (hp' b') t ht _ d' fun d => hk b b' d d').trans ?_
    exact mul_le_mul_of_nonneg_right (hc b) (mul_nonneg ht (ipAt_self_nonneg _ v _ (hp b) _))
  have hB0 : 0 ≤ (Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re)) := by positivity
  calc (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re
      ≤ ∑ _b' : (Q.F (i + 1)).β, h' * ((Fintype.card (Q.F i).β : ℝ) * (h * (t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re))) := by
        rw [famIpAt, Complex.re_sum]
        refine Finset.sum_le_sum fun b' _ => ?_
        exact (ipAt_self_le _ v _ (hp' b') _ _ (hB b')).trans (mul_le_mul_of_nonneg_right (hc' b') hB0)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end GlobalTheory.ColNorms.SumBound
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sq_norm_classSumMatrix_le_cauchySchwarz : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (i : ℕ) (v : InfinitePlace K) (t h h' : ℝ), 0 ≤ t → 0 ≤ h → 0 ≤ h' → (∀ b, PosAt ((Q.F i).mem b) v) → (∀ b, PosAt ((Q.F (i + 1)).mem b) v) → (∀ b, (Nat.card ((Q.F i).mem b).Cl : ℝ) ≤ h) → (∀ b, (Nat.card ((Q.F (i + 1)).mem b).Cl : ℝ) ≤ h') → (∀ b b' d d', OpLe ((Q.F i).mem b) ((Q.F (i + 1)).mem b') v ((Q.kk i b b').k d d') t) → ∀ φ : (Q.F i).Forms, (famIpAt (Q.F (i + 1)) (Q.hF (i + 1)) v (Q.step i φ) (Q.step i φ)).re ≤ (Fintype.card (Q.F i).β : ℝ) * (Fintype.card (Q.F (i + 1)).β : ℝ) * h * h' * t * (famIpAt (Q.F i) (Q.hF i) v φ φ).re := by
  atlas_forward_decl GlobalTheory.ColNorms.SumBound.step_le
end

section
section
noncomputable section

namespace GlobalTheory.ColNorms.CplCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

theorem diag_sum_le {V ι : Type} [AddCommGroup V] (B : V →+ V →+ ℝ) (hB : ∀ x, 0 ≤ B x x) (s : Finset ι) (x : ι → V) :
    B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤ s.card * ∑ i ∈ s, B (x i) (x i) := by
  have h1 : ∀ a b, B a b + B b a ≤ B a a + B b b := by
    intro a b
    have := hB (a - b)
    simp only [map_sub, AddMonoidHom.sub_apply] at this
    linarith
  have e : B (∑ i ∈ s, x i) (∑ i ∈ s, x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := by
    rw [map_sum B x s, AddMonoidHom.finset_sum_apply]
    exact Finset.sum_congr rfl fun i _ => map_sum _ _ _
  have e' : ∑ i ∈ s, ∑ j ∈ s, B (x j) (x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := Finset.sum_comm
  have h2 : ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x j) + B (x j) (x i)) ≤ ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x i) + B (x j) (x j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h2
  rw [e]
  linarith

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def reForm (S : GSD K) (v : InfinitePlace K) : S.V →+ S.V →+ ℝ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => (S.pairAt v x y).re) (by
      intro y z
      simp only [GSD.pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]))
    (by
      intro x y
      ext z
      simp only [GSD.pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re,
        AddMonoidHom.mk'_apply, AddMonoidHom.add_apply])

theorem sq_nonneg' {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have e : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      S.gramV.map v.embedding *ᵥ fun i => v.embedding (S.bV.repr x i) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, starRingEnd_apply,
      mul_assoc]
  rw [e]
  exact (Complex.nonneg_iff.1 (Matrix.PosSemidef.dotProduct_mulVec_nonneg h _)).1

theorem sq_sum_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) {ι : Type} (s : Finset ι) (x : ι → S.V) {m : ℝ}
    (hm : (s.card : ℝ) ≤ m) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ m * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re :=
  (diag_sum_le (reForm S v) (sq_nonneg' h) s x).trans
    (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg fun _ _ => sq_nonneg' h _))

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := Nat.cast_inv_le_one n

theorem sq_smul_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (n : ℕ) (x : S.V) :
    (S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x)).re ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := by
  have e : S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x) = (((n : ℝ)⁻¹ * (n : ℝ)⁻¹ : ℝ) : ℂ) * S.pairAt v x x := by
    simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, mul_assoc]
  have h0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := mul_nonneg (by positivity) (sq_nonneg' h x)
  exact mul_le_of_le_one_left h0 (inv_nat_le_one n)

theorem ipAt_re (S : GSD K) (h : S.Ok) (v : InfinitePlace K) (φ : S.D → S.V) :
    (S.ipAt h v φ φ).re = letI := h.fintypeCl
      ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

theorem comp_opLe {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (hS : S.Ok) (v : InfinitePlace K)
    {t₁ t₂ h ny : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hh : 0 ≤ h) (hny : 0 ≤ ny) (p₀ : PosAt S₀ v) (p₁ : PosAt S₁ v)
    (hc : (Nat.card S.Cl : ℝ) ≤ h) (hy : ∀ d, ((Y.ys d).ncard : ℝ) ≤ ny)
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, OpLe S₀ S v (A.k1 d₀ d y) t₁) (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, OpLe S S₁ v (A.k2 d y d₁) t₂)
    (d₀ : S₀.D) (d₁ : S₁.D) : OpLe S₀ S₁ v ((A.comp hS S.outSec).k d₀ d₁) (h ^ 2 * ny ^ 2 * t₁ * t₂) := by
  intro x
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hx := sq_nonneg' p₀ x
  have e : (A.comp hS S.outSec).k d₀ d₁ x = ∑ c : S.Cl, (((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x) := by
    simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [e]
  refine (sq_sum_le p₁ _ _ hc').trans ?_
  have key : ∀ c : S.Cl, (S₁.pairAt v ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))
      ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))).re ≤
      ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))) := by
    intro c
    have hy' : (((Y.fin (S.outSec.rep c)).toFinset.card : ℕ) : ℝ) ≤ ny := by
      rw [← Set.ncard_eq_toFinset_card _ (Y.fin _)]
      exact hy _
    refine (sq_smul_le p₁ _ _).trans ((mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans ?_)
    refine (sq_sum_le p₁ _ _ hy').trans (mul_le_mul_of_nonneg_left ?_ hny)
    refine (Finset.sum_le_card_nsmul _ _ (t₂ * (t₁ * (S₀.pairAt v x x).re)) fun y hy => ?_).trans ?_
    · have hy0 : y ∈ Y.ys (S.outSec.rep c) := (Set.Finite.mem_toFinset _).1 hy
      exact (h2 _ _ y hy0 _).trans (mul_le_mul_of_nonneg_left (h1 _ _ y hy0 _) ht₂)
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hy' (by positivity)
  have h3 := Finset.sum_le_card_nsmul Finset.univ _ _ fun c _ => key c
  rw [nsmul_eq_mul] at h3
  calc _ ≤ h * (h * (ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))))) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right hc' (by positivity))) hh
    _ = _ := by ring

theorem appOf_le {S S' : GSD K} (A : ClsKer S S') (hS : S.Ok) (v : InfinitePlace K) {t h : ℝ} (hh : 0 ≤ h)
    (p' : PosAt S' v) (hc : (Nat.card S.Cl : ℝ) ≤ h) (hA : ∀ d d', OpLe S S' v (A.k d d') t) (φ : S.D → S.V) (d' : S'.D) :
    (S'.pairAt v (A.appOf hS S.outSec φ d') (A.appOf hS S.outSec φ d')).re ≤ h * (t * (S.ipAt hS v φ φ).re) := by
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  unfold ClsKer.appOf
  refine (sq_sum_le p' _ _ hc').trans (mul_le_mul_of_nonneg_left ?_ hh)
  rw [ipAt_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => (sq_smul_le p' _ _).trans ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hA _ _ _) (by positivity)

theorem cpl_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  intro K _ _ _ Q v t₁ t₂ h₀ h h₁ ny ht₁ ht₂ hh₀ hh hh₁ hny p₀ _ p₁ c₀ c c₁ hy k1 k2 φ
  letI := Q.hS₁.fintypeCl
  have hc' : ((Finset.univ : Finset Q.S₁.Cl).card : ℝ) ≤ h₁ := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  set M : ℝ := (Fintype.card (Q.F Q.n).β : ℝ) * (h₀ * (h ^ 2 * ny ^ 2 * t₁ * t₂ *
    (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re)) with hM
  have key : ∀ d : Q.S₁.D, (Q.S₁.pairAt v ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d) ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d)).re ≤ M := by
    intro d
    have e : (Q.cpl φ : Q.S₁.D → Q.S₁.V) d = ∑ b : (Q.F Q.n).β,
        ((Q.cp b).comp Q.hS Q.S.outSec).appOf (Q.hF Q.n b) ((Q.F Q.n).mem b).outSec (φ b) d := by
      simp only [KerChain.cpl, LinearMap.sum_apply, AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]
      rfl
    rw [e]
    refine (sq_sum_le p₁ _ _ (le_of_eq (by rw [Finset.card_univ]))).trans
      (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    unfold famIpAt
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => appOf_le _ _ v hh₀ p₁ (c₀ b)
      (comp_opLe (Q.cp b) Q.hS v ht₁ ht₂ hh hny (p₀ b) p₁ c hy (k1 b) (k2 b)) _ _
  have hF : 0 ≤ (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
    unfold famIpAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b _ => ?_
    rw [ipAt_re]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sq_nonneg' (p₀ b) _)
  have hM0 : 0 ≤ M := by positivity
  rw [ipAt_re]
  refine (Finset.sum_le_card_nsmul _ _ M fun c _ =>
    (mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans (key _)).trans ?_
  rw [nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right hc' hM0).trans (le_of_eq ?_)
  rw [hM]
  ring

end GlobalTheory.ColNorms.CplCS
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coupled_class_sum_cauchy_schwarz : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  atlas_forward_decl GlobalTheory.ColNorms.CplCS.cpl_le
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder IntermediateField

namespace GlobalTheory.ColNorms.ExField

theorem exists_field_holdsData : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] [NumberField K] (σ₀ : K →+* ℂ) (R : Ranks), StandardLatticesGL3.Crv D cc dl → IsDgen D cD → (∀ i < R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ TaylorLogMetric.CoefIn D (B.thZero (R.N i) (R.N (i + 1))) M) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ThetaFieldData B cD σ₀ R M := by
  intro D cc dl B cD K _ _ σ₀ R hC hD hM
  obtain ⟨M₁, hM₁, hE, hc⟩ := hD
  obtain ⟨⟨-, h2, h3⟩, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D
    (GlobalTheory.InducedType.induced_type D).1).2 cc dl hC
  choose Mi hMi hcoef using fun i : Fin R.m => hM i.1 i.2
  let M₀ : IntermediateField ℚ ℂ := σ₀.toRatAlgHom.fieldRange
  haveI f0 : FiniteDimensional ℚ M₀ :=
    (AlgEquiv.ofInjectiveField σ₀.toRatAlgHom).toLinearEquiv.finiteDimensional
  let M₂ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g2 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  let M₃ : IntermediateField ℚ ℂ := ℚ⟮TaylorLogMetric.g3 (TaylorLogMetric.tor0 D cc dl).abelian₂⟯
  haveI f2 : FiniteDimensional ℚ M₂ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h2).isIntegral
  haveI f3 : FiniteDimensional ℚ M₃ :=
    IntermediateField.adjoin.finiteDimensional (mem_algebraicClosure_iff.mp h3).isIntegral
  haveI f1 : FiniteDimensional ℚ M₁ := inferInstance
  haveI f4 : FiniteDimensional ℚ (⨆ i, Mi i : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  let M : IntermediateField ℚ ℂ := (M₀ ⊔ M₁) ⊔ (M₂ ⊔ M₃) ⊔ ⨆ i, Mi i
  have l0 : M₀ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_left)
  have l1 : M₁ ≤ M := le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  have l2 : M₂ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_left)
  have l3 : M₃ ≤ M := le_sup_of_le_left (le_sup_of_le_right le_sup_right)
  have l4 : ∀ i, Mi i ≤ M := fun i => le_sup_of_le_right (le_iSup Mi i)
  refine ⟨M, inferInstance, fun k => l0 ⟨k, rfl⟩, ⟨fun τ x => l1 (hE τ x),
    l2 (IntermediateField.mem_adjoin_simple_self _ _), l3 (IntermediateField.mem_adjoin_simple_self _ _)⟩,
    fun τ => ?_, fun i hi α => l4 ⟨i, hi⟩ (hcoef ⟨i, hi⟩ α)⟩
  obtain ⟨s, hs, -⟩ := hc τ
  exact hs ▸ l1 s.2

end GlobalTheory.ColNorms.ExField
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_containing_coefficientData : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] [NumberField K] (σ₀ : K →+* ℂ) (R : Ranks), StandardLatticesGL3.Crv D cc dl → IsDgen D cD → (∀ i < R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ TaylorLogMetric.CoefIn D (B.thZero (R.N i) (R.N (i + 1))) M) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ThetaFieldData B cD σ₀ R M := by
  atlas_forward_decl GlobalTheory.ColNorms.ExField.exists_field_holdsData
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.BlockNumber

theorem factor_eq_exp {a : ℕ} (nu : DomWeight a) (y : ℕ → ℚ) (b : ℕ) (L : ℝ) (h0 : ∀ l, 0 ≤ nu.w l)
    (hy : ∀ l : Fin a, ((nu.w l : ℤ) : ℚ) = y l) :
    (Real.exp L)⁻¹ ^ GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu * Real.exp 1 * (2 * (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) + 2) ^ (2 * (a * b)) *
      Real.exp (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ)) =
    Real.exp (((∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) - ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) * L) +
      (1 + 2 * ((a : ℝ) * b) * Real.log (2 * ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) + 2))) := by
  have hr : ∀ l : Fin a, ((y l : ℚ) : ℝ) = (nu.w l : ℝ) := fun l => by rw [← hy l]; simp
  have hs : ((∑ i ∈ Finset.range a, y i : ℚ) : ℝ) = (GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu : ℝ) := by
    rw [Finset.sum_range, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]
    have := Int.toNat_of_nonneg (h0 l)
    exact_mod_cast this.symm
  have hp : (∑ i ∈ Finset.range a, Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ)) = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.ph (nu.w i : ℝ) := by
    rw [Finset.sum_range (fun i => Formalism.LatticeIndexTer.ph ((y i : ℚ) : ℝ))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hr l]; rfl
  rw [hs, hp]
  set s := GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.size nu
  have hpos : (0 : ℝ) < 2 * (s : ℝ) + 2 := by positivity
  have e1 : (Real.exp L)⁻¹ ^ s = Real.exp (-((s : ℝ) * L)) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  have e2 : (2 * (s : ℝ) + 2) ^ (2 * (a * b)) = Real.exp (2 * ((a : ℝ) * b) * Real.log (2 * (s : ℝ) + 2)) := by
    conv_lhs => rw [← Real.exp_log hpos, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  rw [e1, e2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1; ring

theorem sq_le_exp (C A g T : ℕ) (G r L : ℝ) (hG : 1 ≤ G) (hT : 1 ≤ T) (hr : 0 ≤ r) (hg : 1 ≤ g) (hA : g ≤ A) :
    (G ^ (C * A) * ((T : ℝ) * G) ^ (2 * (2 * g)) * Real.sqrt (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp (L / 2)) ^ 2 ≤
      Real.exp (L + ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2)) + 2 * (((C : ℝ) + 4) * A * Real.log (G * T)))) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hGT : 1 ≤ G * T := one_le_mul_of_one_le_of_one_le hG hT'
  have hx : (0 : ℝ) < 2 * (g : ℝ) * r + 1 := by positivity
  have h8 : (0 : ℝ) < 8 + 32 * (g : ℝ) * (r / 2) := by positivity
  have e1 : Real.exp ((g : ℝ) * Real.log (8 + 32 * (g : ℝ) * (r / 2))) = 8 ^ g * (2 * (g : ℝ) * r + 1) ^ g := by
    rw [Real.exp_nat_mul, Real.exp_log h8, ← mul_pow]; congr 1; ring
  have e2 : Real.exp (2 * (((C : ℝ) + 4) * A * Real.log (G * T))) = (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) := by
    rw [← pow_add]
    conv_rhs => rw [← Real.exp_log (show (0 : ℝ) < G * T by linarith), ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have e3 : Real.exp (L / 2) ^ 2 = Real.exp L := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [Real.exp_add, Real.exp_add, e1, e2, mul_pow, mul_pow, mul_pow, e3, Real.sq_sqrt (by positivity), ← pow_mul, ← pow_mul]
  have b1 : G ^ (C * A * 2) ≤ (G * T) ^ (2 * (C * A)) := by
    rw [mul_comm (C * A) 2]
    exact pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_right (by linarith) hT') _
  have b2 : ((T : ℝ) * G) ^ (2 * (2 * g) * 2) ≤ (G * T) ^ (8 * A) := by
    rw [mul_comm (T : ℝ) G]
    exact pow_le_pow_right₀ hGT (by omega)
  have b3 : (3 : ℝ) ≤ 8 ^ g := by
    calc (3 : ℝ) ≤ 8 ^ 1 := by norm_num
      _ ≤ 8 ^ g := pow_le_pow_right₀ (by norm_num) hg
  have hG0 : 0 ≤ G := by linarith
  calc G ^ (C * A * 2) * ((T : ℝ) * G) ^ (2 * (2 * g) * 2) * (3 * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L
      ≤ (G * T) ^ (2 * (C * A)) * (G * T) ^ (8 * A) * (8 ^ g * (2 * (g : ℝ) * r + 1) ^ g) * Real.exp L := by gcongr
    _ = _ := by ring

theorem tmax_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  intro C
  refine ⟨(C : ℝ) + 4, by positivity, ?_⟩
  intro N δ T i ι _ pl nu logOm logTh hi hT h0 hy
  have hm := N.R.two_le_m
  have hk := N.R.m_add_three_le_k
  have ha : 1 ≤ N.R.N i := by unfold Ranks.N; omega
  have hb : 1 ≤ N.R.N (i + 1) := by unfold Ranks.N; omega
  have hf : 1 ≤ N.R.f := by
    have : 0 < N.R.ord := N.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have haN : N.R.N i ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi.le) _
  have hbN : N.R.N (i + 1) ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _
  have hg : 1 ≤ N.R.f * N.R.N i * N.R.N (i + 1) := Nat.mul_pos (Nat.mul_pos hf ha) hb
  have hA : N.R.f * N.R.N i * N.R.N (i + 1) ≤ N.R.f * N.R.m ^ 2 * N.Nm ^ 2 := by
    have h1 : 1 ≤ N.R.m ^ 2 := Nat.one_le_pow _ _ (by omega)
    calc N.R.f * N.R.N i * N.R.N (i + 1) = N.R.f * 1 * (N.R.N i * N.R.N (i + 1)) := by ring
      _ ≤ N.R.f * N.R.m ^ 2 * (N.Nm * N.Nm) := by gcongr
      _ = _ := by ring
  have hG : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast (N.g_prime 0).one_le) (by exact_mod_cast (N.g_prime 1).one_le)
  have hr : 0 ≤ N.rd := by unfold NumDatum.rd Formalism.HC.HostRaw.rd; positivity
  have key := sq_le_exp C _ _ T _ N.rd logTh hG (by omega) hr hg hA
  have hprod := fun z : RPl N.R => factor_eq_exp (nu (pl z)) (N.nu δ (i + 1) z) (N.R.N (i + 1)) (logOm z) (h0 _) (hy z)
  unfold GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax
  rw [← pl.prod_comp]
  simp only [Equiv.symm_apply_apply]
  rw [Finset.prod_congr rfl fun z _ => hprod z, ← Real.exp_sum]
  have e1 : C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2 = C * (N.R.f * N.R.m ^ 2 * N.Nm ^ 2) := by ring
  have e2 : 2 * N.R.f * N.R.N i * N.R.N (i + 1) = 2 * (N.R.f * N.R.N i * N.R.N (i + 1)) := by ring
  have e3 : ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) = (T : ℝ) * ((N.g 0 : ℝ) * N.g 1) := by push_cast; ring
  rw [e1, e2, e3]
  refine (mul_le_mul_of_nonneg_right key (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  unfold kernelBound_sq NumDatum.nuAbs NumDatum.v
  simp only [Nat.add_sub_cancel, Finset.sum_add_distrib, Nat.cast_one, mul_one, Real.log_one]
  push_cast
  simp only [mul_assoc]
  ring

end GlobalTheory.BlockNumber
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jetBlockBound_le_exp_kernelBound : ∀ C : ℕ, ∃ CK : ℝ, 0 ≤ CK ∧ ∀ (N : NumDatum) (δ : Code N) (T : ℕ) (i : ℕ) (ι : Type) [Fintype ι] (pl : RPl N.R ≃ ι) (nu : ι → DomWeight (N.R.N i)) (logOm : RPl N.R → ℝ) (logTh : ℝ), i < N.R.m → 2 ≤ T → (∀ τ l, 0 ≤ (nu τ).w l) → (∀ (z : RPl N.R) (l : Fin (N.R.N i)), (((nu (pl z)).w l : ℤ) : ℚ) = N.nu δ (i + 1) z l) → GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry.tmax (N.R.N (i + 1)) nu (((N.g 0 : ℝ) * N.g 1) ^ (C * N.R.f * N.R.m ^ 2 * N.Nm ^ 2) * ((T * (N.g 0 * N.g 1) : ℕ) : ℝ) ^ (2 * (2 * N.R.f * N.R.N i * N.R.N (i + 1))) * Real.sqrt (3 * (2 * ((N.R.f * N.R.N i * N.R.N (i + 1) : ℕ) : ℝ) * N.rd + 1) ^ (N.R.f * N.R.N i * N.R.N (i + 1))) * Real.exp (logTh / 2)) (fun τ => Real.exp (logOm (pl.symm τ))) ≤ Real.exp (kernelBound_sq N δ T CK (i + 1) logOm logTh 1 1 1 1) := by
  atlas_forward_decl GlobalTheory.BlockNumber.tmax_le_exp_kernelBound
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ColNorms

theorem errUnit_nonneg (N : NumDatum) {T : ℕ} (hT : 1 ≤ T) : 0 ≤ errUnit N T := by
  have h0 : (1 : ℝ) ≤ N.g 0 := by exact_mod_cast (N.g_prime 0).one_lt.le
  have h1 : (1 : ℝ) ≤ N.g 1 := by exact_mod_cast (N.g_prime 1).one_lt.le
  have h2 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h3 : 0 ≤ Real.log ((N.g 0 : ℝ) * N.g 1 * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h0 h1) h2)
  unfold errUnit
  positivity

theorem kernelBound_ge (N : NumDatum) (δ : Code N) (T : ℕ) (C₁ C₂ : ℝ) (j : ℕ) (lo : RPl N.R → ℝ) (lt : ℝ) (h h' n n' : ℕ) :
    kernelBound_sq N δ T C₁ j lo lt 1 1 1 1 + 2 * (C₂ * errUnit N T) ≤ kernelBound_sq N δ T (C₁ + C₂) j lo lt h h' n n' := by
  have a1 : 0 ≤ Real.log ((h : ℝ) * h') := by exact_mod_cast Real.log_natCast_nonneg (h * h')
  have a2 : 0 ≤ Real.log ((n : ℝ) * n') := by exact_mod_cast Real.log_natCast_nonneg (n * n')
  unfold kernelBound_sq errUnit
  simp only [Nat.cast_one, mul_one, Real.log_one]
  nlinarith

theorem SmallDatum.mono {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    {S : Finset (HeightOneSpectrum (𝓞 E))} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {c : ℕ}
    {Ξ : HomE E a b → K} {β β' : ℝ} (h : SmallDatum S N N' c Ξ β) (hβ : β ≤ β') : SmallDatum S N N' c Ξ β' :=
  ⟨h.1, h.2.1, fun σ x => (h.2.2 σ x).trans hβ⟩

end GlobalTheory.ColNorms
end
end
