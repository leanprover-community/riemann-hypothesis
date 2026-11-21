import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality
import BuildAid.ForwardExisting
import Formalism.RealPlaceAnalysis.StatementE
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.QuantumDeterminantEquality : CompanionTheory.RgExh.Hk.QdetEq := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | exact GlobalTheory.CompanionTheory.RgExhHecke.qdetEq | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.qdetEq <;> assumption)
end

section
section
open Finset

namespace GlobalTheory.CompanionTheory.HeckeCapelli

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry capelliExpand)

theorem capelli_entry_apply {n : ℕ} (X : GMod n) (x : ℂ) (d b : Fin n) (v : X.V) :
    capEntry X.E x d b v = X.E d b v + if d = b then x • v else 0 := by
  unfold capEntry
  split_ifs <;> simp [Module.algebraMap_end_apply]

theorem capelli_component {m : ℕ} (X : GMod (m + 1)) (x : ℂ) (f : Fin (m + 1) → X.V) (b : Fin (m + 1)) :
    ∑ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) = capelliC X.E x (f b) := by
  have key := (capelliExpand (Module.End ℂ X.V) m X.E x X.gl).1 b
  have h : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) =
      if b = c then capelliC X.E x (f c) else 0 := by
    intro c
    have := LinearMap.congr_fun (key c) (f c)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply] at this
    rw [this]
    split_ifs <;> simp
  simp only [h]
  simp

theorem omMinor : OmMinor := by
  intro m X x
  rw [GlobalTheory.T.QuantumDeterminantEquality (m + 1) X.V X.E x]
  refine LinearMap.ext fun f => funext fun b => ?_
  have h := capelli_component X x f b
  simp only [capelli_entry_apply, smul_add, sum_add_distrib] at h
  simp only [LinearMap.compLeft_apply, Function.comp_apply, ← h]
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
    Pi.add_apply, Pi.smul_apply, om_apply]
  simp only [minorOp, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  refine (add_comm _ _).trans ?_
  congr 1
  · exact sum_comm
  · rw [sum_comm]
    simp [smul_sum, smul_comm x]

end GlobalTheory.CompanionTheory.HeckeCapelli
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.OmegaMinor : CompanionTheory.RgExh.Hk.OmMinor := by
  atlas_forward_decl GlobalTheory.CompanionTheory.HeckeCapelli.omMinor
end

section
section
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh

namespace GlobalTheory.CompanionTheory.RgExhHecke

variable {n : ℕ}

theorem capEntry_tensE_apply (X : GMod n) (x : ℂ) (a b : Fin n) (f : Fin n → X.V) (d : Fin n) :
    capEntry (tensE X) x a b f d = capEntry X.E x a b (f d) + if d = a then f b else 0 := by
  unfold capEntry
  by_cases h : a = b
  · simp [h, tensE_apply, Module.algebraMap_end_apply]; abel
  · simp [h, tensE_apply]

theorem capEntry_apply_shift {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (x : ℂ) (a b : Fin n) (v : V) :
    capEntry E x a b v = capEntry E (x - 1) a b v + if b = a then v else 0 := by
  unfold capEntry
  by_cases h : a = b
  · subst h
    simp [Module.algebraMap_end_apply, sub_smul, add_assoc]
  · simp [h, Ne.symm h]

theorem sum_pair_swap {M : Type*} [AddCommMonoid M] {q : ℕ} (Φ : Fin (q + 2) → Fin (q + 1) → M) :
    ∑ i, ∑ k, Φ i k = ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), Φ (i.succAbove k) (k.predAbove i) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  let τ : Equiv.Perm (Fin (q + 2) × Fin (q + 1)) :=
    Function.Involutive.toPerm (fun p => (p.1.succAbove p.2, p.2.predAbove p.1)) (by
      rintro ⟨i, k⟩
      simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove])
  exact (Equiv.sum_comp τ (fun p => Φ p.1 p.2)).symm

theorem sign_pair_swap {q : ℕ} (i : Fin (q + 2)) (k : Fin (q + 1)) :
    (-1 : ℂ) ^ (i.succAbove k : ℕ) * (-1) ^ (k.predAbove i : ℕ) = -((-1) ^ (i : ℕ) * (-1) ^ (k : ℕ)) := by
  have h : (i.succAbove k : ℕ) + (k.predAbove i : ℕ) + 1 = (i : ℕ) + (k : ℕ) ∨
      (i.succAbove k : ℕ) + (k.predAbove i : ℕ) = (i : ℕ) + (k : ℕ) + 1 := by
    simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val, Fin.val_pred,
      Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
    split_ifs <;> omega
  rw [← pow_add, ← pow_add]
  rcases h with h | h
  · rw [← h, pow_succ]; ring
  · rw [h, pow_succ]; ring

theorem cminor_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (R C : Fin 0 → Fin n) (x : ℂ) : cminor E R C x = 1 := by
  simp [cminor]

section Key

variable {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) {q : ℕ}
  (R C : Fin (q + 2) → Fin n) (x : ℂ) (f : Fin n → V) (d : Fin n)

def dbl (i : Fin (q + 2)) (k : Fin (q + 1)) (l : Fin (q + 1)) : V :=
  cminor E ((R ∘ i.succAbove) ∘ k.succAbove) ((C ∘ Fin.succ) ∘ l.succAbove) (x - 1 - 1) (f (C l.succ))

theorem dbl_swap (i : Fin (q + 2)) (k l : Fin (q + 1)) :
    dbl E R C x f (i.succAbove k) (k.predAbove i) l = dbl E R C x f i k l := by
  unfold dbl
  have : (R ∘ (i.succAbove k).succAbove) ∘ (k.predAbove i).succAbove = (R ∘ i.succAbove) ∘ k.succAbove := by
    funext t
    simp only [Function.comp, Fin.succAbove_succAbove_succAbove_predAbove]
  rw [this]

theorem minor_expand (i : Fin (q + 2)) (l : Fin (q + 1)) :
    cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) =
      ∑ k : Fin (q + 1), ((-1 : ℂ) ^ (k : ℕ)) •
        capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) := by
  rw [cminor_succ_col]
  have h0 : (C ∘ l.succ.succAbove) 0 = C 0 := by simp
  have h1 : (C ∘ l.succ.succAbove) ∘ Fin.succ = (C ∘ Fin.succ) ∘ l.succAbove := by
    funext t
    simp [Function.comp, Fin.succ_succAbove_succ]
  rw [h0, h1]
  simp [dbl, LinearMap.sum_apply, Module.End.mul_apply]

theorem key_identity :
    (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • capEntry E x (R i) (C 0)
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0)) +
      (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if C 0 = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0)) =
    ∑ i : Fin (q + 2), ∑ l : Fin (q + 1), if d = R i then
      ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
        cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0 := by
  have h1 : (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • capEntry E x (R i) (C 0)
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0)) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ)) •
        capEntry E x (R i) (C 0) (if d = R (i.succAbove k) then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) := by
    simp only [map_sum, Finset.smul_sum, Function.comp]
  have h2 : (∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
        (∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if C 0 = (R ∘ i.succAbove) k then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0)) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), ((-1 : ℂ) ^ (i : ℕ)) •
        (if d = R i then (if C 0 = R (i.succAbove k) then
          ((-1 : ℂ) ^ ((k : ℕ) + (l : ℕ))) • dbl E R C x f i k l else 0) else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : d = R i <;> simp [h, Finset.smul_sum]
  have h3 : (∑ i : Fin (q + 2), ∑ l : Fin (q + 1), if d = R i then
      ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
        cminor E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0) =
      ∑ i : Fin (q + 2), ∑ k : Fin (q + 1), ∑ l : Fin (q + 1), if d = R i then
        ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) • ((-1 : ℂ) ^ (k : ℕ)) •
          capEntry E (x - 1) (R (i.succAbove k)) (C 0) (dbl E R C x f i k l) else 0 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h : d = R i
    · simp only [h, if_true, minor_expand, Finset.smul_sum]
    · simp [h]
  rw [h1, h2, h3, sum_pair_swap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fin.succAbove_succAbove_predAbove, dbl_swap]
  have hs : (-1 : ℂ) ^ (i.succAbove k : ℕ) * (-1) ^ (((k.predAbove i : Fin (q + 1)) : ℕ) + (l : ℕ)) =
      -((-1) ^ (i : ℕ) * (-1) ^ ((k : ℕ) + (l : ℕ))) := by
    rw [pow_add, ← mul_assoc, sign_pair_swap, pow_add]; ring
  by_cases hd : d = R i
  · simp only [hd, if_true, map_smul, smul_smul, hs]
    rw [capEntry_apply_shift E x (R (i.succAbove k)) (C 0)]
    by_cases hc : C 0 = R (i.succAbove k)
    · simp only [hc, if_true, smul_add, Fin.val_succ, pow_add, pow_one]
      module
    · simp only [hc, if_false, add_zero, smul_zero, Fin.val_succ, pow_add, pow_one]
      module
  · simp [hd]

end Key

theorem cminor_tensE_apply (X : GMod n) (q : ℕ) : ∀ (R C : Fin (q + 1) → Fin n) (x : ℂ)
    (f : Fin n → X.V) (d : Fin n),
    cminor (tensE X) R C x f d = cminor X.E R C x (f d) +
      ∑ i : Fin (q + 1), ∑ j : Fin (q + 1), if d = R i then
        ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
          cminor X.E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) (f (C j)) else 0 := by
  induction q with
  | zero =>
    intro R C x f d
    rw [cminor_succ_col, cminor_succ_col X.E]
    simp [cminor_zero, capEntry_tensE_apply, Module.End.mul_apply, LinearMap.sum_apply]
  | succ q ih =>
    intro R C x f d
    have hL : cminor (tensE X) R C x f d =
        ∑ i : Fin (q + 2), ((-1 : ℂ) ^ (i : ℕ)) •
          (capEntry X.E x (R i) (C 0) (cminor (tensE X) (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) f d) +
            if d = R i then cminor (tensE X) (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) f (C 0) else 0) := by
      rw [cminor_succ_col]
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
        Module.End.mul_apply, capEntry_tensE_apply]
    have hR := key_identity X.E R C x f d
    have hsplit : ∀ i : Fin (q + 2), (∑ j : Fin (q + 2), if d = R i then
          ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) •
            cminor X.E (R ∘ i.succAbove) (C ∘ j.succAbove) (x - 1) (f (C j)) else 0) =
        ((-1 : ℂ) ^ (i : ℕ)) • (if d = R i then
          cminor X.E (R ∘ i.succAbove) (C ∘ Fin.succ) (x - 1) (f (C 0)) else 0) +
        ∑ l : Fin (q + 1), if d = R i then
          ((-1 : ℂ) ^ ((i : ℕ) + ((l.succ : Fin (q + 2)) : ℕ))) •
            cminor X.E (R ∘ i.succAbove) (C ∘ l.succ.succAbove) (x - 1) (f (C l.succ)) else 0 := by
      intro i
      rw [Fin.sum_univ_succ]
      by_cases h : d = R i
      · simp [h, Fin.succAbove_zero]
      · simp [h]
    rw [hL]
    simp only [hsplit, Finset.sum_add_distrib]
    rw [← hR, cminor_succ_col X.E R C x]
    have hit : ∀ (p : Prop) [Decidable p] (a b : X.V),
        (if p then a + b else 0) = (if p then a else 0) + (if p then b else 0) := by
      intro p _ a b
      split_ifs <;> simp
    simp only [ih, hit, map_add, smul_add, Finset.sum_add_distrib, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.mul_apply]
    simp only [dbl, Function.comp_apply]
    abel

abbrev minorOp {m : ℕ} (X : GMod (m + 1)) (y : ℂ) : Module.End ℂ (Fin (m + 1) → X.V) :=
  Hk.minorOp X y

theorem minorOp_apply {m : ℕ} (X : GMod (m + 1)) (y : ℂ) (f : Fin (m + 1) → X.V) (a : Fin (m + 1)) :
    minorOp X y f a = ∑ c : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) • cminor X.E a.succAbove c.succAbove y (f c) :=
  rfl

theorem rankOneTens : ∀ (m : ℕ) (X : GMod (m + 1)) (u : ℂ),
    qdet (tensE X) u = (qdet X.E u).compLeft (Fin (m + 1)) + minorOp X (u - 1) := by
  intro m X u
  rw [qdet_eq_capelliC, qdet_eq_capelliC]
  refine LinearMap.ext fun f => funext fun d => ?_
  rw [capelliC, capelliC, cminor_tensE_apply X m id id u f d]
  simp only [LinearMap.add_apply, Pi.add_apply, minorOp_apply, LinearMap.compLeft_apply,
    Function.comp_apply, id_eq, Function.id_comp]
  simp

theorem rankOne : Hk.RankOne := rankOneTens

end GlobalTheory.CompanionTheory.RgExhHecke
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HeckeRankOne : CompanionTheory.RgExh.Hk.RankOne := by
  atlas_forward_decl GlobalTheory.CompanionTheory.RgExhHecke.rankOne
end

section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExh

open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

theorem commute_qdet_of {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (T : A)
    (h : ∀ a b, Commute (E a b) T) (u : ℂ) : Commute (qdet E u) T := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) ?_
  refine Commute.list_prod_left _ _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  unfold Formalism.REAL.Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

theorem commute_compLeft_om {n : ℕ} (X : GMod n) (u : ℂ) :
    Commute ((qdet X.E u).compLeft (Fin n)) (om X) := by
  have hc := Formalism.REAL.qDetCentral (Module.End ℂ X.V) n X.E X.gl u
  unfold Commute SemiconjBy
  refine LinearMap.ext fun f => funext fun b => ?_
  simp only [Module.End.mul_apply, LinearMap.compLeft_apply, Function.comp_apply, om, LinearMap.coe_mk,
    AddHom.coe_mk, map_sum]
  exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hc a b) (f a)

theorem qdetTens : QdetTens := by
  intro n X u
  rcases n with _ | m
  · exact LinearMap.ext fun f => funext fun i => i.elim0
  · have hT : ∀ a b, Commute (tensE X a b) (om X) := by
      intro a b
      unfold Commute SemiconjBy
      refine LinearMap.ext fun f => funext fun c => ?_
      have key : ∀ d, X.E a b (X.E d c (f d)) =
          ((if b = d then X.E a c else 0) - (if c = a then X.E d b else 0)) (f d) + X.E d c (X.E a b (f d)) := by
        intro d
        have h1 := LinearMap.congr_fun (X.gl a b d c) (f d)
        rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at h1
        exact h1
      simp only [Module.End.mul_apply, tensE, eOp, om, LinearMap.add_apply, LinearMap.compLeft_apply,
        Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, map_sum, map_add]
      rw [Finset.sum_congr rfl fun d _ => key d]
      by_cases hca : c = a
      · subst hca
        simp [Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, Finset.sum_sub_distrib]
        simp only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        abel
      · simp [Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, hca, Finset.sum_sub_distrib]
        simp only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        abel
    have hC : Commute (qdet (tensE X) u) (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X) :=
      Commute.add_right ((Commute.one_right _).smul_right u) (commute_qdet_of _ _ hT u)
    have hD : Commute ((qdet X.E u).compLeft (Fin (m + 1)))
        (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X) :=
      Commute.add_right ((Commute.one_right _).smul_right u) (commute_compLeft_om X u)
    rw [hC.eq, GlobalTheory.T.HeckeRankOne m X u, mul_add, GlobalTheory.T.OmegaMinor m X u, ← hD.eq]
    simp only [add_smul, one_smul, mul_add, mul_one]
    abel

end GlobalTheory.CompanionTheory.RgExh
end
end
