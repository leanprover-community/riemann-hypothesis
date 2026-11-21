import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFamilyFiniteCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocRingIso
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpLocalChart
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpOverLocFiniteCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingIsLocal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingNoetherian
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHomLocRingDimLe
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AssemblyDimensionInequality

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace BlowUpOverLocInChart

section Graded

variable {R : Type*} [CommRing R] {κ : Type*} [DecidableEq κ] {E : κ → Type*}

theorem weight_blockWeight (d : (Σ o, E o) →₀ ℕ) :
    Finsupp.weight (blockWeight E) d = ⇑(d.mapDomain Sigma.fst) := by
  induction d using Finsupp.induction_linear with
  | zero => funext o; simp
  | add x y hx hy => rw [map_add, hx, hy, Finsupp.mapDomain_add, Finsupp.coe_add]
  | single v n =>
    rw [Finsupp.weight_single, Finsupp.mapDomain_single]
    funext o
    by_cases h : v.1 = o
    · subst h; simp [blockWeight]
    · simp [blockWeight, Pi.single_apply, Ne.symm h]

theorem coeff_eval₂_C_mul_X_fst {B : Type*} [CommRing B] (f : R →+* B) (a : (Σ o, E o) → B)
    (p : MvPolynomial (Σ o, E o) R) (e : κ →₀ ℕ) :
    coeff e (eval₂ (C.comp f) (fun v => C (a v) * X v.1) p) =
      eval₂ f a (weightedHomogeneousComponent (blockWeight E) ⇑e p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have hX : (monomial (d.mapDomain Sigma.fst) (1 : B) : MvPolynomial κ B) =
        d.prod fun v n => (X v.1 : MvPolynomial κ B) ^ n := by
      rw [← rename_monomial, monomial_eq, C_1, one_mul, map_finsuppProd]
      simp [rename_X]
    have hC : (C (d.prod fun v n => a v ^ n) : MvPolynomial κ B) = d.prod fun v n => C (a v) ^ n := by
      rw [map_finsuppProd]
      simp
    have h : eval₂ (C.comp f) (fun v => C (a v) * X v.1) (monomial d c) =
        C (eval₂ f a (monomial d c)) * monomial (d.mapDomain Sigma.fst) 1 := by
      rw [eval₂_monomial, eval₂_monomial, hX, map_mul, hC]
      simp only [mul_pow, Finsupp.prod_mul, RingHom.coe_comp, Function.comp_apply]
      ring
    rw [h, coeff_C_mul, coeff_monomial, weightedHomogeneousComponent_monomial', weight_blockWeight]
    by_cases hd : d.mapDomain Sigma.fst = e
    · subst hd
      simp
    · rw [if_neg hd, if_neg (fun h => hd (DFunLike.coe_injective h)), mul_zero, eval₂_zero]
  | add p q hp hq => simp only [eval₂_add, map_add, coeff_add, hp, hq]

theorem eval₂_C_mul_X_fst_of_homog [Fintype κ] {B : Type*} [CommRing B] (f : R →+* B)
    (a : (Σ o, E o) → B) {p : MvPolynomial (Σ o, E o) R} {b : κ → ℕ}
    (hp : IsWeightedHomogeneous (blockWeight E) p b) :
    eval₂ (C.comp f) (fun v => C (a v) * X v.1) p =
      monomial (Finsupp.equivFunOnFinite.symm b) (eval₂ f a p) := by
  classical
  ext e
  rw [coeff_eval₂_C_mul_X_fst, coeff_monomial]
  by_cases he : (⇑e : κ → ℕ) = b
  · have : Finsupp.equivFunOnFinite.symm b = e := by
      rw [← he]
      exact Finsupp.equivFunOnFinite.symm_apply_apply e
    rw [if_pos this, he, hp.weightedHomogeneousComponent_same]
  · have : Finsupp.equivFunOnFinite.symm b ≠ e := fun h => he (by rw [← h]; simp)
    rw [if_neg this, hp.weightedHomogeneousComponent_ne _ he, eval₂_zero]

theorem eval₂_mul_fst_of_homog [Fintype κ] {B : Type*} [CommRing B] (f : R →+* B)
    (x : (Σ o, E o) → B) (s : κ → B) {p : MvPolynomial (Σ o, E o) R} {b : κ → ℕ}
    (hp : IsWeightedHomogeneous (blockWeight E) p b) :
    eval₂ f (fun v => x v * s v.1) p = eval₂ f x p * ∏ o, s o ^ b o := by
  have h1 : eval₂ f (fun v => x v * s v.1) p =
      eval s (eval₂ (C.comp f) (fun v => C (x v) * X v.1) p) := by
    rw [eval, eval₂_comp_left]
    congr 1
    · ext r
      simp
    · funext v
      simp
  rw [h1, eval₂_C_mul_X_fst_of_homog f x hp, eval_monomial,
    Finsupp.prod_fintype _ _ (fun o => pow_zero _)]
  simp

end Graded

section Lift

variable {K : Type} [DecidableEq K] {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem component_liftForm (g : MRing ι R) (c : K → ℕ) :
    weightedHomogeneousComponent (blockWeight (extIdx ι J)) (liftMDeg c) (liftForm g) =
      liftForm (weightedHomogeneousComponent (blockWeight ι) c g) := by
  classical
  have key : ∀ a : (Σ k, ι k) →₀ ℕ,
      Finsupp.weight (blockWeight (extIdx ι J))
        (a.mapDomain fun v : Σ k, ι k => (⟨some v.1, v.2⟩ : Σ o, extIdx ι J o)) =
      liftMDeg (Finsupp.weight (blockWeight ι) a) := by
    intro a
    induction a using Finsupp.induction_linear with
    | zero => funext o; cases o <;> simp [liftMDeg]
    | add x y hx hy =>
      rw [Finsupp.mapDomain_add, map_add, map_add, hx, hy]
      funext o; cases o <;> simp [liftMDeg]
    | single v n =>
      rw [Finsupp.mapDomain_single, Finsupp.weight_single, Finsupp.weight_single]
      funext o; cases o <;> simp [liftMDeg, blockWeight, Pi.single_apply]
  have inj : ∀ y z : K → ℕ, liftMDeg y = liftMDeg z ↔ y = z :=
    fun y z => ⟨fun h => funext fun k => congrFun h (some k), fun h => h ▸ rfl⟩
  induction g using MvPolynomial.induction_on' with
  | monomial d r =>
    simp only [liftForm, rename_monomial]
    rw [weightedHomogeneousComponent_monomial', weightedHomogeneousComponent_monomial', key, inj]
    split_ifs
    · simp [rename_monomial]
    · simp
  | add p q hp hq => simp only [map_add, hp, hq]

end Lift

end BlowUpOverLocInChart

set_option maxHeartbeats 1600000 in
open BlowUpOverLocInChart in

theorem BlowUpOverLocInChart.proof : BlowUpOverLocInChart.Statement.{u} := by
  intro R _ K _ _ ι J P W _ hPh hW hPW hrel N u hu j huj
  set L := FractionRing (MRing ι R ⧸ P)
  let ev : MRing ι R →+* L := (algebraMap (MRing ι R ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hev : ∀ g, ev g = algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P g) := fun _ => rfl
  have hne : ∀ g, g ∉ W → ev g ≠ 0 := fun g hg =>
    HomLocRingMem.algebraMap_mk_ne_zero P (fun h => hg (hPW h))
  obtain ⟨Cr, hCr⟩ : ∃ Cr : Subring L, Cr = Subring.closure ((homLocRing P W : Set L) ∪ Set.range fun k =>
      algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P (u k)) /
        algebraMap (MRing ι R ⧸ P) L (Ideal.Quotient.mk P (u j))) := ⟨_, rfl⟩
  rw [← hCr]
  have hgen : ∀ (c : K → ℕ) (x y : MRing ι R), IsMultiHomog x c → IsMultiHomog y c → y ∉ W →
      ev x / ev y ∈ Cr := fun c x y hx hy hyW => by
    rw [hCr]
    exact Subring.subset_closure (Or.inl (Subring.subset_closure ⟨c, x, y, hx, hy, hyW, rfl⟩))
  have hrange : ∀ l, ev (u l) / ev (u j) ∈ Cr := fun l => by
    rw [hCr]
    exact Subring.subset_closure (Or.inr ⟨l, rfl⟩)
  clear hCr
  have h1W : (1 : MRing ι R) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one W).mpr h)
  intro f hf
  by_contra hfC

  let 𝔇 : Ideal Cr :=
    { carrier := {d | (d : L) * f ∈ Cr}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Subring.coe_add, add_mul] at ha hb ⊢
        exact Cr.add_mem ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq, ZeroMemClass.coe_zero, zero_mul]
        exact Cr.zero_mem
      smul_mem' := by
        intro c d hd
        simp only [Set.mem_setOf_eq, smul_eq_mul, Subring.coe_mul, mul_assoc] at hd ⊢
        exact Cr.mul_mem c.2 hd }
  have h𝔇 : 𝔇 ≠ ⊤ := by
    intro h
    have h1 : (1 : Cr) ∈ 𝔇 := by rw [h]; trivial
    have h2 : ((1 : Cr) : L) * f ∈ Cr := h1
    rw [OneMemClass.coe_one, one_mul] at h2
    exact hfC h2
  obtain ⟨𝔮, h𝔮, h𝔇𝔮⟩ := Ideal.exists_le_maximal 𝔇 h𝔇
  have h𝔮p : 𝔮.IsPrime := h𝔮.isPrime
  have h0mem : (0 : Cr) ∈ 𝔮 := 𝔮.zero_mem

  choose i hi using hrel
  have hXne : ∀ k, ev (X ⟨k, i k⟩) ≠ 0 := fun k => hne _ (hi k)
  have hune : ev (u j) ≠ 0 := HomLocRingMem.algebraMap_mk_ne_zero P huj
  let Dinv : Option K → L := fun o => Option.elim o (ev (u j))⁻¹ fun k => (ev (X ⟨k, i k⟩))⁻¹
  let x : (Σ o, extIdx ι J o) → L := fun v => ev (blowUpAtOne u v)
  let aL : (Σ o, extIdx ι J o) → L := fun v => x v * Dinv v.1
  have haL : ∀ v, aL v ∈ Cr := by
    rintro ⟨o, l⟩
    cases o with
    | none =>
      simpa [aL, x, Dinv, blowUpAtOne, div_eq_mul_inv] using hrange l
    | some k =>
      have h := hgen (blockWeight ι ⟨k, l⟩) (X ⟨k, l⟩) (X ⟨k, i k⟩) (isWeightedHomogeneous_X R _ _)
        (isWeightedHomogeneous_X R _ _) (hi k)
      simpa [aL, x, Dinv, blowUpAtOne, div_eq_mul_inv] using h
  obtain ⟨aC, haC⟩ : ∃ aC : (Σ o, extIdx ι J o) → Cr, ∀ v, (aC v : L) = aL v := ⟨fun v => ⟨aL v, haL v⟩, fun _ => rfl⟩
  have hcst : ∀ r : R, ev (C r) ∈ Cr := fun r => by
    have h := hgen 0 (C r) 1 (isWeightedHomogeneous_C _ _) (isWeightedHomogeneous_one _ _) h1W
    simpa using h
  obtain ⟨fC, hfCv⟩ : ∃ fC : R →+* Cr, ∀ r, (fC r : L) = ev (C r) :=
    ⟨(ev.comp C).codRestrict Cr hcst, fun _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MvPolynomial (Σ o, extIdx ι J o) R →+* MvPolynomial (Option K) Cr,
      ψ = eval₂Hom (C.comp fC) fun v => C (aC v) * X v.1 := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : Ideal (MRing (extIdx ι J) R),
      Q = RingHom.ker ((MvPolynomial.map (Ideal.Quotient.mk 𝔮)).comp ψ) := ⟨_, rfl⟩
  have memQ : ∀ F, F ∈ Q ↔ ∀ e : Option K →₀ ℕ,
      eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) ∈ 𝔮 := by
    intro F
    simp only [hQdef, hψ, RingHom.mem_ker, RingHom.comp_apply, MvPolynomial.ext_iff, coeff_map, coeff_zero,
      Ideal.Quotient.eq_zero_iff_mem, coe_eval₂Hom, coeff_eval₂_C_mul_X_fst]

  have hσ : ∀ F, eval₂ (ev.comp C) x F = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) := by
    intro F
    have h : (eval₂Hom (ev.comp C) x : MRing (extIdx ι J) R →+* L) =
        (algebraMap (MRing ι R ⧸ P) L).comp (blowUpEval P u) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [ev, blowUpEval]
        try rfl
      · rintro ⟨o, l⟩
        cases o <;> simp [x, ev, blowUpEval, blowUpAtOne, blowUpSubst]
    exact DFunLike.congr_fun h F
  have hval : ∀ (F : MRing (extIdx ι J) R) (b : Option K → ℕ), IsMultiHomog F b →
      ((eval₂ fC aC F : Cr) : L) = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) * ∏ o, Dinv o ^ b o := by
    intro F b hF
    have e1 : ((eval₂ fC aC F : Cr) : L) = eval₂ (ev.comp C) aL F := by
      have h := eval₂_comp_left Cr.subtype fC aC F
      rw [Subring.coe_subtype] at h
      rw [h]
      congr 1
      · ext r
        simp [hfCv]
      · funext v
        simp [haC]
    rw [e1, eval₂_mul_fst_of_homog (ev.comp C) x Dinv hF, hσ]
  have hcomp : ∀ (F : MRing (extIdx ι J) R) (b : Option K → ℕ) (e : Option K →₀ ℕ), IsMultiHomog F b →
      eval₂ fC aC F ∈ 𝔮 → eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) ∈ 𝔮 := by
    intro F b e hF h
    rw [weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hF)]
    split_ifs
    · exact h
    · rw [eval₂_zero]
      exact 𝔮.zero_mem

  have hQp : Q.IsPrime := hQdef ▸ RingHom.ker_isPrime _
  have hQh : IsMultiHomogIdeal Q := by
    intro F hF b
    rw [memQ] at hF ⊢
    intro e
    refine hcomp _ b e (weightedHomogeneousComponent_isWeightedHomogeneous _ _) ?_
    have := hF (Finsupp.equivFunOnFinite.symm b)
    rwa [Finsupp.coe_equivFunOnFinite_symm] at this
  have hQr : IsRelevant Q := by
    have hXnot : ∀ (o : Option K) (l : extIdx ι J o), aL ⟨o, l⟩ = 1 → (X ⟨o, l⟩ : MRing (extIdx ι J) R) ∉ Q := by
      intro o l h1 hmem
      rw [hQdef, RingHom.mem_ker, RingHom.comp_apply] at hmem
      simp only [hψ, coe_eval₂Hom, eval₂_X, map_mul, map_C, map_X] at hmem
      have h2 := congrArg (coeff (Finsupp.single o 1)) hmem
      simp only [coeff_C_mul, coeff_X, coeff_X', if_true, mul_one, coeff_zero] at h2
      rw [Ideal.Quotient.eq_zero_iff_mem] at h2
      have h1' : aC ⟨o, l⟩ = 1 := Subtype.ext (by rw [haC]; exact h1)
      rw [h1'] at h2
      exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h2)
    intro o
    cases o with
    | none =>
      refine ⟨j, hXnot none j ?_⟩
      simp only [aL, x, Dinv, blowUpAtOne, Option.elim]
      exact mul_inv_cancel₀ hune
    | some k =>
      refine ⟨i k, hXnot (some k) (i k) ?_⟩
      simp only [aL, x, Dinv, blowUpAtOne, Option.elim]
      exact mul_inv_cancel₀ (hXne k)
  have hQb : blowUpOf P u ≤ Q := by
    intro F hF
    rw [memQ]
    intro e
    have hFe := isMultiHomogIdeal_blowUpOf hPh N u hu F hF ⇑e
    have h0 : eval₂ fC aC (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) = 0 := by
      apply Subtype.ext
      rw [hval _ _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
      have hz : blowUpEval P u (weightedHomogeneousComponent (blockWeight (extIdx ι J)) ⇑e F) = 0 := by
        rw [blowUpOf, RingHom.mem_ker] at hFe
        show Polynomial.eval 1 (aeval (blowUpSubst P u) _) = 0
        rw [hFe, Polynomial.eval_zero]
      rw [hz, map_zero, zero_mul, ZeroMemClass.coe_zero]
    rw [h0]
    exact h0mem
  have hQW : Q.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ W := by
    intro g hg
    rw [Ideal.mem_comap] at hg
    by_contra hgW
    obtain ⟨c, hc⟩ : ∃ c, weightedHomogeneousComponent (blockWeight ι) c g ∉ W := by
      by_contra hall
      push_neg at hall
      apply hgW
      rw [← sum_weightedHomogeneousComponent (blockWeight ι) g,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp g)]
      exact Ideal.sum_mem _ fun c _ => hall c
    have hmem := (memQ _).mp hg (Finsupp.equivFunOnFinite.symm (liftMDeg c))
    rw [Finsupp.coe_equivFunOnFinite_symm, component_liftForm] at hmem
    set gc := weightedHomogeneousComponent (blockWeight ι) c g with hgc_def
    have hgc : IsMultiHomog gc c := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hmW : (powMonomial c i : MRing ι R) ∉ W := fun h =>
      (W.primeCompl.prod_mem fun k _ => W.primeCompl.pow_mem (hi k) _) h
    have hinv := hgen c _ _ (isMultiHomog_powMonomial c i) hgc hc
    have hv := hval _ _ (isMultiHomog_liftForm (J := J) hgc)
    rw [blowUpEval_liftForm, Fintype.prod_option] at hv
    have hpm : ev (powMonomial c i) = ∏ k, ev (X ⟨k, i k⟩) ^ c k := by
      simp [powMonomial, map_prod, map_pow]
    have hunit : eval₂ fC aC (liftForm gc) * ⟨_, hinv⟩ = 1 := by
      apply Subtype.ext
      rw [Subring.coe_mul, hv]
      simp only [Dinv, liftMDeg, Option.elim, pow_zero, one_mul, inv_pow, Finset.prod_inv_distrib,
        OneMemClass.coe_one]
      rw [hpm, ← hev]
      have h1 : ev gc ≠ 0 := hne _ hc
      have h2 : ∏ k, ev (X ⟨k, i k⟩) ^ c k ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hXne k)
      calc _ = (ev gc * (ev gc)⁻¹) * ((∏ k, ev (X ⟨k, i k⟩) ^ c k) * (∏ k, ev (X ⟨k, i k⟩) ^ c k)⁻¹) := by
            ring
        _ = 1 := by rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2, one_mul]
    exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr (hunit ▸ 𝔮.mul_mem_right _ hmem))

  have hfQ : f ∈ blowUpLocRing P u Q := by
    have h := hf
    simp only [blowUpOverLoc, Subring.mem_iInf] at h
    exact h Q ⟨hQp, hQh, hQr, hQb, hQW⟩

  have key : ∀ z ∈ blowUpLocRing P u Q, ∃ d : Cr, d ∉ 𝔮 ∧ (d : L) * z ∈ Cr := by
    intro z hz
    refine Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨b, F, G, hF, hG, hGQ, rfl⟩
      have hd : eval₂ fC aC G ∉ 𝔮 := fun h => hGQ ((memQ G).mpr fun e => hcomp G b e hG h)
      refine ⟨eval₂ fC aC G, hd, ?_⟩
      have hG0 : algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G) ≠ 0 := by
        intro h0
        apply hd
        have : eval₂ fC aC G = 0 := Subtype.ext (by rw [hval G b hG, h0, zero_mul, ZeroMemClass.coe_zero])
        rw [this]
        exact 𝔮.zero_mem
      have e2 : ((eval₂ fC aC G : Cr) : L) *
          (algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) / algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G)) =
          ((eval₂ fC aC F : Cr) : L) := by
        rw [hval G b hG, hval F b hF]
        generalize algebraMap (MRing ι R ⧸ P) L (blowUpEval P u G) = g at hG0 ⊢
        calc _ = algebraMap (MRing ι R ⧸ P) L (blowUpEval P u F) * (∏ o, Dinv o ^ b o) * (g * g⁻¹) := by
              ring
          _ = _ := by rw [mul_inv_cancel₀ hG0, mul_one]
      rw [e2]
      exact (eval₂ fC aC F).2
    · exact ⟨1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simpa using Cr.zero_mem⟩
    · exact ⟨1, fun h => h𝔮.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simpa using Cr.one_mem⟩
    · rintro a b - - ⟨d₁, h₁, e₁⟩ ⟨d₂, h₂, e₂⟩
      refine ⟨d₁ * d₂, fun h => (h𝔮p.mem_or_mem h).elim h₁ h₂, ?_⟩
      have : ((d₁ * d₂ : Cr) : L) * (a + b) = (d₂ : L) * ((d₁ : L) * a) + (d₁ : L) * ((d₂ : L) * b) := by
        push_cast
        ring
      rw [this]
      exact Cr.add_mem (Cr.mul_mem d₂.2 e₁) (Cr.mul_mem d₁.2 e₂)
    · rintro a - ⟨d, h, e⟩
      exact ⟨d, h, by rw [mul_neg]; exact Cr.neg_mem e⟩
    · rintro a b - - ⟨d₁, h₁, e₁⟩ ⟨d₂, h₂, e₂⟩
      refine ⟨d₁ * d₂, fun h => (h𝔮p.mem_or_mem h).elim h₁ h₂, ?_⟩
      have : ((d₁ * d₂ : Cr) : L) * (a * b) = ((d₁ : L) * a) * ((d₂ : L) * b) := by
        push_cast
        ring
      rw [this]
      exact Cr.mul_mem e₁ e₂
  obtain ⟨d, hd, hdf⟩ := key f hfQ
  exact hd (h𝔇𝔮 hdf)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

namespace BlowUpOverLocFibreFinite

theorem isAlgebraic_div {A L : Type*} [CommRing A] [Field L] [Algebra A L] (a b : A)
    (hb : algebraMap A L b ≠ 0) : IsAlgebraic A (algebraMap A L a / algebraMap A L b) := by
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => Polynomial.coeff p 1) h
    simp at h1
    rw [h1, map_zero]
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rw [mul_div_cancel₀ _ hb, sub_self]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {J : Type} {R : Type u} [CommRing R]

def blowUpFrac (P : Ideal (MRing ι R)) (u : J → MRing ι R) :
    MRing (extIdx ι J) R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (blowUpEval P u)

theorem blowUpFrac_apply (P : Ideal (MRing ι R)) (u : J → MRing ι R) (F : MRing (extIdx ι J) R) :
    blowUpFrac P u F = algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) := rfl

theorem blowUpFrac_X_none (P : Ideal (MRing ι R)) (u : J → MRing ι R) (j : J) :
    blowUpFrac P u (X ⟨none, j⟩) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u j)) := by
  rw [blowUpFrac_apply]
  congr 1
  show Polynomial.eval 1 (aeval (blowUpSubst P u) (newVar j : MRing (extIdx ι J) R)) = _
  rw [aeval_blowUpSubst_newVar]
  simp

theorem blowUpFrac_X_some (P : Ideal (MRing ι R)) (u : J → MRing ι R) (k : K) (i : ι k) :
    blowUpFrac P u (X ⟨some k, i⟩) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, i⟩)) := by
  rw [blowUpFrac_apply, ← blowUpEval_liftForm (J := J) P u, liftForm_X]

theorem blowUpFrac_C (P : Ideal (MRing ι R)) (u : J → MRing ι R) (r : R) :
    blowUpFrac P u (C r) =
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (C r)) := by
  rw [blowUpFrac_apply, ← blowUpEval_liftForm (J := J) P u, liftForm_C]

theorem blowUpLocRing_isLocal (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R)
    (Q : Ideal (MRing (extIdx ι J) R)) (hQ : Q.IsPrime) (hle : blowUpOf P u ≤ Q) :
    IsLocalRing (blowUpLocRing P u Q) ∧
      ∀ (z : blowUpLocRing P u Q) (b : Option K → ℕ) (F G : MRing (extIdx ι J) R), IsMultiHomog F b →
        IsMultiHomog G b → G ∉ Q →
        (z : FractionRing (MRing ι R ⧸ P)) =
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u F) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (blowUpEval P u G) →
        (IsUnit z ↔ F ∉ Q) := by
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := BlowUpLocRingIso.proof R K ι J P u Q hle
  obtain ⟨-, hunit⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof R (Option K) (extIdx ι J)
    (blowUpOf P u) Q hQ hle
  have := (HomLocRingIsLocal.proof HomLocRingMem.proof R (Option K) (extIdx ι J)
    (blowUpOf P u) Q hQ hle).1
  refine ⟨φ.isLocalRing, fun z b F G hF hG hGQ hz => ?_⟩
  have e : z = φ ⟨_, Subring.subset_closure ⟨b, F, G, hF, hG, hGQ, rfl⟩⟩ :=
    (Subtype.ext ((hφ b F G hF hG hGQ).trans hz.symm)).symm
  rw [e]
  exact (MulEquiv.isUnit_map φ.toMulEquiv).trans (hunit b F G hF hG hGQ _)

theorem isMultiHomog_prod_X_pow (e : ∀ o, extIdx ι J o) (b : Option K → ℕ) :
    IsMultiHomog (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) b := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun o => (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o)
    (fun o => b o • blockWeight (extIdx ι J) ⟨o, e o⟩)
    (fun o _ => (isWeightedHomogeneous_X R (blockWeight (extIdx ι J)) ⟨o, e o⟩).pow (b o))
  have hb : (∑ o, b o • blockWeight (extIdx ι J) ⟨o, e o⟩) = b := by
    funext o'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hb] at h
  exact h

theorem prod_X_pow_not_mem {Q : Ideal (MRing (extIdx ι J) R)} (hQ : Q.IsPrime)
    {e : ∀ o, extIdx ι J o} (he : ∀ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ∉ Q) (b : Option K → ℕ) :
    (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) ∉ Q := by
  haveI := hQ
  exact fun h => (Q.primeCompl.prod_mem fun o _ => Q.primeCompl.pow_mem (he o) _) h

def chartCoord (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (e : ∀ o, extIdx ι J o) :
    (Σ o, extIdx ι J o) → FractionRing (MRing ι R ⧸ P) :=
  fun v => blowUpFrac P u (X v) * (blowUpFrac P u (X ⟨v.1, e v.1⟩))⁻¹

def chartVal (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (e : ∀ o, extIdx ι J o) (F : MRing (extIdx ι J) R) :
    FractionRing (MRing ι R ⧸ P) :=
  eval₂ ((blowUpFrac P u).comp C) (chartCoord P u e) F

theorem chartVal_of_homog (P : Ideal (MRing ι R)) [P.IsPrime] (u : J → MRing ι R) (e : ∀ o, extIdx ι J o)
    {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b) :
    chartVal P u e F = blowUpFrac P u F / blowUpFrac P u (∏ o, X ⟨o, e o⟩ ^ b o) := by
  have hφ : blowUpFrac P u = eval₂Hom ((blowUpFrac P u).comp C) (fun v => blowUpFrac P u (X v)) :=
    ringHom_ext (fun r => by simp) (fun v => by simp)
  refine (BlowUpOverLocInChart.eval₂_mul_fst_of_homog ((blowUpFrac P u).comp C) (fun v => blowUpFrac P u (X v))
    (fun o => (blowUpFrac P u (X ⟨o, e o⟩))⁻¹) hF).trans ?_
  have h1 : eval₂ ((blowUpFrac P u).comp C) (fun v => blowUpFrac P u (X v)) F = blowUpFrac P u F := by
    conv_rhs => rw [hφ]
    rfl
  rw [h1, map_prod, div_eq_mul_inv, ← Finset.prod_inv_distrib]
  simp only [map_pow, inv_pow]

variable [∀ k, Fintype (ι k)] [Fintype J]

set_option maxHeartbeats 1000000 in

theorem eq_of_le_of_mem_fibre (P W : Ideal (MRing ι R)) [P.IsPrime]
    (hN : IsNoetherianRing (homLocRing P W)) (hD : ringKrullDim (homLocRing P W) = 1)
    (hWp : W.IsPrime) (hPW : P ≤ W) (hWrel : IsRelevant W) (N : K → ℕ) (u : J → MRing ι R)
    (hu : ∀ j, IsMultiHomog (u j) N) (c : K → ℕ) (x : MRing ι R) (hx : IsMultiHomog x c) (hxP : x ∉ P)
    (hxW : x ∈ W) {Q₀ Q : Ideal (MRing (extIdx ι J) R)}
    (hQ₀ : Q₀.IsPrime ∧ IsMultiHomogIdeal Q₀ ∧ IsRelevant Q₀ ∧ blowUpOf P u ≤ Q₀ ∧
      Q₀.comap (liftForm (ι := ι) (J := J) (R := R)) = W)
    (hQ : Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧ blowUpOf P u ≤ Q ∧
      Q.comap (liftForm (ι := ι) (J := J) (R := R)) = W)
    (hle : Q₀ ≤ Q) : Q₀ = Q := by
  obtain ⟨hQ₀p, hQ₀h, hQ₀r, hQ₀le, hQ₀W⟩ := hQ₀
  obtain ⟨hQp, hQh, hQr, hQle, hQW⟩ := hQ
  haveI := hN
  by_contra hne
  choose e he using hQr
  have hL : ∀ f : MRing ι R, f ∉ P →
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P f) ≠ 0 :=
    fun f hf => HomLocRingMem.algebraMap_mk_ne_zero P hf

  have hφne : ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ}, IsMultiHomog F b → F ∉ blowUpOf P u →
      blowUpFrac P u F ≠ 0 := by
    intro F b hF hFn h0
    apply hFn
    rw [blowUpFrac_apply, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h0
    rw [blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_of_isMultiHomog P u hF, h0, map_zero, zero_mul]
  have hG : ∀ b : Option K → ℕ, IsMultiHomog (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) b :=
    fun b => isMultiHomog_prod_X_pow e b
  have hGQ : ∀ b : Option K → ℕ, (∏ o, (X ⟨o, e o⟩ : MRing (extIdx ι J) R) ^ b o) ∉ Q := prod_X_pow_not_mem hQp he
  have hφe : ∀ o, blowUpFrac P u (X ⟨o, e o⟩) ≠ 0 := fun o =>
    hφne (isWeightedHomogeneous_X R (blockWeight (extIdx ι J)) ⟨o, e o⟩) fun h => he o (hQle h)

  let B : Subalgebra (homLocRing P W) (FractionRing (MRing ι R ⧸ P)) :=
    Algebra.adjoin (homLocRing P W) (Set.range (chartCoord P u e))
  have hCA : ∀ r : R, blowUpFrac P u (C r) ∈ homLocRing P W := by
    intro r
    refine Subring.subset_closure ⟨0, C r, 1, isWeightedHomogeneous_C _ r, isWeightedHomogeneous_one R _,
      fun h => hWp.ne_top ((Ideal.eq_top_iff_one W).mpr h), ?_⟩
    rw [map_one, map_one, div_one, blowUpFrac_C]
  have hτB : ∀ F, chartVal P u e F ∈ B := by
    intro F
    refine MvPolynomial.induction_on (motive := fun F => chartVal P u e F ∈ B) F (fun r => ?_) (fun p q hp hq => ?_) (fun p v hp => ?_)
    · show eval₂ _ _ (C r) ∈ B
      rw [eval₂_C]
      exact Subalgebra.algebraMap_mem B (⟨_, hCA r⟩ : homLocRing P W)
    · show eval₂ _ _ (p + q) ∈ B
      rw [eval₂_add]
      exact add_mem hp hq
    · show eval₂ _ _ (p * X v) ∈ B
      rw [eval₂_mul, eval₂_X]
      exact mul_mem hp (Algebra.subset_adjoin ⟨v, rfl⟩)

  have hτD : ∀ {Q' : Ideal (MRing (extIdx ι J) R)}, Q' ≤ Q → ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ},
      IsMultiHomog F b → chartVal P u e F ∈ blowUpLocRing P u Q' := fun hQ' F b hF =>
    Subring.subset_closure ⟨b, F, _, hF, hG b, fun h => hGQ b (hQ' h), chartVal_of_homog P u e hF⟩
  have hBD : ∀ {Q' : Ideal (MRing (extIdx ι J) R)}, Q'.IsPrime → IsMultiHomogIdeal Q' → IsRelevant Q' →
      blowUpOf P u ≤ Q' → Q'.comap (liftForm (ι := ι) (J := J) (R := R)) ≤ W → Q' ≤ Q →
      ∀ z ∈ B, z ∈ blowUpLocRing P u Q' := by
    intro Q' h1 h2 h3 h4 h5 h6 z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      have h := hτD h6 (isWeightedHomogeneous_X R (blockWeight (extIdx ι J)) v)
      rwa [chartVal, eval₂_X] at h
    | algebraMap r =>
      have h := homLocRing_le_blowUpOverLoc P W u r.2
      simp only [blowUpOverLoc, Subring.mem_iInf] at h
      exact h Q' ⟨h1, h2, h3, h4, h5⟩
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hBQ := hBD hQp hQh (fun o => ⟨e o, he o⟩) hQle hQW.le le_rfl
  have hBQ₀ := hBD hQ₀p hQ₀h hQ₀r hQ₀le hQ₀W.le hle

  obtain ⟨hloc, hunit⟩ := blowUpLocRing_isLocal P u Q hQp hQle
  obtain ⟨hloc₀, hunit₀⟩ := blowUpLocRing_isLocal P u Q₀ hQ₀p hQ₀le
  let f : B →+* blowUpLocRing P u Q :=
    ((B.val : B →ₐ[homLocRing P W] FractionRing (MRing ι R ⧸ P)) : B →+* _).codRestrict _ fun z => hBQ z z.2
  let f₀ : B →+* blowUpLocRing P u Q₀ :=
    ((B.val : B →ₐ[homLocRing P W] FractionRing (MRing ι R ⧸ P)) : B →+* _).codRestrict _ fun z => hBQ₀ z z.2
  let 𝔮 : Ideal B := (IsLocalRing.maximalIdeal _).comap f
  let 𝔮₀ : Ideal B := (IsLocalRing.maximalIdeal _).comap f₀
  have hmem : ∀ z, z ∈ 𝔮 ↔ ¬ IsUnit (f z) := fun z => by
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hmem₀ : ∀ z, z ∈ 𝔮₀ ↔ ¬ IsUnit (f₀ z) := fun z => by
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hform : ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b),
      ((⟨_, hτB F⟩ : B) ∈ 𝔮 ↔ F ∈ Q) := fun {F} {b} hF => by
    rw [hmem, hunit _ b F _ hF (hG b) (hGQ b) (chartVal_of_homog P u e hF), not_not]
  have hform₀ : ∀ {F : MRing (extIdx ι J) R} {b : Option K → ℕ} (hF : IsMultiHomog F b),
      ((⟨_, hτB F⟩ : B) ∈ 𝔮₀ ↔ F ∈ Q₀) := fun {F} {b} hF => by
    rw [hmem₀, hunit₀ _ b F _ hF (hG b) (fun h => hGQ b (hle h)) (chartVal_of_homog P u e hF), not_not]
  have hDD : blowUpLocRing P u Q ≤ blowUpLocRing P u Q₀ :=
    Subring.closure_mono fun z ⟨b, F, G', hF, hG', hG'Q, hz⟩ => ⟨b, F, G', hF, hG', fun h => hG'Q (hle h), hz⟩
  have hmono : 𝔮₀ ≤ 𝔮 := by
    intro z hz
    rw [hmem₀] at hz
    rw [hmem]
    intro hu
    exact hz (hu.map (Subring.inclusion hDD))

  have hx₀ : (⟨_, hτB (liftForm x)⟩ : B) ∈ 𝔮₀ := (hform₀ (isMultiHomog_liftForm hx)).mpr (by
    rw [← Ideal.mem_comap, hQ₀W]
    exact hxW)
  have h0 : (⊥ : Ideal B) < 𝔮₀ := by
    refine bot_lt_iff_ne_bot.mpr fun hb => ?_
    rw [hb, Ideal.mem_bot] at hx₀
    have h := congrArg Subtype.val hx₀
    rw [show ((⟨_, hτB (liftForm x)⟩ : B) : FractionRing (MRing ι R ⧸ P)) = chartVal P u e (liftForm x) from rfl,
      chartVal_of_homog P u e (isMultiHomog_liftForm hx), blowUpFrac_apply, blowUpEval_liftForm] at h
    exact div_ne_zero (hL x hxP) (hφne (hG _) fun h' => hGQ _ (hQle h')) h

  obtain ⟨F, hFQ, hFQ₀⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hle hne)
  obtain ⟨b, hbQ₀⟩ : ∃ b, weightedHomogeneousComponent (blockWeight (extIdx ι J)) b F ∉ Q₀ := by
    by_contra h
    push_neg at h
    apply hFQ₀
    rw [← sum_weightedHomogeneousComponent (blockWeight (extIdx ι J)) F]
    exact finsum_induction (· ∈ Q₀) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) h
  have hFb := weightedHomogeneousComponent_isWeightedHomogeneous (R := R) (w := blockWeight (extIdx ι J)) b F
  have h01 : 𝔮₀ < 𝔮 := by
    refine lt_of_le_of_ne hmono fun h => hbQ₀ ((hform₀ hFb).mp ?_)
    rw [h]
    exact (hform hFb).mpr (hQh F hFQ b)

  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  have e2 := Ideal.height_add_one_le_of_lt_of_isPrime h01
  rw [Ideal.height_bot] at e1
  have h2 : (2 : ℕ∞) ≤ 𝔮.height :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ 𝔮₀.height + 1 := add_le_add e1 le_rfl
      _ ≤ 𝔮.height := e2
  haveI : Algebra.FiniteType (homLocRing P W) B :=
    Algebra.FiniteType.adjoin_of_finite (R := homLocRing P W) (t := Set.range (chartCoord P u e)) (Set.finite_range _)
  haveI hAlg : Algebra.IsAlgebraic (homLocRing P W) B := by
    refine (Subalgebra.isAlgebraic_iff B).mp (Algebra.isAlgebraic_adjoin_iff.mpr ?_)
    rintro _ ⟨⟨o, i⟩, rfl⟩
    cases o with
    | none =>
      obtain ⟨i₀, hi₀⟩ := powMonomial_not_mem hWp hWrel N
      have hmP : powMonomial N i₀ ∉ P := fun h => hi₀ (hPW h)
      have ha : ∀ k : J, algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u k)) /
          algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i₀)) ∈
            homLocRing P W := fun k =>
        Subring.subset_closure ⟨N, u k, powMonomial N i₀, hu k, isMultiHomog_powMonomial N i₀, hi₀, rfl⟩
      have hj : algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u (e none))) ≠ 0 :=
        fun h => hφe none (by rw [← h]; exact blowUpFrac_X_none P u (e none))
      have key : chartCoord P u e ⟨none, i⟩ =
          (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u i)) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i₀))) /
          (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (u (e none))) /
            algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) (Ideal.Quotient.mk P (powMonomial N i₀))) := by
        show blowUpFrac P u (X ⟨none, i⟩) * (blowUpFrac P u (X ⟨none, e none⟩))⁻¹ = _ / _
        rw [show blowUpFrac P u (X ⟨none, i⟩) = _ from blowUpFrac_X_none P u i,
          show blowUpFrac P u (X ⟨none, e none⟩) = _ from blowUpFrac_X_none P u (e none),
          div_div_div_cancel_right₀ (hL _ hmP), div_eq_mul_inv]
      rw [key]
      exact isAlgebraic_div (⟨_, ha i⟩ : homLocRing P W) ⟨_, ha (e none)⟩ (div_ne_zero hj (hL _ hmP))
    | some k =>
      have hnot : (X ⟨k, e (some k)⟩ : MRing ι R) ∉ W := fun h => he (some k) (by
        rw [← hQW, Ideal.mem_comap, liftForm_X] at h
        exact h)
      have hmemA : chartCoord P u e ⟨some k, i⟩ ∈ homLocRing P W := by
        refine Subring.subset_closure ⟨Pi.single k 1, X ⟨k, i⟩, X ⟨k, e (some k)⟩,
          isWeightedHomogeneous_X R (blockWeight ι) ⟨k, i⟩,
          isWeightedHomogeneous_X R (blockWeight ι) ⟨k, e (some k)⟩, hnot, ?_⟩
        show blowUpFrac P u (X ⟨some k, i⟩) * (blowUpFrac P u (X ⟨some k, e (some k)⟩))⁻¹ = _
        rw [show blowUpFrac P u (X ⟨some k, i⟩) = _ from blowUpFrac_X_some P u k i,
          show blowUpFrac P u (X ⟨some k, e (some k)⟩) = _ from blowUpFrac_X_some P u k (e (some k)),
          div_eq_mul_inv]
      exact isAlgebraic_algebraMap (⟨_, hmemA⟩ : homLocRing P W)
  have hinj : Function.Injective (algebraMap (homLocRing P W) B) := fun a a' h => by
    have h' := congrArg (fun z : B => (z : FractionRing (MRing ι R ⧸ P))) h
    exact Subtype.ext h'
  have hdi := DimensionInequality.full (homLocRing P W) B hinj 𝔮
  rw [trdeg_eq_zero (R := homLocRing P W) (A := B), add_zero] at hdi
  have h3 : 𝔮.height ≤ (𝔮.under (homLocRing P W)).height :=
    Cardinal.ofENat_le_ofENat.mp (le_trans le_self_add hdi)
  have h4 : (𝔮.under (homLocRing P W)).height ≤ 1 := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔮.under (homLocRing P W))
    rw [hD] at h
    exact_mod_cast h
  have h5 := h2.trans (h3.trans h4)
  norm_num at h5

end BlowUpOverLocFibreFinite

open BlowUpOverLocFibreFinite in

theorem BlowUpOverLocFibreFinite.proof : BlowUpOverLocFibreFinite.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have hPp : P.IsPrime := hP.multiProj.isPrime
  obtain ⟨-, hNoeth, hDim⟩ := HomLocRingLocal.proof (HomLocRingIsLocal.proof HomLocRingMem.proof)
    (HomLocRingNoetherian.proof HomLocRingMem.proof)
    (HomLocRingDimLe.proof HomLocRingMem.proof (HomLocRingIsLocal.proof HomLocRingMem.proof))
    O K ι P hP.multiProj c x hx hxP W hWmin hWrel
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hxW : x ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hI : IsMultiHomogIdeal (blowUpOf P u ⊔ Ideal.span {liftForm (J := J) x}) :=
    SupSpanMultiHomog.proof O (Option K) (extIdx ι J) (blowUpOf P u) (liftForm x) (liftMDeg c)
      (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
    (blowUpOf P u ⊔ Ideal.span {liftForm (J := J) x})).subset ?_
  rintro Q ⟨hQp, hQh, hQr, hQle, hQW⟩
  have hxQ : liftForm x ∈ Q := by
    rw [← Ideal.mem_comap, hQW]
    exact hxW
  refine ⟨⟨hQp, sup_le hQle ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)⟩, fun Q' hQ' hQ'Q => ?_⟩
  haveI := hQ'.1
  obtain ⟨Q₀, hQ₀, hQ₀Q'⟩ := Ideal.exists_minimalPrimes_le hQ'.2
  have hQ₀p : Q₀.IsPrime := hQ₀.1.1
  have hQ₀Q : Q₀ ≤ Q := hQ₀Q'.trans hQ'Q
  have hQ₀h := MinimalPrimeMultiHomog.proof O (Option K) (extIdx ι J) _ Q₀ hI hQ₀
  have hQ₀r : IsRelevant Q₀ := fun o =>
    let ⟨i, hi⟩ := hQr o
    ⟨i, fun h => hi (hQ₀Q h)⟩
  have hQ₀le : blowUpOf P u ≤ Q₀ := le_sup_left.trans hQ₀.1.2
  have hQ₀W : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) = W := by
    have hle : Q₀.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W := hQW ▸ Ideal.comap_mono hQ₀Q
    refine le_antisymm hle (hWmin.2 ⟨Ideal.comap_isPrime _ _,
      sup_le (fun p hp => hQ₀le (liftForm_mem_blowUpOf hp)) ?_⟩ hle)
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact hQ₀.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have h := eq_of_le_of_mem_fibre P W hNoeth hDim hWp hPW hWrel N u hu c x hx hxP hxW
    ⟨hQ₀p, hQ₀h, hQ₀r, hQ₀le, hQ₀W⟩ ⟨hQp, hQh, hQr, hQle, hQW⟩ hQ₀Q
  exact h ▸ hQ₀Q'

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end
