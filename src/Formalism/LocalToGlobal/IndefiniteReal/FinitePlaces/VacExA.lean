import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 400000

namespace Formalism.IndefR.Fin.VacEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsDyIdem (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) : Prop :=
  IsSplitIdem D e ∧ finPart D e ∈ intAE D ∧
    ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def DyadIdem (D : D7) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), (2 : 𝓞 D.host.F) ∈ v.asIdeal → ∃ e : AE D, IsDyIdem v e

open Classical in

def eDy (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D :=
  if (2 : 𝓞 D.host.F) ∈ v.asIdeal then Classical.epsilon (IsDyIdem (D := D) v) else 0

theorem eDy_spec (hdy : DyadIdem D) (v : HeightOneSpectrum (𝓞 D.host.F)) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) :
    IsDyIdem v (eDy (D := D) v) := by
  unfold eDy
  rw [if_pos h2]
  exact Classical.epsilon_spec (hdy v h2)

theorem eDy_of_not (v : HeightOneSpectrum (𝓞 D.host.F)) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) : eDy (D := D) v = 0 := by
  unfold eDy; rw [if_neg h2]

theorem dyad_finite (D : D7) : {v : HeightOneSpectrum (𝓞 D.host.F) | (2 : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

def e2 (D : D7) : AE D := ∑ v ∈ (dyad_finite D).toFinset, eDy v

theorem fstA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : fstA D.host.F (pairA D.host.F x y) = x := rfl
theorem sndA_pairA (x : Ainf D.host.F) (y : Af D.host.F) : sndA D.host.F (pairA D.host.F x y) = y := rfl

open Classical in
theorem placeIdem_mul {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v' ε') : ε * ε' = if v = v' then ε else 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, h1', h0'⟩ := h'
  split_ifs with hvv
  · subst hvv
    refine Fock.DRho.AF_ext D ?_ ?_
    · rw [map_mul, fstA_pairA, zero_mul]
    · rw [map_mul, sndA_pairA, sndA_pairA]
      refine Formalism.IndefR.Fin.af_ext fun w => ?_
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1', mul_one]
      · rw [h0 w hw, zero_mul]
  · refine Fock.DRho.AF_ext D ?_ ?_
    · rw [map_mul, fstA_pairA, zero_mul, map_zero]
    · rw [map_mul, sndA_pairA, sndA_pairA, map_zero]
      refine Formalism.IndefR.Fin.af_ext fun w => ?_
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [h0' w hvv, mul_zero]
      · rw [h0 w hw, zero_mul]

theorem infPart_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
  obtain ⟨α, rfl, -, -⟩ := h
  show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
  rw [Fock.DRho.infPart_tmul, fstA_pairA, TensorProduct.zero_tmul]

theorem idem_mul_eps {e : AE D} {ε : AF D.host.F} (he : e * e = e) (hc : e * cA D e = 0)
    (hs : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : e * algebraMap (AF D.host.F) (AE D) ε = e := by
  rw [← hs, mul_add, he, hc, add_zero]

theorem infPart_idem {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (he : e * e = e)
    (hc : e * cA D e = 0) (hε : IsPlaceIdem D v ε) (hs : e + cA D e = algebraMap (AF D.host.F) (AE D) ε) :
    infPart D e = 0 := by
  rw [← idem_mul_eps he hc hs, map_mul, infPart_placeIdem hε, mul_zero]

open Classical in
theorem eDy_mul_eps (hdy : DyadIdem D) (v' : HeightOneSpectrum (𝓞 D.host.F)) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    eDy (D := D) v' * algebraMap (AF D.host.F) (AE D) ε = if v' = v then eDy v' else 0 := by
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v'.asIdeal
  · obtain ⟨⟨he, hc, -⟩, -, ε', hε', hs⟩ := eDy_spec hdy v' h2
    conv_lhs => rw [← idem_mul_eps he hc hs]
    rw [mul_assoc, ← map_mul, placeIdem_mul hε' hε]
    split_ifs
    · exact idem_mul_eps he hc hs
    · rw [map_zero, mul_zero]
  · rw [eDy_of_not v' h2, zero_mul]; split_ifs <;> rfl

theorem dyadic_idempotent_mul_place_idempotent (hdy : DyadIdem D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) : e2 D * algebraMap (AF D.host.F) (AE D) ε = eDy v := by
  unfold e2
  rw [Finset.sum_mul]
  by_cases h : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · rw [Finset.sum_eq_single v]
    · rw [eDy_mul_eps hdy v hε, if_pos rfl]
    · intro b _ hb; rw [eDy_mul_eps hdy b hε, if_neg hb]
    · intro hv; exact absurd ((Set.Finite.mem_toFinset (dyad_finite D)).2 h) hv
  · rw [eDy_of_not v h]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [eDy_mul_eps hdy b hε, if_neg]
    rintro rfl
    exact h ((Set.Finite.mem_toFinset (dyad_finite D)).1 hb)




theorem finPart_algebraMap (r : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) r) = sndA D.host.F r ⊗ₜ[D.host.F] (1 : D.host.E) := rfl

theorem half_mem_int {v : HeightOneSpectrum (𝓞 D.host.F)} (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) :
    finPart D (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2) * ε)) ∈ intAE D := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  refine AddSubgroup.subset_closure ⟨sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2) * pairA D.host.F 0 α), ?_,
    1, ?_⟩
  · intro w
    rw [map_mul, sndA_pairA, map_mul]
    have e : evalV D.host.F w (sndA D.host.F (algebraMap D.host.F (AF D.host.F) (1 / 2))) =
        algebraMap D.host.F (w.adicCompletion D.host.F) (1 / 2) := by
      rw [AlgHom.commutes, AlgHom.commutes]
    rw [e]
    by_cases hw : w = v
    · subst hw
      rw [h1, mul_one]
      have hv2 : Valued.v (((2 : 𝓞 D.host.F) : D.host.F) : w.adicCompletion D.host.F) = 1 := by
        refine le_antisymm (Formalism.IndefR.Fin.val_coe_le_one w 2) ?_
        exact not_lt.1 fun h => h2 ((Formalism.IndefR.Fin.val_coe_lt_one_iff w 2).1 h)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have hprod : algebraMap D.host.F (w.adicCompletion D.host.F) (1 / 2) *
          (((2 : 𝓞 D.host.F) : D.host.F) : w.adicCompletion D.host.F) = 1 := by
        have hc2 : (((2 : 𝓞 D.host.F) : D.host.F)) = 2 := by norm_cast
        rw [← Formalism.IndefR.Fin.algebraMap_adic_eq (D := D) w, hc2, ← map_mul]; norm_num
      have hv := congrArg Valued.v hprod
      rw [map_mul, hv2, mul_one, map_one] at hv
      rw [hv]
    · rw [h0 w hw, mul_zero]
      exact zero_mem _
  · rw [finPart_algebraMap]; rfl

section Sym

variable (S T : HSp D)

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a w =>
    show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)
      ((Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (a ⊗ₜ[D.host.F] w)) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    show a ⊗ₜ[D.host.F] star (star w) = _
    rw [star_star]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hO_smul_left (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  ring


theorem symplO_alg_left (r : AF D.host.F) (x y : WO S T) :
    symplO S T (algebraMap (AF D.host.F) (AE D) r • x) y = r * symplO S T x y := by
  unfold symplO
  rw [hO_smul_left, mul_left_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem symplO_sub_left (x x' y : WO S T) : symplO S T (x - x') y = symplO S T x y - symplO S T x' y := by
  rw [sub_eq_add_neg, Formalism.IndefR.Fin.symplO_add_left, Formalism.IndefR.Fin.symplO_neg_left, ← sub_eq_add_neg]

def halfE (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (1 / 2))

theorem symplOH_eq (x y : WO S T) : symplOH S T x y = symplO S T (halfE D • x) y := by
  unfold symplOH halfE; rw [symplO_alg_left]

theorem two_halfE : (2 : AF D.host.F) * algebraMap D.host.F (AF D.host.F) (1 / 2) = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num

theorem symplOH_add_self (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y :=
  Formalism.IndefR.Fin.symplOH_two S T x y




end Sym

section Phi

variable (S T : HSp D)

def U0 (Λ : AddSubgroup (WO S T)) : AddSubgroup (WO S T) where
  carrier := {w | ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0}
  add_mem' := by
    rintro a b ⟨u, hu, ha⟩ ⟨u', hu', hb⟩
    refine ⟨u + u', Λ.add_mem hu hu', fun i j => ?_⟩
    have : (a + b - (u + u')) i j = (a - u) i j + (b - u') i j := by
      simp only [Matrix.sub_apply, Matrix.add_apply]; abel
    rw [this, map_add, ha, hb, add_zero]
  zero_mem' := ⟨0, Λ.zero_mem, fun i j => by simp⟩
  neg_mem' := by
    rintro a ⟨u, hu, ha⟩
    refine ⟨-u, Λ.neg_mem hu, fun i j => ?_⟩
    have : (-a - -u) i j = -((a - u) i j) := by simp only [Matrix.sub_apply, Matrix.neg_apply]; abel
    rw [this, map_neg, ha, neg_zero]

theorem mem_U0 {Λ : AddSubgroup (WO S T)} {w : WO S T} :
    w ∈ U0 S T Λ ↔ ∃ u ∈ Λ, ∀ i j, finPart D ((w - u) i j) = 0 := Iff.rfl

theorem le_open_neighbourhood {Λ : AddSubgroup (WO S T)} : Λ ≤ U0 S T Λ := fun u hu => ⟨u, hu, fun i j => by simp⟩

theorem open_neighbourhood_set_eq (Λ : AddSubgroup (WO S T)) :
    (U0 S T Λ : Set (WO S T)) = {w | ∃ u ∈ Λ, (w - u).map (finPart D) = 0} := by
  ext w
  simp only [SetLike.mem_coe, mem_U0, Set.mem_setOf_eq]
  refine exists_congr fun u => and_congr_right fun _ => ⟨fun h => ?_, fun h i j => ?_⟩
  · ext i j; exact h i j
  · have := congrFun (congrFun h i) j; simpa using this

open Classical in

def phiV (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (g : WO S T → ℂ) (y : WO S T) : ℂ :=
  if y ∈ U0 S T Λ then ψ (symplOH S T (e2 D • y) y) * g y else 0

def thS (ψ : AddChar (AF D.host.F) ℂ) (Φ : WO S T → ℂ) (w : WO S T) : ℂ :=
  ∑' γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ψ (symplOH S T (ratW T S γ) w) * Φ (ratW T S γ + w)

theorem symplOH_rat (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∃ q : D.host.F, symplOH S T (ratW T S a) (ratW T S b) = algebraMap D.host.F (AF D.host.F) q := by
  obtain ⟨q, hq⟩ := Formalism.IndefR.Fin.symplO_rat S T a b
  exact ⟨1 / 2 * q, by unfold symplOH; rw [hq, map_mul]⟩



end Phi

section Lat

variable (S T : HSp D)

structure LatHyp (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) : Prop where
  fi : ∀ x ∈ Λ, ∀ i j, infPart D (x i j) = 0
  int : ∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ
  pair : ∀ x ∈ Λ, ∀ u ∈ Λ, ψ (symplO S T x u) = 1

variable {S T}






theorem beta_int (hdy : DyadIdem D) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    finPart D (halfE D * (algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)))) ∈ intAE D := by
  have hce : cA D (algebraMap (AF D.host.F) (AE D) ε) = algebraMap (AF D.host.F) (AE D) ε := PHeisTh.cA_algebraMap ε
  have h1 : algebraMap (AF D.host.F) (AE D) ε * (1 + e2 D - cA D (e2 D)) =
      algebraMap (AF D.host.F) (AE D) ε + eDy v - cA D (eDy v) := by
    rw [← dyadic_idempotent_mul_place_idempotent hdy hε, map_mul, hce]; ring
  rw [h1]
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · obtain ⟨⟨hee, hec, -⟩, hint, ε', hε', hs⟩ := eDy_spec hdy v h2
    have hεε : ε' = ε := by
      have a := placeIdem_mul hε' hε
      have b := placeIdem_mul hε hε'
      rw [if_pos rfl] at a b
      rw [← a, mul_comm, b]
    subst hεε
    rw [← hs]
    have : halfE D * (eDy v + cA D (eDy v) + eDy v - cA D (eDy v)) = eDy (D := D) v := by
      have h2' : halfE D * 2 = 1 := by
        unfold halfE
        rw [← map_ofNat (algebraMap (AF D.host.F) (AE D)) 2, ← map_mul, mul_comm, two_halfE, map_one]
      calc halfE D * (eDy v + cA D (eDy v) + eDy v - cA D (eDy v)) = (halfE D * 2) * eDy v := by ring
        _ = eDy v := by rw [h2', one_mul]
    rw [this]; exact hint
  · rw [eDy_of_not v h2, add_zero, map_zero, sub_zero]
    unfold halfE
    rw [← map_mul]
    exact half_mem_int h2 hε



end Lat

end Formalism.IndefR.Fin.VacEx
