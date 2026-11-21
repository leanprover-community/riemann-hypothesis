import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U2ringPfDMain
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DescentValuation
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrystallineLatticeOfJumpPoints
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorLevelsUnramifiedStatement

section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

section U2E

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfE_mem_max (p : ℕ) [hp : Fact p.Prime] (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O)
    {x : O} (hroot : (1 + x) ^ p = 1) : x ∈ IsLocalRing.maximalIdeal O := by
  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  have h := congrArg (IsLocalRing.residue O) hroot
  rw [map_pow, map_add, map_one, add_pow_char, one_pow] at h
  have h2 : (IsLocalRing.residue O x) ^ p = 0 := by linear_combination h
  have h3 := (pow_eq_zero_iff hp.out.ne_zero).mp h2
  rwa [IsLocalRing.residue_eq_zero_iff] at h3

theorem u2ringPfE_val_unit {y c : O} (hy : y ∈ IsLocalRing.maximalIdeal O) {F : PowerSeries O}
    (hF : IsUnit (PowerSeries.constantCoeff F)) (hc : (mkI y) F = (mkI y) (PowerSeries.C c)) :
    IsUnit c := by
  obtain ⟨H, hH⟩ := DualFramesAlt.BlockProductRing.dvd_of_mk_eq hc
  have h0 := congrArg PowerSeries.constantCoeff hH
  simp only [map_sub, map_mul, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_C, zero_sub] at h0
  by_contra hnu
  have hcm : c ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
  have hFm : PowerSeries.constantCoeff F ∈ IsLocalRing.maximalIdeal O := by
    have e0 : PowerSeries.constantCoeff F = c + -y * PowerSeries.constantCoeff H := by linear_combination h0
    rw [e0]
    exact Ideal.add_mem _ hcm (Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 hy))
  exact (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hFm)) hF

theorem u2ringPfE_mk_aeval {x y : O} {P : PowerSeries O} (hP : (mkI x) P = (mkI x) (PowerSeries.C y))
    (E : Polynomial O) :
    (mkI x) (Polynomial.aeval P E) = (mkI x) (PowerSeries.C (E.eval y)) := by
  have h1 : (mkI x) (Polynomial.aeval P E) =
      Polynomial.aeval ((mkI x) P) E := by
    rw [← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
  rw [h1, hP, ← Ideal.Quotient.mkₐ_eq_mk O, Polynomial.aeval_algHom_apply]
  congr 1
  show Polynomial.aeval (PowerSeries.C y) E = PowerSeries.C (E.eval y)
  rw [show (PowerSeries.C y : PowerSeries O) = algebraMap O (PowerSeries O) y by
    rw [PowerSeries.algebraMap_apply]; rfl, Polynomial.aeval_algebraMap_apply]
  rw [PowerSeries.algebraMap_apply]; rfl

end U2E

end Formalism.MainNotions.N.Ln34
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2S

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfS_split [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) (ζ : O)
    (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ (a : O) (r : Fin e → O), IsUnit a ∧ (∀ j, r j ∈ IsLocalRing.maximalIdeal O) ∧
      E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)) ∧
      ∀ j, ∃ x : O, x ∈ IsLocalRing.maximalIdeal O ∧ (1 + x) ^ PD.p = 1 ∧ x ≠ 0 ∧
        (mkI x) (π' c) = (mkI x) (PowerSeries.C (r j)) := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨-, -, ⟨w, hw⟩, hdeg, ⟨w₁, hq⟩, -, -, -⟩ := hR
  set p := PD.p with hpdef
  have hp2 : 2 ≤ p := PD.hp.two_le
  set π := π' c with hπdef
  set u := (w : LetA O n) c with hudef
  have hu : IsUnit u := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  have hπu : π = u * PowerSeries.X ^ s' := by rw [hπdef, hw]; rfl
  set wq := (w₁ : LetA O n) c with hwqdef
  have hwq : IsUnit wq := w₁.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  set Ec := E c with hEcdef
  have hQ : W.q₀ = wq * Polynomial.aeval π Ec := congrFun hq c

  set I := Finset.Ico 1 p with hI
  let xs : ℕ → O := fun i => ζ ^ i - 1
  have hxroot : ∀ i, (1 + xs i) ^ p = 1 := fun i => by
    show (1 + (ζ ^ i - 1)) ^ p = 1
    rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hxm : ∀ i, xs i ∈ IsLocalRing.maximalIdeal O := fun i => u2ringPfE_mem_max p hpm (hxroot i)
  have hxinj : Set.InjOn xs I := by
    intro i hi j hj hij
    have h' : ζ ^ i = ζ ^ j := sub_left_injective hij
    exact hζ.pow_inj (Finset.mem_Ico.1 hi).2 (Finset.mem_Ico.1 hj).2 h'

  have hval : ∀ i, ∃ y : O, (mkI (xs i)) π = (mkI (xs i)) (PowerSeries.C y) := fun i =>
    DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) π
  choose yv hyv using hval
  have hyvm : ∀ i, yv i ∈ IsLocalRing.maximalIdeal O := by
    intro i
    obtain ⟨uv, huv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) u
    have h1 : (mkI (xs i)) π = (mkI (xs i)) (PowerSeries.C (uv * xs i ^ s')) := by
      rw [hπu, map_mul, map_pow, huv, DualFramesAlt.eigenRingInvariants.mk_X, ← map_pow, ← map_mul, ← map_pow, ← map_mul]
    have h2 := DualFramesAlt.eigenRingInvariants.ev_inj (hxm i) ((hyv i).symm.trans h1)
    rw [h2]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (hxm i) _ (by omega))

  have hEy : ∀ i ∈ I, Ec.eval (yv i) = 0 := by
    intro i hi
    have hxne : xs i ≠ 0 := by
      show ζ ^ i - 1 ≠ 0
      rw [sub_ne_zero]
      exact hζ.pow_ne_one_of_pos_of_lt (by have := (Finset.mem_Ico.1 hi).1; omega) (Finset.mem_Ico.1 hi).2
    obtain ⟨qv, hqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) W.q₀
    have h1 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia (xs i))) W.q₀_def
    have e1 : (mkI (xs i)) (PowerSeries.X * W.q₀) = (mkI (xs i)) (PowerSeries.C (xs i * qv)) := by
      rw [map_mul, DualFramesAlt.eigenRingInvariants.mk_X, hqv, ← map_mul, ← map_mul]
    have e2 : (mkI (xs i)) ((1 + PowerSeries.X) ^ p - 1) =
        (mkI (xs i)) (PowerSeries.C ((1 + xs i) ^ p - 1)) := by
      simp only [map_sub, map_pow, map_add, map_one, DualFramesAlt.eigenRingInvariants.mk_X]
    rw [e1, e2, hxroot i, sub_self] at h1
    have h3 := DualFramesAlt.eigenRingInvariants.ev_inj (hxm i) h1
    have hqv0 : qv = 0 := (mul_eq_zero.1 h3).resolve_left hxne
    obtain ⟨wv, hwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists (hxm i) wq
    have hwvu : IsUnit wv := u2ringPfE_val_unit (hxm i)
      ((PowerSeries.isUnit_iff_constantCoeff).1 hwq) hwv
    have h4 : (mkI (xs i)) W.q₀ = (mkI (xs i)) (PowerSeries.C (wv * Ec.eval (yv i))) := by
      rw [hQ, map_mul, hwv, u2ringPfE_mk_aeval (hyv i), ← map_mul, ← map_mul]
    rw [hqv, hqv0] at h4
    have h5 := DualFramesAlt.eigenRingInvariants.ev_inj (hxm i) h4
    exact (mul_eq_zero.1 h5.symm).resolve_left hwvu.ne_zero

  have hfib : ∀ y ∈ IsLocalRing.maximalIdeal O, (I.filter fun i => yv i = y).card ≤ s' := by
    intro y hy
    set Fb := I.filter fun i => yv i = y with hFb
    set Tt := Fb.image xs with hTt
    have hTcard : Tt.card = Fb.card :=
      Finset.card_image_of_injOn (hxinj.mono (by intro i hi; exact (Finset.mem_filter.1 hi).1))
    have hTm : ∀ t ∈ Tt, t ∈ IsLocalRing.maximalIdeal O := by
      intro t ht; obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ht; exact hxm i
    have hf0 : ∀ t ∈ Tt, Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia t) (π - PowerSeries.C y) = 0 := by
      intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      rw [map_sub, hyv i, (Finset.mem_filter.1 hi).2, sub_self]
    obtain ⟨k, hk⟩ := DualFramesAlt.eigenRingInvariants.prod_dvd Tt hTm _ hf0
    have hres : (π - PowerSeries.C y).map (IsLocalRing.residue O) =
        (PowerSeries.X ^ s' * u).map (IsLocalRing.residue O) := by
      rw [hπu, map_sub, PowerSeries.map_C, (IsLocalRing.residue_eq_zero_iff y).2 hy, map_zero, sub_zero,
        mul_comm]
    have := (DualFramesAlt.eigenRingInvariants.card_le_of_dvd Tt hTm hu hres hk).1
    omega

  set S := I.image yv with hS
  have hcardI : I.card = p - 1 := by rw [hI, Nat.card_Ico]
  have hsum := Finset.card_eq_sum_card_image yv I
  have hle : I.card ≤ S.card * s' := by
    rw [hsum]
    have := Finset.sum_le_card_nsmul S (fun y => (I.filter fun i => yv i = y).card) s'
      (fun y hy => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact hfib _ (hyvm i))
    simpa using this
  have hSe : e ≤ S.card := by
    have h1 : e * s' ≤ S.card * s' := by rw [hes, ← hcardI]; exact hle
    exact Nat.le_of_mul_le_mul_right h1 (by omega)

  have hq0 : W.q₀ ≠ 0 := u2ringPfB_q₀_ne_zero W PD.hp.ne_zero
  have hEc0 : Ec ≠ 0 := by
    intro h0; apply hq0; rw [hQ, h0, map_zero, mul_zero]
  have hSroots : S ⊆ Ec.roots.toFinset := by
    intro y hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hEc0]
    exact hEy i hi
  have hroots_le : Multiset.card Ec.roots ≤ e := (hdeg c) ▸ Polynomial.card_roots' Ec
  have h1 : S.card ≤ Ec.roots.toFinset.card := Finset.card_le_card hSroots
  have h2 : Ec.roots.toFinset.card ≤ Multiset.card Ec.roots := Multiset.toFinset_card_le _
  have hSeq : S = Ec.roots.toFinset := Finset.eq_of_subset_of_card_le hSroots (by omega)
  have hcardr : Multiset.card Ec.roots = Ec.natDegree := by rw [hdeg c]; omega
  have hnodup : Ec.roots.Nodup := by
    rw [← Multiset.toFinset_card_eq_card_iff_nodup]; omega
  have hsplit := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcardr

  set s := Ec.roots.toFinset with hsdef
  have hscard : s.card = e := by omega
  let eqv : Fin e ≃ s := (s.equivFin.trans (finCongr hscard)).symm
  refine ⟨Ec.leadingCoeff, fun j => (eqv j : O), ?_, ?_, ?_, ?_⟩
  ·
    by_contra hna
    have ham : Ec.leadingCoeff ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hna
    have hq : W.q₀ = PowerSeries.C Ec.leadingCoeff *
        (wq * Polynomial.aeval π (Ec.roots.map fun a => Polynomial.X - Polynomial.C a).prod) := by
      rw [hQ]
      conv_lhs => rw [← hsplit]
      rw [map_mul, Polynomial.aeval_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      ring
    have hc1 := congrArg (PowerSeries.coeff (p - 1)) hq
    rw [PowerSeries.coeff_C_mul] at hc1
    have hcoef : PowerSeries.coeff (p - 1) W.q₀ = 1 := by
      have h := congrArg (PowerSeries.coeff p) W.q₀_def
      have e : (1 + PowerSeries.X : PowerSeries O) ^ p =
          ((((1 : Polynomial O) + Polynomial.X) ^ p : Polynomial O) : PowerSeries O) := by
        simp [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
      obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
      rw [map_sub, e, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, Nat.choose_self,
        PowerSeries.coeff_one, if_neg (by omega), sub_zero, hp', PowerSeries.coeff_succ_X_mul] at h
      rw [hp', Nat.add_sub_cancel]
      exact_mod_cast h
    rw [hcoef] at hc1
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [hc1]; exact Ideal.mul_mem_right _ _ ham
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 this)
  · intro j
    show (eqv j : O) ∈ IsLocalRing.maximalIdeal O
    have hj : (eqv j : O) ∈ S := by rw [hSeq]; exact (eqv j).2
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hj
    rw [← hi]; exact hyvm i
  · conv_lhs => rw [← hsplit]
    congr 1
    have hval : s.val = Ec.roots := by rw [hsdef, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnodup]
    rw [← hval, ← Finset.prod_eq_multiset_prod, ← Finset.prod_coe_sort s]
    exact (Equiv.prod_comp eqv (fun x : s => Polynomial.X - Polynomial.C (x : O))).symm
  · intro j
    have hj : (eqv j : O) ∈ S := by rw [hSeq]; exact (eqv j).2
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.1 hj
    refine ⟨xs i, hxm i, hxroot i, ?_, ?_⟩
    · show ζ ^ i - 1 ≠ 0
      rw [sub_ne_zero]
      exact hζ.pow_ne_one_of_pos_of_lt (by have := (Finset.mem_Ico.1 hi).1; omega) (Finset.mem_Ico.1 hi).2
    · show (mkI xs i) π = _
      rw [hyv i]
      show _ = (mkI xs i) (PowerSeries.C (eqv j : O))
      rw [hij]

end U2S

end Formalism.MainNotions.N.Ln34
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section U2T

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

local notation "mkI" y => Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia y)

theorem u2ringPfT_natCast_unit [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) {s : ℕ} (hs1 : 1 ≤ s) (hsp : s < p) : IsUnit (s : O) := by
  have : CharP (IsLocalRing.ResidueField O) p :=
    (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
      rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact hpm)
  by_contra h
  have hm : (s : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 h
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero_iff _ p] at hm
  exact absurd (Nat.le_of_dvd (by omega) hm) (by omega)

theorem u2ringPfT_deriv [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) {x y : O}
    (hxm : x ∈ IsLocalRing.maximalIdeal O) (hx1 : (1 + x) ^ PD.p = 1) (hx0 : x ≠ 0)
    (hy : (mkI x) (π' c) = (mkI x) (PowerSeries.C y)) :
    ∃ ε : O, IsUnit ε ∧ y * (E c).derivative.eval y = (PD.p : O) * ε := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨-, -, ⟨w, hw⟩, -, ⟨w₁, hq⟩, -, -, -⟩ := hR
  set p := PD.p with hpdef
  have hp2 : 2 ≤ p := PD.hp.two_le
  set π := π' c with hπdef
  set u := (w : LetA O n) c with hudef
  have hu : IsUnit u := w.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  have hπu : π = u * PowerSeries.X ^ s' := by rw [hπdef, hw]; rfl
  set wq := (w₁ : LetA O n) c with hwqdef
  have hwq : IsUnit wq := w₁.isUnit.map (Pi.evalMonoidHom (fun _ : ZMod n => PowerSeries O) c)
  set Ec := E c with hEcdef
  have hQ : W.q₀ = wq * Polynomial.aeval π Ec := congrFun hq c
  set D := PowerSeries.derivative O with hD
  obtain ⟨uv, huv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm u
  obtain ⟨duv, hduv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D u)
  obtain ⟨wv, hwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm wq
  obtain ⟨dwv, hdwv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D wq)
  obtain ⟨qv, hqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm W.q₀
  obtain ⟨dqv, hdqv⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hxm (D W.q₀)
  have hwvu : IsUnit wv := u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hwq) hwv
  have huvu : IsUnit uv := u2ringPfE_val_unit hxm ((PowerSeries.isUnit_iff_constantCoeff).1 hu) huv

  have hqv0 : qv = 0 := by
    have h1 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) W.q₀_def
    have e1 : (mkI x) (PowerSeries.X * W.q₀) = (mkI x) (PowerSeries.C (x * qv)) := by
      rw [map_mul, DualFramesAlt.eigenRingInvariants.mk_X, hqv, ← map_mul, ← map_mul]
    have e2 : (mkI x) ((1 + PowerSeries.X) ^ p - 1) = (mkI x) (PowerSeries.C ((1 + x) ^ p - 1)) := by
      simp only [map_sub, map_pow, map_add, map_one, DualFramesAlt.eigenRingInvariants.mk_X]
    rw [e1, e2, hx1, sub_self] at h1
    exact (mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h1)).resolve_left hx0

  have hyu : y = uv * x ^ s' := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    rw [← hy, hπu, map_mul, map_pow, huv, DualFramesAlt.eigenRingInvariants.mk_X, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow]
  have hEy : Ec.eval y = 0 := by
    have h4 : (mkI x) W.q₀ = (mkI x) (PowerSeries.C (wv * Ec.eval y)) := by
      rw [hQ, map_mul, hwv, u2ringPfE_mk_aeval hy, ← map_mul]
      congr 1
      rw [map_mul]
    rw [hqv, hqv0] at h4
    exact (mul_eq_zero.1 (DualFramesAlt.eigenRingInvariants.ev_inj hxm h4).symm).resolve_left hwvu.ne_zero

  have hdX : D PowerSeries.X = 1 := PowerSeries.derivative_X
  have hd1 := congrArg D W.q₀_def
  rw [Derivation.leibniz, map_sub, Derivation.leibniz_pow, Derivation.map_one_eq_zero, sub_zero, map_add,
    Derivation.map_one_eq_zero, zero_add, hdX] at hd1
  have hd2 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hd1
  simp only [smul_eq_mul, mul_one, nsmul_eq_mul, map_add, map_mul, map_pow, map_natCast,
    DualFramesAlt.eigenRingInvariants.mk_X, hqv, hdqv, hqv0, map_one] at hd2
  have hDπ : D π = u * ((s' : PowerSeries O) * PowerSeries.X ^ (s' - 1)) + PowerSeries.X ^ s' * D u := by
    rw [hπu, Derivation.leibniz, Derivation.leibniz_pow, hdX]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one]
    try ring
  have hdq := congrArg D hQ
  rw [Derivation.leibniz, Derivation.map_aeval, hDπ] at hdq
  have hdq2 := congrArg (Ideal.Quotient.mk (DualFramesAlt.eigenRingInvariants.Ia x)) hdq
  simp only [smul_eq_mul, map_add, map_mul, map_pow, map_natCast, DualFramesAlt.eigenRingInvariants.mk_X, hdqv, hwv, hduv, huv,
    u2ringPfE_mk_aeval hy, hEy] at hdq2

  have e1 : x * dqv = (p : O) * (1 + x) ^ (p - 1) := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    simp only [map_mul, map_pow, map_add, map_one, map_natCast]
    simp only [map_zero, add_zero] at hd2
    linear_combination hd2
  have e2 : dqv = wv * ((Ec.derivative.eval y) * (uv * ((s' : O) * x ^ (s' - 1)) + x ^ s' * duv)) := by
    apply DualFramesAlt.eigenRingInvariants.ev_inj hxm
    simp only [map_mul, map_pow, map_add, map_natCast]
    simp only [map_zero, zero_mul, add_zero] at hdq2
    linear_combination hdq2
  have hs'u : IsUnit (s' : O) := u2ringPfT_natCast_unit p hpm hs (by
    have : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h, zero_mul] at hes; omega
      · exact h
    have : s' ≤ e * s' := Nat.le_mul_of_pos_left s' this
    omega)
  have hD0 : IsUnit (wv * (uv * (s' : O) + x * duv)) := by
    refine hwvu.mul ?_
    by_contra hn
    have hm : uv * (s' : O) + x * duv ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hn
    have hm2 : uv * (s' : O) ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right duv _ hxm)
      rwa [add_sub_cancel_right] at this
    exact (IsLocalRing.mem_maximalIdeal _).1 hm2 (huvu.mul hs'u)
  have h1xe : (1 + x) * (1 + x) ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega), hx1]
  have h1x : IsUnit (1 + x) := ⟨⟨1 + x, (1 + x) ^ (p - 1), h1xe, by rw [mul_comm]; exact h1xe⟩, rfl⟩
  obtain ⟨Du, hDu⟩ := hD0
  refine ⟨uv * (1 + x) ^ (p - 1) * ((Du⁻¹ : Oˣ) : O), (huvu.mul (h1x.pow _)).mul (Du⁻¹).isUnit, ?_⟩
  have key : y * Ec.derivative.eval y * (wv * (uv * (s' : O) + x * duv)) = (p : O) * (uv * (1 + x) ^ (p - 1)) := by
    obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at e2
    linear_combination (Ec.derivative.eval y * (wv * (uv * ((s'' + 1 : ℕ) : O) + x * duv))) * hyu -
      (uv * x) * e2 + uv * e1
  have hDuinv : ((Du : Oˣ) : O) * ((Du⁻¹ : Oˣ) : O) = 1 := Units.mul_inv Du
  rw [hDu] at hDuinv
  calc y * Ec.derivative.eval y = y * Ec.derivative.eval y * ((wv * (uv * (s' : O) + x * duv)) *
        ((Du⁻¹ : Oˣ) : O)) := by rw [hDuinv, mul_one]
    _ = (p : O) * (uv * (1 + x) ^ (p - 1) * ((Du⁻¹ : Oˣ) : O)) := by rw [← mul_assoc, key]; ring

theorem u2ringPfT_split [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O}
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (hs : 1 ≤ s') (hes : e * s' = PD.p - 1)
    (hpm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (c : ZMod n) (ζ : O)
    (hζ : IsPrimitiveRoot ζ PD.p) (hp2 : PD.p ≠ 2) (hι : Function.Injective (algebraMap O LL))
    (hRv : ∀ x : LL, 0 ≤ v x ↔ ∃ a : O, algebraMap O LL a = x) :
    ∃ (a : O) (r : Fin e → O), IsUnit a ∧ (∀ j, r j ∈ IsLocalRing.maximalIdeal O) ∧
      E c = Polynomial.C a * ∏ j, (Polynomial.X - Polynomial.C (r j)) ∧
      ∀ (j : Fin e) (w₀ : O), IsUnit w₀ → ∀ t : ℕ, 0 < t →
        (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) ^ t ≠ 1 := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨a, r, ha, hrm, hsplit, hpt⟩ := u2ringPfS_split W hR hs hes hpm c ζ hζ
  refine ⟨a, r, ha, hrm, hsplit, ?_⟩
  intro j w₀ hw₀ t ht
  obtain ⟨x, hxm, hx1, hx0, hxy⟩ := hpt j
  obtain ⟨ε, hε, hyE⟩ := u2ringPfT_deriv W hR hs hes hpm c hxm hx1 hx0 hxy
  have hder : (E c).derivative.eval (r j) = a * ∏ j' ∈ Finset.univ.erase j, (r j - r j') := by
    rw [hsplit, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
      Polynomial.derivative_prod_finset, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finset_sum]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp [Polynomial.eval_prod]
    · intro b _ hb
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun h => hb h.symm, Finset.mem_univ j⟩) (by simp)]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hder] at hyE
  have hxt : (1 + r j * w₀ * a * ∏ j' ∈ Finset.univ.erase j, (r j - r j')) - 1 = ((PD.p : ℕ) : O) * (w₀ * ε) := by
    linear_combination w₀ * hyE
  obtain ⟨ε', hε', he'⟩ := gradNPf_lte v (algebraMap O LL) hι hRv PD.p hp2 W.v_l _ (w₀ * ε) (hw₀.mul hε) hxt t
    (by omega)
  intro h1
  rw [h1, sub_self] at he'
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.2 PD.hp.ne_zero
  exact (mul_ne_zero (pow_ne_zero _ hp0) hε'.ne_zero) he'.symm

end U2T

end Formalism.MainNotions.N.Ln34
end
end

section
noncomputable section

namespace Formalism.MainNotions.N.Ln34.AdicCompletionMax

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem span_eq_max_pow {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.span {p} = IsLocalRing.maximalIdeal O ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (mt Ideal.span_singleton_eq_bot.mp hp0) hϖ
  refine ⟨n, Nat.one_le_iff_ne_zero.mpr ?_, ?_⟩
  · rintro rfl
    rw [pow_zero, Ideal.span_singleton_one, Ideal.span_singleton_eq_top] at hn
    exact absurd hn ((IsLocalRing.mem_maximalIdeal _).1 hpm)
  · rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

private theorem isAdicComplete_of_isAdicComplete_pow {J : Ideal O} {k : ℕ} (hk : 1 ≤ k)
    (h : IsAdicComplete (J ^ k) O) : IsAdicComplete J O := by
  have key : ∀ n : ℕ, (J ^ k) ^ n = J ^ (k * n) := fun n => (pow_mul J k n).symm
  have hkn : ∀ n : ℕ, n ≤ k * n := fun n => by simpa using Nat.mul_le_mul hk (le_refl n)
  have hle : ∀ {a b : ℕ}, a ≤ b → J ^ b • (⊤ : Submodule O O) ≤ J ^ a • ⊤ :=
    fun hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · refine IsHausdorff.haus h.toIsHausdorff x fun n => ?_
    rw [key]
    exact hx (k * n)
  · obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => f (k * n))
      (fun {a b} hab => by
        rw [key]
        exact hf (Nat.mul_le_mul (le_refl k) hab))
    refine ⟨L, fun n => ?_⟩
    have h1 : f n ≡ f (k * n) [SMOD (J ^ n • ⊤ : Submodule O O)] := hf (hkn n)
    have h2 : f (k * n) ≡ L [SMOD (J ^ n • ⊤ : Submodule O O)] := by
      have h3 := hL n
      rw [key] at h3
      exact SModEq.mono (hle (hkn n)) h3
    exact h1.trans h2

theorem isAdicComplete_max {p : O} (hp0 : p ≠ 0) (hpm : p ∈ IsLocalRing.maximalIdeal O)
    [h : IsAdicComplete (Ideal.span {p}) O] : IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  obtain ⟨k, hk, hkeq⟩ := span_eq_max_pow hp0 hpm
  rw [hkeq] at h
  exact isAdicComplete_of_isAdicComplete_pow hk h

end Formalism.MainNotions.N.Ln34.AdicCompletionMax
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem u2ringPf_zetaO {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) {ζ : ↥LL.1}
    (hζ : IsPrimitiveRoot ζ l) : ∃ z : ↥(OL LL), IsPrimitiveRoot z l := by
  have hv : 0 ≤ P.v LL ζ := by
    have h1 : P.v LL (ζ ^ l) = 0 := by rw [hζ.pow_eq_one, AddValuation.map_one]
    rw [AddValuation.map_pow] at h1
    cases hq : P.v LL ζ using WithTop.recTopCoe with
    | top =>
      exfalso
      rw [hq] at h1
      obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Fact.out : l.Prime).pos; omega⟩
      rw [hk, succ_nsmul, WithTop.add_top] at h1
      exact WithTop.top_ne_zero h1
    | coe q =>
      rw [hq] at h1
      have h2 : ((l • q : ℚ) : WithTop ℚ) = 0 := by rw [WithTop.coe_nsmul]; exact h1
      have h3 : l • q = 0 := by exact_mod_cast h2
      rw [nsmul_eq_mul, mul_eq_zero] at h3
      rcases h3 with h3 | h3
      · exact absurd (by exact_mod_cast h3 : l = 0) (Fact.out : l.Prime).ne_zero
      · rw [h3]; exact le_refl _
  refine ⟨⟨ζ, (P.v_O LL ζ).1 hv⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥(OL LL) ↥LL.1) hζ Subtype.val_injective

theorem u2ring_pf : SecondRingHypothesis := by
  intro D HW F Cm CA CB CK _ l _ hl K LL hG π' E hR h' hh' c
  have hlp : l.Prime := Fact.out
  have : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have : CharZero ↥(OL LL) := Formalism.MainNotions.UnusedSlot80.levg_charZero LL
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hV := Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL
  have hpu := Formalism.MainNotions.WachCoordinates.Br.not_isUnit_p ((HW l).W K 1 LL hG) hV
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) :=
    (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hp0 : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ≠ 0 := Nat.cast_ne_zero.2 (by rw [hpl]; exact hlp.ne_zero)
  have : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [hpl]; exact Formalism.MainNotions.WachCoordinates.Br.complete_OL LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := AdicCompletionMax.isAdicComplete_max hp0 hpm
  have hs : 1 ≤ sK l K := DescentValuation.u3downPf_sK_pos hl K LL hG
  have hd := DvdPf.dvdCondition l hl K LL hG
  have hes : eK K * sK l K = ((D.loc l).PD K).p - 1 := by rw [hpl]; exact Nat.mul_div_cancel' hd
  obtain ⟨ζL, hζL⟩ := Formalism.MainNotions.N.zeta_of_good (D.loc l) hG
  obtain ⟨ζ, hζ⟩ := u2ringPf_zetaO (D.loc l) LL hζL
  have hζ' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hpl]; exact hζ
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  obtain ⟨a, r, ha, hrm, hE, hnr⟩ := u2ringPfT_split ((HW l).W K 1 LL hG) hR hs hes hpm c ζ hζ' hp2 hι hRv
  exact u2ringPfD_main ((HW l).W K 1 LL hG) hR hs (((HW l).W K 1 LL hG).gamK_eq_one hs1 hp2) le_rfl c a ha r
    hrm hE hnr h' hh'

end Formalism.MainNotions.N.Ln34
end
end
