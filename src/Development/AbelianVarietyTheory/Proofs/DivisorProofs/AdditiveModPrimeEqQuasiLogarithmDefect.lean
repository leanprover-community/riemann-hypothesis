import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricCocycleModIdealEqCoboundaryQuasiLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCoboundaryRepresentativeCocycleRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefectCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesLiftQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFormalGroupLawCoboundaryOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalChartQuotientByIdealWithPrimePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneTmulQuotReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionsEqSeriesInChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFormalGroupCocycleIffMemCocycles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesEvalTwoGroupsRules
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMapOfNatMultipleFormalGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultiple

section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.defect_ev_succ_eq_mulP_add_p_pow_smul : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → (∀ n, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ n f ∧ constantCoeff s = 0) ∧ ∀ (n : ℕ) (s s' : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → map (algebraMap O E) s' = defect c.μ (p ^ (n + 1)) f → ∃ z, c.ev (n + 1) s' = G.mulP n (c.ev n s) + (p : O) ^ n • z := by
  first | exact @GlobalTheory.QLog.defect_compat | exact GlobalTheory.QLog.defect_compat | (intros; apply GlobalTheory.QLog.defect_compat <;> assumption)
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ I : Ideal O, (p : O) ∈ I → ∀ s : MvPowerSeries (Fin d) O, (∀ α, coeff α (cob1 c.μ s) ∈ I) → ∀ α, coeff α s ∈ I := by
  intro p _ O _ G d c I hp s hs α
  obtain ⟨c', hlaw, -, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 (by rwa [pow_one])
  have hpk : ((p : ℕ) : O ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hp
  have hmap := (GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ c.isLaw.const (O ⧸ I) (Ideal.Quotient.mk I)).1 s
  have hz : map (Ideal.Quotient.mk I) (cob1 c.μ s) = 0 := by
    ext β
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hs β
  rw [hz] at hmap
  have h0 := GlobalTheory.Katz.eq_zero_of_cob1_eq_zero p (O ⧸ I) hpk d (G.baseChange (O ⧸ I)) c'
    (fun i => map (Ideal.Quotient.mk I) (c.μ i)) hlaw (map (Ideal.Quotient.mk I) s) hmap.symm
  have := congrArg (coeff α) h0
  rwa [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at this

end GlobalTheory.QLog
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_mem_of_coeff_cob1_mem : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ I : Ideal O, (p : O) ∈ I → ∀ s : MvPowerSeries (Fin d) O, (∀ α, coeff α (cob1 c.μ s) ∈ I) → ∀ α, coeff α s ∈ I := by
  atlas_forward_decl GlobalTheory.QLog.coeff_mem_ideal_of_formalGroupCoboundaryOne_coeff_mem
end

section
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.Chart

theorem exists_series_of_cobOne_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ)
    (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k),
    c.IsLawOf μ → ∀ b : G.A 1, cobOne k (G.A 1) b = 0 →
    ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k),
      IsCoc μ κ ∧ constantCoeff κ = 0 ∧ cob1 μ B = pull2 (nmul μ p) κ ∧ c.ev 1 B = b := by
  intro p _ k _ d G c μ hμ b hb
  obtain ⟨x, cc, B, -, hcob, hcounit, hB1⟩ := PDivGroup.exists_of_cobOne_eq_zero (G := G) hb
  have hfun := Chart.functions_are_series p k d G c
  have hsq := chart_square_presents p k d G c
  obtain ⟨Bs, hBs, -⟩ := hfun.2.2 B.1 B.2
  obtain ⟨κ, hκ, -⟩ := hsq.2 cc.1 (fun n => (cc.2 n).2)
  have hlaw := (LawCoord.main p k d G c).2 μ hμ
  have hcoc : IsCoc μ κ := (isCoc_iff_mem_cocycles p k d G c μ hμ κ).2 (by
    have e : (fun n => c.ev₂ n κ) = cc.1 := funext hκ
    rw [e]; exact cc.2)
  have hmap := (isMapOf_existsUnique_and p k d d G G c c ((p : ℤ_[p]) • 𝟙 G)).2 (nmul μ p)
    (GlobalTheory.T.isMapOf_natMultiple_formalGroupLaw p k d G c μ hμ p)
  have hid : cob1 μ Bs = pull2 (nmul μ p) κ := by
    obtain ⟨s, -, hs⟩ := hsq.2 (fun n => c.ev₂ n (cob1 μ Bs)) (fun n => hfun.2.1 n _)
    refine (hs _ fun n => rfl).trans (hs _ fun n => ?_).symm
    rw [(hmap.2 n).2, hκ, (hlaw.2 n Bs).2, hBs]
    exact (congrArg (fun z : G.cocycles => z.1 n) hcob).symm
  have hB0 : constantCoeff Bs = 0 := by
    have h := (counit_dUnit_evA k d (G.A 1) (c.x 1) (c.nil 1) (c.aug 1) Bs).1
    rw [← h]
    change Coalgebra.counit (R := k) (c.ev 1 Bs) = 0
    rw [hBs 1, hB1, hcounit]
  have hX : ∀ (σ : Type) (i : σ), constantCoeff (X i : MvPowerSeries σ k) = 0 :=
    fun _ i => constantCoeff_X i
  have hL : ∀ j, constantCoeff (inL (nmul μ p j)) = 0 := fun j => by
    unfold inL
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hR : ∀ j, constantCoeff (inR (nmul μ p j)) = 0 := fun j => by
    unfold inR
    rw [SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hmap.1 j]
  have hκ0 : constantCoeff κ = 0 := by
    have h1 := (SubstCalc.powerSeriesEvalTwoGroups_rules_alt k d (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) _ _ hL hR).2.2.2.1 κ
    have h2 : constantCoeff (cob1 μ Bs) = 0 := by
      unfold cob1 inL inR
      rw [map_sub, map_sub, SubstCalc.constantCoeff_subst_of_zero hlaw.1,
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _),
        SubstCalc.constantCoeff_subst_of_zero (fun i => hX _ _), hB0, sub_zero, sub_zero]
    rw [← h1, ← h2, hid]
    rfl
  exact ⟨κ, Bs, hcoc, hκ0, hid, (hBs 1).trans hB1⟩

end GlobalTheory.Katz.Chart
end
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_of_additive_function_first_level : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Katz.Chart G d) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ → ∀ b : G.A 1, cobOne k (G.A 1) b = 0 → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) k) (B : MvPowerSeries (Fin d) k), IsCoc μ κ ∧ constantCoeff κ = 0 ∧ cob1 μ B = pull2 (nmul μ p) κ ∧ c.ev 1 B = b := by
  atlas_forward_decl GlobalTheory.Katz.Chart.exists_series_of_cobOne_eq_zero
end

section
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

set_option maxHeartbeats 1000000 in

theorem exists_series_of_cobOne_dvd : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  intro p _ O _ G d c b z hbz
  let I : Ideal O := Ideal.span {(p : O)}
  have hpI : (p : O) ^ 1 ∈ I := by rw [pow_one]; exact Ideal.subset_span rfl
  obtain ⟨c', hlaw, hev, -⟩ := GlobalTheory.T.exists_formalChart_quotient_by_ideal_with_primePow p O G d c I 1 hpI
  have hmkp : (algebraMap O (O ⧸ I)) (p : O) = 0 := by
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span rfl
  have hb' : cobOne (O ⧸ I) ((G.baseChange (O ⧸ I)).A 1) ((G.toBase (O ⧸ I)).app 1 b) = 0 := by
    rw [← SemiBialgHom.two_cobOne, hbz, map_smulₛₗ, hmkp, zero_smul]
  obtain ⟨κ', B', hcoc, hκ0, hcob, hev1⟩ := GlobalTheory.T.exists_series_of_additive_function_first_level p (O ⧸ I) d _ c' _ hlaw _ hb'
  obtain ⟨hl2, hz2, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ Fin d) I
  obtain ⟨hl1, hz1, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d ⊕ (Fin d ⊕ Fin d)) I
  obtain ⟨hl0, -, -⟩ := GlobalTheory.mvPowerSeries_lift_quotient O (Fin d) I
  obtain ⟨κ, hκ, hκc⟩ := hl2 κ'
  obtain ⟨B, hB, -⟩ := hl0 B'
  have hdiv : ∀ x : O, x ∈ I ↔ (p : O) ∣ x := fun x => Ideal.mem_span_singleton
  have hμ := c.isLaw.const
  obtain ⟨hm1, hm2, hsw, -, hpull⟩ := GlobalTheory.T.map_coboundary_swap_pullback_commute O d c.μ hμ (O ⧸ I) (Ideal.Quotient.mk I)
  obtain ⟨-, hn⟩ := GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple O d c.μ c.isLaw (O ⧸ I) (Ideal.Quotient.mk I)
  have hnm : (fun i => map (Ideal.Quotient.mk I) (nmul c.μ p i)) =
      nmul (fun i => map (Ideal.Quotient.mk I) (c.μ i)) p := funext fun i => (hn p i).2
  obtain ⟨hpl, -⟩ := hpull (nmul c.μ p) fun i => (hn p i).1
  have hy : ∃ y : G.A 1, c.ev 1 B = b + (p : O) • y := by
    have h1 : (G.toBase (O ⧸ I)).app 1 (c.ev 1 B) = (G.toBase (O ⧸ I)).app 1 b := by
      rw [← hev, hB, hev1]
    rw [toBase_app, toBase_app] at h1
    have h2 : (1 : O ⧸ I) ⊗ₜ[O] (c.ev 1 B - b) = 0 := by rw [tmul_sub, h1, sub_self]
    obtain ⟨-, hq, hs⟩ := GlobalTheory.PDiv.one_tmul_quot_reduction O (G.A 1) I
    obtain ⟨y, hy⟩ := (hs (p : O) _).1 ((hq _).1 h2)
    exact ⟨y, by rw [← hy]; abel⟩
  obtain ⟨y, hy⟩ := hy
  refine ⟨κ, B, y, hκc hκ0, ?_, ?_, ?_, hy⟩
  · intro α
    refine (hdiv _).1 ((hz1 _).1 ?_ α)
    rw [hm2, hκ]; exact hcoc.1
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hsw, hκ, hcoc.2, sub_self]
  · intro α
    refine (hdiv _).1 ((hz2 _).1 ?_ α)
    rw [map_sub, hm1, hpl, hκ, hB, hnm, hcob, sub_self]

end GlobalTheory.QLog
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalSeries_of_coboundary_dvd_p : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (κ : MvPowerSeries (Fin d ⊕ Fin d) O) (B : MvPowerSeries (Fin d) O) (y : G.A 1), constantCoeff κ = 0 ∧ (∀ α, (p : O) ∣ coeff α (cob2 c.μ κ)) ∧ (∀ α, (p : O) ∣ coeff α (Katz.swap κ - κ)) ∧ (∀ α, (p : O) ∣ coeff α (cob1 c.μ B - pull2 (nmul c.μ p) κ)) ∧ c.ev 1 B = b + (p : O) • y := by
  atlas_forward_decl GlobalTheory.QLog.exists_series_of_cobOne_dvd
end

section
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

namespace DefectSurj

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_const {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) : ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ n ih =>
    intro i
    rw [nmul, Function.iterate_succ_apply', ← nmul, op, at2]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ n)
        (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j) <;> simp [ih]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

theorem powerSeriesPullbackTwoGroups_add_smul {φ : Fin d → MvPowerSeries (Fin d) R} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (a : R) (κ h : MvPowerSeries (Fin d ⊕ Fin d) R) :
    pull2 φ (κ + a • h) = pull2 φ κ + a • pull2 φ h := by
  have hs : HasSubst (Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j))) := by
    refine hasSubst_of_constantCoeff_zero ?_
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) (hφ j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
        (fun _ => constantCoeff_X _) (hφ j)
  unfold pull2 at2
  rw [subst_add hs, subst_smul hs]

end DefectSurj

theorem additive_mod_p_is_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f ∧ map (algebraMap O E) s = defect c.μ p f ∧ c.ev 1 s = b + (p : O) • y := by
  intro p _ O E _ _ _ hF G d c b z hb
  obtain ⟨κ, B, y, h0, h2, hsw, hB, hev⟩ := GlobalTheory.T.exists_formalSeries_of_coboundary_dvd_p p O G d c (-b) (-z)
    (by rw [map_neg, hb, smul_neg])
  obtain ⟨f, hf, -, hin⟩ := GlobalTheory.T.symmetricCocycle_modIdeal_eq_coboundary_quasiLog p O E hF d c.μ c.isLaw (p : O) dvd_rfl κ h0 h2 hsw
  obtain ⟨t, ht, hmt⟩ := (GlobalTheory.series_in_ideal_iff_image O E _ _ _).1.1 hin
  obtain ⟨h, rfl⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) t).1
    (fun α => Ideal.mem_span_singleton.1 (ht α))
  have hκ : map (algebraMap O E) (κ + (p : O) • h) = cob1 (up E c.μ) f := by
    rw [map_add, hmt]; abel
  obtain ⟨s, hs, -⟩ := (GlobalTheory.T.defect_ev_succ_eq_mulP_add_p_pow_smul p O E hF G d c f hf).1 p
  have hc := ((GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f _ hκ).2.2 p s hs).1
  rw [DefectSurj.powerSeriesPullbackTwoGroups_add_smul (DefectSurj.nmul_const c.isLaw.const p)] at hc
  obtain ⟨u, hu⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).1 hB
  have hsum : cob1 c.μ (s + B) =
      (p : O) • (κ + (p : O) • h - pull2 (nmul c.μ p) h + u) := by
    rw [formalCoboundary_add c.isLaw.const, hc, smul_add _ _ u, smul_sub, ← hu]; abel
  have hdiv := GlobalTheory.T.coeff_mem_of_coeff_cob1_mem p O G d c (Ideal.span {(p : O)}) (Ideal.mem_span_singleton_self _)
    (s + B) (fun α => Ideal.mem_span_singleton.2
      (((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).2 ⟨_, hsum⟩ α))
  obtain ⟨w, hw⟩ := ((GlobalTheory.mvPowerSeries_lift_quotient O _ ⊤).2.2 (p : O) _).1
    (fun α => Ideal.mem_span_singleton.1 (hdiv α))
  refine ⟨f, s, c.ev 1 w - y, hf, hs, ?_⟩
  have := congrArg (c.ev 1) hw
  rw [map_add, map_smul, hev] at this
  rw [smul_sub, ← this]; abel

end GlobalTheory.QLog
end

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_mod_prime_eq_quasiLogarithm_defect : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (b : G.A 1) (z : G.A 1 ⊗[O] G.A 1), cobOne O (G.A 1) b = (p : O) • z → ∃ (f : MvPowerSeries (Fin d) E) (s : MvPowerSeries (Fin d) O) (y : G.A 1), QL c.μ ⊤ f ∧ map (algebraMap O E) s = defect c.μ p f ∧ c.ev 1 s = b + (p : O) • y := by
  atlas_forward_decl GlobalTheory.QLog.additive_mod_p_is_defect
end
