import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelActionShortThetaSeriesRootOfUnityMul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqOfForallAlgClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetCharacterReductionInvariant
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.OrientationExclusive

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceLattice

section Datum

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.OnTies GlobalTheory.DatumInverseCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}

def DetOne (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) : Prop :=
  LinearMap.det (LinearMap.baseChange (𝓞 E ⧸ l.Mb) (liftLa γ)) = 1

theorem natCast_mem_half (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb ∧ ((l.M : ℕ) : 𝓞 E) ∈ Mfr l := by
  have h : ((l.M : ℕ) : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [l.prod]; exact Ideal.mem_span_singleton_self _
  exact ⟨(Ideal.mul_le_inf.trans inf_le_left) h, (Ideal.mul_le_inf.trans inf_le_right) h⟩

theorem exists_rightMul (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) {n : ℕ} {rk : Bool} {x : Fin n → Dw.La}
    (hx : AdmX (l := l) rk x) : ∃ x' : Fin n → Dw.La, IsRightMul γ x x' ∧ AdmX (l := l) rk x' := by
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  obtain ⟨g, -, hγ, -⟩ := GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism _ _ Dw l γ
  obtain ⟨g', hg'⟩ := g.inv l.M hM₁
  obtain ⟨fa, hfa⟩ := exists_adjoint Dw (g.f l.M)
  obtain ⟨ga, hga⟩ := exists_adjoint Dw g'
  have hsurj : ∀ a, ∃ b, fa b - a ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := fun a =>
    ⟨ga a, mem_of_modN Dw (natCast_mem_half l).2 (modN_of_dvd Dw hM₁ fun v => by
      rw [map_sub, LinearMap.sub_apply, hfa, hga, ← map_sub]
      exact dvd_of_modN Dw a (hg' v).1)⟩
  refine ⟨fun b => fa (x b), fun b a => ?_,
    GlobalTheory.DatumCoverAdjoint.span_image_sup_eq_top (Mfr l) fa hsurj x _ hx⟩
  rw [hfa, map_smul, ← map_sub, ← smul_sub]
  exact dvd_pair_of_mem _ ((Submodule.Quotient.eq _).1 ((hγ a).trans (liftLa_spec γ a).symm))

theorem datum_move {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (hM : d.l₂.M = l.M * d.pd)
    (hb : d.l₂.Mb = l.Mb * d.I) {ph : (Fin n → LaJ Xo c d) → c.F} {ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ}
    {x₀ : Fin n → LaJ Xo c d} (hpin : d.PhiPin ph ψ x₀) (f : Dw.La →ₗ[𝓞 E] Dw.La)
    (hg : ∀ a, f a - a ∈ d.I • (⊤ : Submodule (𝓞 E) Dw.La)) {γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l}
    (hγ : ∀ a, f a - liftLa γ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) (σ : LevQ Dw d.l₂ ≃ LevQ Dw d.l₂)
    (hσ : ∀ a, σ (Submodule.Quotient.mk a) = Submodule.Quotient.mk (f a)) {x x' : Fin n → Dw.La}
    (hx : IsRightMul γ x' x) (q : Fin n → LevQ Dw d.l₂) : d.w x (fun b => σ.symm (q b)) = d.w x' q := by
  obtain ⟨-, -, -, -, -, hφ⟩ := hpin
  have hM₂ : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  have hM₁ : 0 < l.M := by have := l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ hM₂)
  have hIJ := half_prod hM hb
  have hbI : d.l₂.Mb ≤ d.I := hb ▸ (Ideal.mul_le_inf.trans inf_le_right)
  have hbM : d.l₂.Mb ≤ l.Mb := hb ▸ (Ideal.mul_le_inf.trans inf_le_left)
  have hq : ∀ b, f (levRep (σ.symm (q b))) - levRep (q b) ∈ (d.l₂.Mb • ⊤ : Submodule (𝓞 E) Dw.La) := by
    intro b
    rw [← Submodule.Quotient.eq, ← hσ, levRep_spec, levRep_spec]
    exact σ.apply_symm_apply _
  have hz : zetaM c ^ pairL (l := l) x (fun b => levRep (σ.symm (q b))) =
      zetaM c ^ pairL (l := l) x' (fun b => levRep (q b)) := by
    refine zpow_congr hM₁ (root_pow c dvd_rfl) ?_
    unfold pairL
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    have h1 := sub_mem (Submodule.smul_mono hbM le_rfl (hq b)) (hγ (levRep (σ.symm (q b))))
    have h2 := dvd_pair_of_mem (l := l) (x' b) h1
    rw [sub_sub_sub_cancel_left, smul_sub, map_sub] at h2
    have h3 := dvd_add (hx b (levRep (σ.symm (q b)))) h2
    rwa [sub_add_sub_cancel] at h3
  have hroot := root_pow d.c₂ (N := d.pd) (hM ▸ Dvd.intro_left _ rfl)
  have hδ : d.eF (d.φδ (fun b => σ.symm (q b))) = d.eF (d.φδ q) := by
    rw [hφ, hφ]
    refine finsum_congr fun x => ?_
    congr 1
    refine zpow_congr hpd hroot ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun b _ => ?_
    rw [← map_sub, ← smul_sub]
    refine dvd_right Dw hIJ (cHalf_mem d.I) _ ?_
    have := sub_mem (Submodule.smul_mono hbI le_rfl (hq b)) (hg (levRep (σ.symm (q b))))
    convert this using 1
    abel
  unfold DeltaDat.w
  rw [hz, map_mul, map_mul, hδ]

theorem char_eq_one_of_detOne (h3 : ¬ 3 ∣ l.M) {A : Type} [CommGroup A] (χ : (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) →* A)
    {γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l} (hγ : DetOne γ) : χ γ = 1 := by
  haveI := Dw.fin
  haveI := Dw.proj
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ fun h => by
    have := (natCast_mem_half l).1
    rw [h, Ideal.mem_bot] at this
    exact hM0 (by exact_mod_cast this)
  have h4 : ∀ 𝔪 : Ideal (𝓞 E ⧸ l.Mb), 𝔪.IsMaximal → 4 ≤ Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := by
    intro 𝔪 h
    haveI : Nontrivial ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Ideal.Quotient.nontrivial_iff.2 h.ne_top
    haveI : Finite ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    haveI : Fintype ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Fintype.ofFinite _
    have h1 : 1 < Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) := Finite.one_lt_card
    have h0 : ((Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) : ℕ) : (𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 0 := by
      rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    have hN' : (l.M : (𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk 𝔪), ← map_natCast (Ideal.Quotient.mk l.Mb),
        Ideal.Quotient.eq_zero_iff_mem.2 (natCast_mem_half l).1, map_zero]
    by_contra hlt
    have hc : Nat.Coprime (Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪)) l.M := by
      have : Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 2 ∨ Nat.card ((𝓞 E ⧸ l.Mb) ⧸ 𝔪) = 3 := by omega
      rcases this with h | h <;> rw [h]
      · exact Nat.coprime_two_left.2 l.odd
      · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    have := hc.cast (R := (𝓞 E ⧸ l.Mb) ⧸ 𝔪)
    rw [h0, hN'] at this
    exact not_isCoprime_zero_zero this
  have h := GlobalTheory.char_eq_one_of_inverse_reduction_det_one (𝓞 E) Dw.La Dw.La l.Mb A χ LinearMap.id (liftLa γ) γ⁻¹ h4
    (fun b => ⟨b, by simp⟩) (fun _ h => h) hγ fun a => by
      obtain ⟨a', ha'⟩ := Submodule.Quotient.mk_surjective _ (γ⁻¹ (Submodule.Quotient.mk a))
      refine ⟨a', ha', (Submodule.Quotient.eq _).1 ?_⟩
      exact (liftLa_spec γ a').trans ((congrArg γ ha').trans (γ.apply_symm_apply _))
  rwa [map_inv, inv_eq_one] at h

end Datum

section Move

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.ShortMove
open scoped TensorProduct

variable {D : D7}

def TwistTrivialOnRational (T : Full D) (j : ℕ) : Prop :=
  ∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀),
    T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1

def GoodDatum (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ j w.n).l₂.M ∧ Λ.LevOK N (T.dδ j w.n).l₂.M ∧ P ∈ harmL T.Q.c Λ (wtA w)

def IsSeries (T : Top D) (j : ℕ) (w : WeightFamilies.Wt D j) (Λ : GenLat D.host.E w.n) (N : ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (x : Fin w.n → (T.Q.Dw j).La) (f : T.R j) : Prop :=
  AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x ∧ f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n ∧
    IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x P f

variable {j : ℕ} {w : WeightFamilies.Wt D j}

theorem IsSeries.mem_sh {T : Top D} {Λ N P x f} (hG : GoodDatum T j w Λ N P) (hf : IsSeries T j w Λ N P x f) :
    f ∈ T.sh j w :=
  ⟨hf.2.1, Λ, N, x, P, hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hf.1, hG.2.2.2.2, hf.2.2⟩

theorem exists_isSeries {T : Top D} (hT : LawsSh T) (hj : InR D j) {Λ N P} (hG : GoodDatum T j w Λ N P)
    {x : Fin w.n → (T.Q.Dw j).La} (hx : AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x) : ∃ f, IsSeries T j w Λ N P x f := by
  obtain ⟨f, hf, hR⟩ := (hT.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x P hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hx hG.2.2.2.2).2
  exact ⟨f, hx, hf, hR⟩

theorem IsSeries.unique {T : Top D} (hT : LawsSh T) (hj : InR D j) {Λ N P x f f'} (hG : GoodDatum T j w Λ N P)
    (hf : IsSeries T j w Λ N P x f) (hf' : IsSeries T j w Λ N P x f') : f = f' := by
  have tot := (hT.shTot j hj (wtA w) w.n (dom_wtA w) Λ N x P hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 hf.1 hG.2.2.2.2).1
  have hd := hT.dLev j hj w.n
  obtain ⟨-, h1, h2⟩ := hf
  obtain ⟨-, h1', h2'⟩ := hf'
  generalize T.dδ j w.n = d at *
  refine GlobalTheory.ClassSumUnique.sec_eq_of_geometric h1 h1' fun k _ _ _ y => ?_
  letI : Algebra d.c₂.F k := ((algebraMap T.Q.c.F k).comp (d.eF.symm : d.c₂.F →+* T.Q.c.F)).toAlgebra
  have hk : ∀ a : T.Q.c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap T.Q.c.F k a := fun a => by
    show algebraMap T.Q.c.F k (d.eF.symm (d.eF a)) = _
    rw [AlgEquiv.symm_apply_apply]
  obtain ⟨y₂, hy⟩ := hd.2.2.2.2.2.2.1 k hk y
  obtain ⟨v, hv, e⟩ := h2 k hk y y₂ hy
  obtain ⟨v', hv', e'⟩ := h2' k hk y y₂ hy
  rw [e, e', (tot k y₂).unique hv hv']

abbrev mv (T : Top D) (j : ℕ) (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) : T.R j →ₗ[T.Q.c.F] T.R j :=
  actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_const (T : Full D) (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hw : D.R.r ≤ w.n)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) :
    ∃ u : T.Q.c.F, u ≠ 0 ∧ ∀ Λ N P x x' f f', GoodDatum T.toTop j w Λ N P → IsRightMul γ x' x →
      IsSeries T.toTop j w Λ N P x f → IsSeries T.toTop j w Λ N P x' f' → mv T.toTop j γ f = u • f' := by
  have hC := GlobalTheory.chartIndependence_unconditional
  have hL := GlobalTheory.firstFiveLaws.1
  have hpq := rank_eq hT.p.pins hj
  have hA : T.Q.l.A = 1 := hT.p.pins.2.1.2
  have hAct := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j hpq hA
  have hLev := hT.sh.dLev j hj w.n
  have hA₂ := hT.lvA j hj w.n
  obtain ⟨inst, hnab⟩ := hT.sh.dNab j hj w.n
  obtain ⟨ph, ψ, x₀, -, hpin, htie⟩ := hT.sh.dPhi j hj w.n hw
  have hTot := hT.sh.shTot j hj (wtA w) w.n (dom_wtA w)
  obtain ⟨g, hν, hγ, hg⟩ := GlobalTheory.T.exists_completed_isometry_inducing_half_level_automorphism _ _ (T.Q.Dw j) T.Q.l γ
  obtain ⟨ρ₂, hρ₂⟩ := GlobalTheory.LevelActionLaws.exists_levAut hpq (T.dδ j w.n).Xo₂ g (by rw [hν, sub_self]; exact dvd_zero _)
  obtain ⟨u, hu, hcd⟩ := exists_root T hT hj hxi hw g hν ρ₂ hρ₂
  refine ⟨u, hu, fun Λ N P x0 x0' f f' hG hx hf hf' => ?_⟩
  suffices key : IsSeries T.toTop j w Λ N P x0' ((u : T.Q.c.F)⁻¹ • mv T.toTop j γ f) by
    rw [← key.unique hT.sh hj hG hf', smul_inv_smul₀ hu]
  obtain ⟨hX, hsec, hR⟩ := hf
  obtain ⟨hU, hb, hb₂, hO, hP⟩ := hG
  refine ⟨hf'.1, Submodule.smul_mem _ _ (actL_mem _ _ _ _ hAct.total hAct.nat hAct.bor _ γ hsec), ?_⟩
  clear hf'
  generalize T.dδ j w.n = d at *
  have hM := hLev.2.1
  have hM₁ : 0 < T.Q.l.M := by have := T.Q.l.three_le; omega
  have hpd : 0 < d.pd := Nat.pos_of_mul_pos_left (hM ▸ (by have := d.l₂.three_le; omega : 0 < d.l₂.M))
  have hI : ∀ a, g.f d.l₂.M a - a ∈ d.I • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have hpI : ((d.pd : ℕ) : 𝓞 D.host.E) ∈ d.I := by
      refine (Ideal.mul_le_inf.trans inf_le_left : d.I * d.I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ d.I) ?_
      rw [GlobalTheory.DatumInverseCharacter.half_prod hM hLev.2.2.2.1]
      exact Ideal.mem_span_singleton_self _
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (g.tower d.pd T.Q.l.M hpd hM₁ a)
    have h2 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ hpI (hg d.pd hpd hLev.2.2.1 a)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, mul_comm, ← hM] at this
  have hγ' : ∀ a, g.f d.l₂.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) := fun a => by
    have h1 := GlobalTheory.DatumInverseCharacter.mem_of_modN _ (natCast_mem_half T.Q.l).1 (g.tower T.Q.l.M d.pd hM₁ hpd a)
    have h2 : g.f T.Q.l.M a - liftLa γ a ∈ T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (T.Q.Dw j).La) :=
      (Submodule.Quotient.eq _).1 ((hγ a).trans (liftLa_spec γ a).symm)
    have := add_mem h1 h2
    rwa [sub_add_sub_cancel, ← hM] at this
  obtain ⟨σq, hσ, -⟩ := GlobalTheory.T.levelCoverDatum_similitude_adjoint_transport _ _ _ _ _ _ _ d hM hLev.2.2.2.1 ph ψ x₀ hpin g hI
  have hw' := datum_move d hM hLev.2.2.2.1 hpin _ hI hγ' σq hσ hx
  obtain ⟨hρs, ν₂, hη, hηA⟩ := hρ₂
  have hmv₂ : IsLevMove ρ₂.hom ν₂ (g.f d.l₂.M) (g.f d.l₂.A) := ⟨hρs, hη, hηA⟩
  have hP₂ := (GlobalTheory.admissible_columns_le_and_harmonic_map_cover _ _ _ _ _ _ _ d).2 _ P hP.1
  intro k _ _ _ _ hk y y₂ ho
  have hev := evalAt_actL hAct (hT.p.evalWD j hj) frMap_trans_id γ hsec.1 y
  obtain ⟨ρ, ν, -, hmv, hfr⟩ := mvPt_spec hAct.total γ y
  generalize mvPt _ _ γ y = y' at hev hfr
  obtain ⟨y₂', hfr₂⟩ := (GlobalTheory.exists_unique_frMove _ _ _ _ d.Xo₂ d.c₂ ρ₂.hom ν₂ hρs k y₂).1
  obtain ⟨r', m', hr', hm', hE'⟩ := GlobalTheory.T.exists_conj_levelMap_by_levelMoves _ _ _ _ _ _ _ d hLev.2.2.2.2.2.1 ρ ν ρ₂ ν₂ _ _ _ _ hmv hmv₂ hγ'
    (fun a => ⟨_, by rw [hA, one_smul]⟩)
  have ho' := GlobalTheory.T.liesOverFramed_of_square_levelMoves _ _ _ _ _ _ _ d ρ ν ρ₂.hom ν₂ r' m' hr' hm' k y y' y₂ y₂' ho hfr hfr₂
  obtain ⟨z₂, hz₂⟩ := hLev.2.2.2.2.2.2.1 k hk y'
  obtain ⟨v, hv, hfv⟩ := hR k hk y' z₂ hz₂
  obtain ⟨v', hv', -⟩ := (hTot Λ N x0 P hU hb hb₂ hO hX hP).1 k y₂'
  have e₁ := GlobalTheory.ShortLiftInvariance.cover_product_indep_of_lift hL hC _ _ _ _ _ _ _ d
    (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 _ _ _ hpq).1 hLev (hA₂.trans hA.symm) hnab ⟨ph, ψ, x₀, hpin, htie⟩ Λ N hU hb₂ hO _ _ hP₂ x0 _
    r' m' hE' k hk y' z₂ y₂' hz₂ ho' v v' hv hv'
  have e₂ := GlobalTheory.T.shortThetaValue_under_levelMove hL hC _ _ _ _ d.Xo₂ d.c₂ d.nab₂ hnab k ρ₂.hom ν₂ _ _ y₂ y₂' hmv₂ hfr₂ σq hσ
    _ _ _ hP₂ (d.w x0) Λ _ N v' hv'
  rw [funext hw'] at e₂
  refine ⟨v', e₂, (evalAt_smul _ _ _ _ y).trans ?_⟩
  refine (congrArg (_ * ·) (hev.trans (hfv.trans e₁))).trans ?_
  rw [hcd k y₂ y₂' hfr₂.1, hk, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu, map_one, one_mul]

theorem not_three_dvd_level {T : Top D} (h : LawsP T) : ¬ 3 ∣ T.Q.l.M := by
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have key : ∀ k, ¬ 3 ∣ D.host.g k := fun k hk => by
    have hc := D.ntypes.g_cond k
    have h4 : D.host.g k % 4 = 1 := by
      rw [← Nat.mod_mod_of_dvd (D.host.g k)
        (show 4 ∣ D.host.QS * D.host.q * D.host.d from ((((pow_dvd_pow 2 (Nat.le_add_left 2 _)).trans D.host.tower_dvd).mul_right _).mul_right _)), hc]
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (D.host.g_prime k)).1 hk
    omega
  rw [hM, Nat.prime_three.dvd_mul]
  exact fun h => h.elim (key 0) (key 1)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem mv_series (T : Full D) (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hw : D.R.r ≤ w.n)
    {γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l} (hγ : DetOne γ) {Λ N P x x' f f'}
    (hG : GoodDatum T.toTop j w Λ N P) (hx : IsRightMul γ x' x) (hf : IsSeries T.toTop j w Λ N P x f)
    (hf' : IsSeries T.toTop j w Λ N P x' f') : mv T.toTop j γ f = f' := by
  choose u hu0 hu using exists_const (w := w) T hT hj hxi hw
  rw [hu γ _ _ _ _ _ _ _ hG hx hf hf']
  by_cases h0 : f' = 0
  · rw [h0, smul_zero]
  have hAct := GlobalTheory.T.actLev_full_level_group_framedPoints D T.Q j (rank_eq hT.p.pins hj) hT.p.pins.2.1.2
  have hmul : ∀ a b, u (a * b) = u a * u b := fun a b => by
    obtain ⟨x₁, r₁, a₁⟩ := exists_rightMul a hf'.1
    obtain ⟨x₂, r₂, a₂⟩ := exists_rightMul b a₁
    obtain ⟨f₁, s₁⟩ := exists_isSeries hT.sh hj hG a₁
    obtain ⟨f₂, s₂⟩ := exists_isSeries hT.sh hj hG a₂
    have e : mv T.toTop j (a * b) f₂ = mv T.toTop j a (mv T.toTop j b f₂) :=
      actL_mul _ _ _ hAct.total hAct.func hAct.mul a b s₂.2.1.1
    rw [hu _ _ _ _ _ _ _ _ hG (r₁.mul r₂) s₂ hf', hu _ _ _ _ _ _ _ _ hG r₂ s₂ s₁, map_smul,
      hu _ _ _ _ _ _ _ _ hG r₁ s₁ hf', smul_smul, mul_comm] at e
    exact smul_left_injective _ h0 e
  have h1 := char_eq_one_of_detOne (not_three_dvd_level hT.p)
    (MonoidHom.mk' (fun a => Units.mk0 (u a) (hu0 a)) fun a b => Units.ext (hmul a b)) hγ
  rw [show u γ = 1 from congrArg Units.val h1, one_smul]

end Move

end GlobalTheory.TraceLattice
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct Matrix nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem det_baseChange_lift {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (γ : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M))) (f : M →ₗ[R] M)
    (hf : ∀ v, (I • (⊤ : Submodule R M)).mkQ (f v) = γ ((I • (⊤ : Submodule R M)).mkQ v)) :
    LinearMap.det (LinearMap.baseChange (R ⧸ I) f) =
      ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective) : (R ⧸ I)ˣ) : R ⧸ I) := by
  let e := (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective (S := R ⧸ I) Ideal.Quotient.mk_surjective
  rw [LinearEquiv.coe_det, ← LinearMap.det_conj _ e]
  congr 1
  refine LinearMap.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change TensorProduct.quotTensorEquivQuotSMul M I (LinearMap.baseChange (R ⧸ I) f
    ((TensorProduct.quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk a))) = γ _
  rw [TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearMap.baseChange_tmul,
    ← TensorProduct.quotTensorEquivQuotSMul_symm_mk, LinearEquiv.apply_symm_apply]
  exact hf a

section General

open GlobalTheory.AdLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def swapF : RA F E →+* E ⊗[F] Formalism.L2.Herm.Af F :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toAlgHom.toRingHom

theorem exists_res_eq_zero {I : Ideal (𝓞 E)} {PP : Pl E} (hI : I ≤ PP.asIdeal) {x : RA F E}
    (hx : x ∈ hat1 F ((I : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ t : Formalism.L2.Herm.intAf F E, t.1 = swapF F E x ∧ resS F PP t = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    refine ⟨oToS F E b * ⟨(1 : E) ⊗ₜ a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩, ?_, ?_⟩
    · change ((b : E) ⊗ₜ 1) * ((1 : E) ⊗ₜ a) = (b : E) ⊗ₜ a
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · rw [map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 (hI hb), zero_mul]
  | zero => exact ⟨0, (RingHom.map_zero _).symm, RingHom.map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hs'⟩ := hx
    obtain ⟨t, ht, ht'⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add, ← hs, ← ht]; rfl, by rw [RingHom.map_add, hs', ht', add_zero]⟩
  | neg x _ hx =>
    obtain ⟨s, hs, hs'⟩ := hx
    exact ⟨-s, by rw [RingHom.map_neg, ← hs]; rfl, by rw [RingHom.map_neg, hs', neg_zero]⟩

theorem det_eq_one_of_lift {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (Pg : Finset (Pl E)) (I J : Ideal (𝓞 E)) (hI : I ≠ ⊥) (hIJ : I ⊔ J = ⊤)
    (hPg : I = ∏ PP ∈ Pg, PP.asIdeal) {M : Type} [AddCommGroup M] [Module (𝓞 E) M] (ι : M →ₗ[𝓞 E] (Fin n → E))
    (hinj : Function.Injective ι) (hr : LinearMap.range ι = L)
    (γ : (M ⧸ I • (⊤ : Submodule (𝓞 E) M)) ≃ₗ[𝓞 E] (M ⧸ I • (⊤ : Submodule (𝓞 E) M))) (f : M →ₗ[𝓞 E] M)
    (hf : ∀ v, (I • (⊤ : Submodule (𝓞 E) M)).mkQ (f v) = γ ((I • (⊤ : Submodule (𝓞 E) M)).mkQ v))
    (k : Matrix (Fin n) (Fin n) (RA F E)) (s : Formalism.L2.Herm.intAf F E) (hs : swapF F E k.det = s.1)
    (hdet : ∀ PP ∈ Pg, resS F PP s = 1) {N : ℕ} (hN : (N : 𝓞 E) ∈ I)
    (h : ∀ a ∈ J • (⊤ : Submodule (𝓞 E) M), ∃ w ∈ hat F (L : Set (Fin n → E)),
      fv F (ι (f a)) - k.mulVec (fv F (ι a)) = N • w) :
    LinearMap.det (LinearMap.baseChange (𝓞 E ⧸ I) f) = 1 := by
  have h1 : (1 : 𝓞 E) ∈ I ⊔ J := by rw [hIJ]; trivial
  obtain ⟨m, hm, c, hc, hmc⟩ := Submodule.mem_sup.1 h1
  obtain ⟨u, hu⟩ := Ideal.Quotient.mk_surjective ((LinearEquiv.det (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ I)
    Ideal.Quotient.mk_surjective) : (𝓞 E ⧸ I)ˣ) : 𝓞 E ⧸ I)
  let ρ : 𝓞 E →+* RA F E :=
    (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)).toRingHom.comp (algebraMap (𝓞 E) E)
  have hfv : ∀ (b : 𝓞 E) a, fv F (ι (b • a)) = ρ b • fv F (ι a) := fun b a => by
    funext i
    rw [map_smul]
    change (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((b : E) * ι a i) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ι a i)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have key := GlobalTheory.LevDet.det_sub_mem_completedIdeal_of_level F L hfg hsp I hI ι hinj hr γ f hf (ρ c • k) (fun a => by
      obtain ⟨w, hw, e⟩ := h (c • a) (Submodule.smul_mem_smul hc trivial)
      have hfa : fv F (ι (f a)) ∈ hat F (L : Set (Fin n → E)) :=
        AddSubgroup.subset_closure ⟨1, fun v => one_mem _, _, hr ▸ LinearMap.mem_range_self ι _, rfl⟩
      rw [map_smul, hfv, hfv, Matrix.mulVec_smul, ← Nat.cast_smul_eq_nsmul (RA F E), ← map_natCast ρ] at e
      have e' : (ρ c • k) *ᵥ fv F (ι a) - fv F (ι (f a)) = -(ρ m • fv F (ι (f a))) - ρ (N : 𝓞 E) • w := by
        have : ρ m = 1 - ρ c := by rw [← map_one ρ, ← hmc, map_add, add_sub_cancel_right]
        rw [← e, this, Matrix.smul_mulVec, sub_smul, one_smul]
        abel
      rw [e']
      exact sub_mem (neg_mem (AddSubgroup.subset_closure ⟨m, hm, _, hfa, rfl⟩))
        (AddSubgroup.subset_closure ⟨_, hN, w, hw, rfl⟩)) u hu
  rw [det_baseChange_lift I γ _ hf, ← hu, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq, hPg,
    Ideal.prod_eq_iInf_of_pairwise_isCoprime fun a _ b _ hab => HeightOneSpectrum.isCoprime_of_ne _ _ hab]
  refine Ideal.mem_iInf.2 fun PP => Ideal.mem_iInf.2 fun hP => ?_
  have hle : I ≤ PP.asIdeal := hPg ▸ Ideal.prod_le_inf.trans (Finset.inf_le hP)
  obtain ⟨t, ht, ht0⟩ := exists_res_eq_zero hle key
  have hρ : ∀ b, swapF F E (ρ b) = (oToS F E b).1 := fun _ => rfl
  have e : t = oToS F E c ^ n * s - oToS F E u := by
    apply Subtype.ext
    rw [ht, Matrix.det_smul, RingHom.map_sub, RingHom.map_mul, RingHom.map_pow, hρ, hs, Fintype.card_fin]
    rfl
  have h4 : Ideal.Quotient.mk PP.asIdeal c = 1 := by
    rw [← map_one (Ideal.Quotient.mk PP.asIdeal), ← hmc, map_add, Ideal.Quotient.eq_zero_iff_mem.2 (hle hm), zero_add]
  rw [e, RingHom.map_sub, RingHom.map_mul, RingHom.map_pow, resS_oToS, resS_oToS, hdet PP hP, h4, one_pow, one_mul,
    sub_eq_zero] at ht0
  rw [← Ideal.Quotient.eq, ← ht0, map_one]

theorem exists_det_of_mem_St {n : ℕ} (k : Matrix (Fin n) (Fin n) (RA F E)) {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hk : x.1 = (swapF F E).mapMatrix k) (hx : x ∈ St β) : ∃ s : Formalism.L2.Herm.intAf F E, swapF F E k.det = s.1 ∧
      ∀ PP, resS F PP s = ((redFn β PP x : GL _ _) : Matrix (Fin n) (Fin n) (kP PP)).det := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y.1.det, ?_, fun PP => ?_⟩
  · have e2 : (y.1.det).1 = (intGL F E _ y).1.det := RingHom.map_det (Formalism.L2.Herm.intAf F E).subtype _
    rw [RingHom.map_det, ← hk, e2]
    exact Matrix.det_units_conj β _
  · rw [redFn_frGL]
    exact RingHom.map_det _ _

end General

variable {D : D7}

theorem detOne_of_lift (V : HSp D) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) (γ : LaMod Dw l ≃ₗ[𝓞 D.host.E] LaMod Dw l)
    (κ : GA D V) (β : GL (Fin V.rank) (EAf D)) (hκ : finE V κ ∈ St β) (Pg : Finset (Pl D.host.E))
    (hPg : l.Mb = ∏ PP ∈ Pg, PP.asIdeal)
    (hdet : ∀ PP ∈ Pg, ((redFn β PP (finE V κ) : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)).det = 1)
    (h : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat V 1,
      finVec V (ι (liftLa γ a)) - (finHom V κ).1.mulVec (finVec V (ι a)) = l.M • w) : DetOne γ := by
  obtain ⟨hfg, hsp, -, -, hhat, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  have hI : l.Mb ≠ ⊥ := fun h0 => by
    have h1 := (natCast_mem_half l).1
    rw [h0, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    have := l.three_le
    omega
  rw [hhat] at h
  obtain ⟨s, hs, hs'⟩ := exists_det_of_mem_St (F := D.host.F) (finHom V κ).1 rfl hκ
  exact det_eq_one_of_lift (latG V 1) hfg hsp Pg l.Mb (Mfr l) hI l.coprime hPg ι hι.1 hι.2 γ _ (liftLa_spec γ)
    (finHom V κ).1 s hs (fun PP hP => (hs' PP).trans (hdet PP hP)) (natCast_mem_half l).1 h

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem latEmb_iotaW {T : Full D} (hT : LawsFull T) (ι : Fin D.R.m) : LatEmb (Wc D ι) (iotaW T.J ι) := by
  obtain ⟨hr, _, _, _, _, _, _, hL, -⟩ := hT.j.adPin _ (inR_succ ι) T.σ₀ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (_ : V = Wc D ι) (hr : V.rank = D.R.r),
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((ι : ℕ) + 1)) →
      LatEmb (Wc D ι) (iotaW T.J ι) := by
    rintro _ rfl _ h
    exact h
  exact key _ (hT.p.spaceW _ (inR_succ ι) _ T.toCore.good_σ₀) hr hL

theorem detOne_of_levelPin {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} (hT : LawsFull T)
    {ι : Fin D.R.m} {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    (hℓ : LevelPin R ι ℓ) (hPg : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal) {g : G}
    (hg : ∀ PP : R.Pg, ((R.eG g PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) : DetOne (ℓ g) := by
  obtain ⟨κ, ⟨-, hκ, hr⟩, h⟩ := hℓ g
  refine detOne_of_lift (Wc D ι) _ (latEmb_iotaW hT ι) _ κ (R.βW ι) (parLev_St hκ) R.Pg hPg (fun PP hP => ?_) h
  have e : upperLeftBlock (r_le_rank_Wc ι) (redFn (R.βW ι) PP (finE (Wc D ι) κ)) = R.eG g ⟨PP, hP⟩ := congrFun hr ⟨PP, hP⟩
  have hb : redFn (R.βW ι) PP (finE (Wc D ι) κ) ∈ blockTri (blk2 D.R.r) := fun i j hij => by
    have hi : i.val < D.R.r := (rank_Wc ι) ▸ i.2
    have hj : j.val < D.R.r := (rank_Wc ι) ▸ j.2
    simp [blk2, hi, hj] at hij
  rw [← hg ⟨PP, hP⟩, ← e, upper_block_val_submatrix _ hb]
  exact (Matrix.det_submatrix_equiv_self (finCongr (rank_Wc ι).symm) _).symm

end GlobalTheory.TraceLattice
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Trace

variable {K Z P : Type} [Field K] [NumberField K] [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
  [IsScalarTower (𝓞 K) K Z] [Group P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U] (ψ : P → 𝓞 K)

def trace : Z →ₗ[K] Z := ∑ u : U, ((ψ (u : P) : 𝓞 K) : K) • ρ (u : P)⁻¹

theorem trace_apply (y : Z) : trace ρ U ψ y = ∑ u : U, ψ (u : P) • ρ (u : P)⁻¹ y := by
  simp only [trace, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun u _ => algebraMap_smul K _ _

variable {ρ U ψ}

theorem mem_eig_iff {y : Z} : y ∈ eig ρ U ψ ↔ ∀ u : U, ρ (u : P) y = ((ψ (u : P) : 𝓞 K) : K) • y := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem trace_mem_eig (hψ : ∀ a ∈ U, ∀ b ∈ U, ψ (a * b) = ψ a * ψ b) (y : Z) : trace ρ U ψ y ∈ eig ρ U ψ := by
  refine mem_eig_iff.2 fun a => ?_
  simp only [trace, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight a) _ _ fun u => ?_).symm
  have e : ρ (a : P) (ρ ((u : P) * a)⁻¹ y) = ρ (u : P)⁻¹ y := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, mul_inv_cancel_left]
  rw [Equiv.coe_mulRight, Subgroup.coe_mul, e, hψ _ u.2 _ a.2, smul_smul, mul_comm (ψ u)]
  exact congrArg (· • _) (map_mul (algebraMap (𝓞 K) K) _ _).symm

theorem trace_of_mem_eig (h1 : ψ 1 = 1) (hψ : ∀ a ∈ U, ∀ b ∈ U, ψ (a * b) = ψ a * ψ b) {y : Z} (hy : y ∈ eig ρ U ψ) :
    trace ρ U ψ y = ((Nat.card U : ℕ) : K) • y := by
  simp only [trace, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_congr rfl (g := fun _ => y) fun u _ => ?_, Finset.sum_const, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul,
    Finset.card_univ]
  have e : ((ψ (u : P) : 𝓞 K) : K) * ((ψ (u : P)⁻¹ : 𝓞 K) : K) = 1 := by
    have := hψ _ u.2 _ (U.inv_mem u.2)
    rw [mul_inv_cancel, h1] at this
    exact_mod_cast congrArg (fun a : 𝓞 K => (a : K)) this.symm
  have := mem_eig_iff.1 hy u⁻¹
  rw [Subgroup.coe_inv] at this
  rw [this, smul_smul, e, one_smul]

end Trace

variable {D : D7}

def ShortSpanFG {B : WeightFamilies.Prov D} {P6 : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P6 j) (w : WeightFamilies.Wt D j) : Prop :=
  (X.shortTh w).FG

section Coord

variable {F K : Type} [Field F] [Field K] [NumberField K] [Algebra F K] {n : ℕ}

theorem sum_eq_trace {C : Type} [AddCommGroup C] [Module F C] {z : (Fin n → K) ≃ₗ[K] K ⊗[F] C} {P : Type} [Group P]
    {ρ : Representation K P (Fin n → K)} {U : Subgroup P} [Fintype U] (ψ : P → 𝓞 K) {act : P → C → C}
    (hρ : ∀ g y, ρ g (z.symm (1 ⊗ₜ y)) = z.symm (1 ⊗ₜ act g y)) {f : U → C} {y : C} (hf : ∀ u : U, act u (f u) = y) :
    ∑ᶠ u : U, ψ (u : P) • z.symm (1 ⊗ₜ[F] f u) = trace ρ U ψ (z.symm (1 ⊗ₜ y)) := by
  rw [finsum_eq_sum_of_fintype, trace_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← hf u, ← hρ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem spanK_comap_span_le {R : Type} [AddCommGroup R] [Module F R] [Module (𝓞 F) R] [IsScalarTower (𝓞 F) F R]
    (C : Submodule F R) (z : (Fin n → K) ≃ₗ[K] K ⊗[F] C) {s : Set R} (hs : ∀ f ∈ s, f ∈ C)
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : ∀ y : C, y.1 ∈ s → z.symm (1 ⊗ₜ y) ∈ M) :
    spanK z {y : C | y.1 ∈ Submodule.span (𝓞 F) s} ≤ M := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨f, hf⟩, hF, rfl⟩
  change f ∈ Submodule.span (𝓞 F) s at hF
  suffices key : ∃ hf : f ∈ C, z.symm (1 ⊗ₜ (⟨f, hf⟩ : C)) ∈ M from key.2
  clear hf
  induction hF using Submodule.span_induction with
  | mem x hx => exact ⟨hs x hx, hM ⟨x, hs x hx⟩ hx⟩
  | zero =>
    refine ⟨zero_mem _, ?_⟩
    change z.symm (1 ⊗ₜ (0 : C)) ∈ _
    rw [TensorProduct.tmul_zero, map_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    obtain ⟨a, hx⟩ := hx
    obtain ⟨b, hy⟩ := hy
    refine ⟨add_mem a b, ?_⟩
    have := add_mem hx hy
    rwa [← map_add, ← TensorProduct.tmul_add] at this
  | smul r x _ hx =>
    obtain ⟨a, hx⟩ := hx
    have e : r • x = (r : F) • x := (algebraMap_smul F r x).symm
    refine ⟨e ▸ C.smul_mem _ a, ?_⟩
    have e1 : (⟨r • x, e ▸ C.smul_mem _ a⟩ : C) = (r : F) • (⟨x, a⟩ : C) := Subtype.ext e
    rw [e1, TensorProduct.tmul_smul, ← algebraMap_smul K (r : F), map_smul]
    exact M.smul_mem (algebraMap (𝓞 F) (𝓞 K) r) hx

theorem sum_eq_trace_cusp {B : WeightFamilies.Prov D} {j : ℕ} {w : WeightFamilies.Wt D j} [Algebra B.KO K]
    {z : (Fin n → K) ≃ₗ[K] K ⊗[B.KO] B.Cusp j w} {P : Type} [Group P]
    {ρ : Representation K P (Fin n → K)} {U : Subgroup P} [Fintype U] (ψ : P → 𝓞 K) {act : P → B.Cusp j w → B.Cusp j w}
    (hρ : ∀ g y, ρ g (z.symm (1 ⊗ₜ y)) = z.symm (1 ⊗ₜ act g y)) {f : U → B.Cusp j w} {y : B.Cusp j w}
    (hf : ∀ u : U, act u (f u) = y) :
    ∑ᶠ u : U, ψ (u : P) • z.symm (1 ⊗ₜ[B.KO] f u) = trace ρ U ψ (z.symm (1 ⊗ₜ y)) := sum_eq_trace ψ hρ hf

theorem spanK_spanIn_le [NumberField F] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra F (R j)] [∀ j, Algebra (𝓞 F) (R j)]
    [∀ j, IsScalarTower (𝓞 F) F (R j)] (C : ∀ j, WeightFamilies.Wt D j → Submodule F (R j)) (j : ℕ) (w : WeightFamilies.Wt D j)
    (z : (Fin n → K) ≃ₗ[K] K ⊗[F] cutR C j w) {s : Set (R j)} (hs : ∀ f ∈ s, f ∈ cutR C j w)
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : ∀ y : cutR C j w, y.1 ∈ s → z.symm (1 ⊗ₜ y) ∈ M) :
    spanK z (spanIn C j w s : Set (cutR C j w)) ≤ M := spanK_comap_span_le _ z hs hM


end Coord

section Forms

variable {T : Full D} {h : LawsP T.toTop} {j : ℕ} {w : WeightFamilies.Wt D j} {K : Type} [Field K] [NumberField K]
  [Algebra (recB h.toLawsCore).KO K] {n : ℕ}
  {z : (Fin n → K) ≃ₗ[K] K ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp j w} {P : Type} [Group P]
  {ρ : Representation K P (Fin n → K)} {U : Subgroup P} [Fintype U] {ψ : P → 𝓞 K}
  {ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)}
  {act : P → (recB h.toLawsCore).Cusp j w → (recB h.toLawsCore).Cusp j w}

theorem thetaEig_le_eig (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hn : w.n = D.R.nV)
    (hρ : ∀ g F, ρ g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)) (hact : IsLevAct T.toTop h j w ℓ act)
    (hdet : ∀ u ∈ U, DetOne (ℓ u)) (hψ : ∀ a ∈ U, ∀ b ∈ U, ψ (a * b) = ψ a * ψ b) :
    thetaEig h j w z U ψ ℓ ≤ (eig ρ U ψ).restrictScalars (𝓞 K) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨Λ, N, x₀, Q, x, h1, h2, h3, h4, h5, h6, h7⟩, rfl⟩
  have hG : GoodDatum T.toTop j w Λ N Q := ⟨h1, h2, h3, h4, h6⟩
  obtain ⟨f₀, s₀⟩ := exists_isSeries hT.sh hj hG (x := x₀) (by simpa [hn] using h5)
  have key : ∀ u : U, ((act u (f u)).1 : T.R j) = f₀ := fun u => (hact _ _).trans
    (mv_series T hT hj hxi (hn ▸ Nat.le_add_right _ _) (hdet _ u.2) hG (h7 u).1
      ⟨by simpa [hn] using (h7 u).2.1, (cutR_le T.C _ _ (f u).2).1, (h7 u).2.2⟩ s₀)
  have e := sum_eq_trace_cusp ψ hρ (f := f) (y := act (1 : U) (f 1)) fun u => Subtype.ext ((key u).trans (key 1).symm)
  exact (congrArg (· ∈ eig ρ U ψ) e).mpr (trace_mem_eig hψ _)

theorem trace_gen_mem (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hn : w.n = D.R.nV)
    (hρ : ∀ g F, ρ g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)) (hact : IsLevAct T.toTop h j w ℓ act)
    (hdet : ∀ u ∈ U, DetOne (ℓ u)) (hc : ∀ f ∈ T.toTop.sh j w, f ∈ cutR T.C j w)
    (F : (recB h.toLawsCore).Cusp j w) (hF : (F.1 : T.R j) ∈ T.toTop.sh j w) :
    trace ρ U ψ (z.symm (1 ⊗ₜ F)) ∈ thetaEig h j w z U ψ ℓ := by
  obtain ⟨hs, Λ, N, x₀, Q, h1, h2, h3, h4, h5, h6, h7⟩ := hF
  have hG : GoodDatum T.toTop j w Λ N Q := ⟨h1, h2, h3, h4, h6⟩
  choose x hx ax using fun u : U => exists_rightMul (ℓ u) h5
  choose f hf using fun u : U => exists_isSeries hT.sh hj hG (ax u)
  let f' : U → (recB h.toLawsCore).Cusp j w := fun u => ⟨f u, hc _ ((hf u).mem_sh hG)⟩
  rw [← sum_eq_trace_cusp ψ hρ (f := f') fun u => Subtype.ext ((hact _ _).trans
    (mv_series T hT hj hxi (hn ▸ Nat.le_add_right _ _) (hdet _ u.2) hG (hx u) (hf u) ⟨h5, hs, h7⟩))]
  exact Submodule.subset_span ⟨f', ⟨Λ, N, x₀, Q, x, h1, h2, h3, h4, by simpa [hn] using h5, h6,
    fun u => ⟨hx u, by simpa [hn] using ax u, (hf u).2.2⟩⟩, rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem trace_mem_thetaEig (hT : LawsFull T) (hj : InR D j) (hxi : TwistTrivialOnRational T j) (hn : w.n = D.R.nV)
    (hl : w.LastPos) (hρ : ∀ g F, ρ g (z.symm (1 ⊗ₜ F)) = z.symm (1 ⊗ₜ act g F)) (hact : IsLevAct T.toTop h j w ℓ act)
    (hdet : ∀ u ∈ U, DetOne (ℓ u)) {y : Fin n → K} (hy : y ∈ spanK z ((recPJ h j hj).shortTh w : Set _)) :
    trace ρ U ψ y ∈ thetaEig h j w z U ψ ℓ := by
  have hl' := ((GlobalTheory.WeightOnDatum.weight_on_datum D T.toCore h.pins j hj w).2.2.1 hl).1
  have hc : ∀ f ∈ T.toTop.sh j w, f ∈ cutR T.C j w := fun f hf => by
    rw [cutR_eq T.C hj]
    exact hT.sh.shCusp j hj _ _ (dom_wtA w) hl' (dom_wtA w) hl' hf
  letI : Algebra T.Q.c.F K := ‹Algebra (recB h.toLawsCore).KO K›
  exact spanK_spanIn_le T.C j w z hc
    (M := (thetaEig h j w z U ψ ℓ).comap ((trace ρ U ψ).restrictScalars (𝓞 K)))
    (fun F hF => trace_gen_mem hT hj hxi hn hρ hact hdet hc F hF) hy

end Forms

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

def DetOneOn {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (U : Subgroup G)
    (ℓ : G → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)) : Prop :=
  ∀ u ∈ U, DetOne (ℓ u)

theorem clauses_of_onTie {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
    {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}
    (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hT : LawsFull T)
    (hxi : TwistTrivialOnRational T ((ι : ℕ) + 1)) (hn : (κ ι).n = D.R.nV) (hl : (κ ι).LastPos) (hdet : DetOneOn U ℓ)
    (hfg : (O.ThK v i).FG) :
    (O.Th0 v i).FG ∧ O.Th0 v i ≤ (eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
      sc ((Nat.card O.U : ℕ) : D.what₂.LL) (cut (eig (O.ρ i) O.U O.ψ) (O.ThK v i)) ≤ O.Th0 v i := by
  haveI := Fintype.ofFinite O.U
  have hU : ∀ u ∈ O.U, inc u ∈ U := fun u hu => by rwa [t.U_eq] at hu
  have h1 : O.ψ 1 = 1 := RingOfIntegers.ext ((t.ψ_eq 1 (hU 1 (one_mem _))).trans (by
    rw [show (⟨inc 1, hU 1 (one_mem _)⟩ : U) = 1 from Subtype.ext (map_one inc), map_one]; rfl))
  have hψ : ∀ a ∈ O.U, ∀ b ∈ O.U, O.ψ (a * b) = O.ψ a * O.ψ b := fun a ha b hb =>
    RingOfIntegers.ext ((t.ψ_eq _ (hU _ (mul_mem ha hb))).trans (by
      rw [show (⟨inc (a * b), hU _ (mul_mem ha hb)⟩ : U) = ⟨inc a, hU a ha⟩ * ⟨inc b, hU b hb⟩ from
        Subtype.ext (map_mul inc a b), map_mul, Units.val_mul, ← t.ψ_eq a, ← t.ψ_eq b]
      exact (map_mul (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) _ _).symm))
  have hd : ∀ u ∈ O.U, DetOne (ℓ (inc u)) := fun u hu => hdet _ (hU u hu)
  refine ⟨hfg.of_le (t.Th0_le_ThK hn), ?_, ?_⟩
  · rw [t.Th0_eq]
    exact thetaEig_le_eig hT (inR_succ ι) hxi hn t.rho_eq t.act_eq hd hψ
  · rintro _ ⟨x, ⟨hx, he⟩, rfl⟩
    rw [t.ThK_eq] at hx
    rw [t.Th0_eq]
    have := trace_mem_thetaEig (ψ := O.ψ) hT (inR_succ ι) hxi hn hl t.rho_eq t.act_eq hd hx
    rwa [trace_of_mem_eig h1 hψ he] at this

variable (A) in

def TiedAt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (O : OnObj S P oc) (inc : P →* G) (U : Subgroup G)
    (ψ : U →* D.what₂.LLˣ)
    (Q : ∀ (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ), WeightAlgebra.PJ D B P6 j → ℕ → (ka wL wF : WeightFamilies.Wt D j) → ℕ → Prop)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J) : Prop :=
  ∃ (T : Full D) (_ : Algebra T.J.Q.c.F D.what₂.LL) (R : RealDat D A T.J.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (p : ℕ) (ι : Fin D.R.m) (wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)) (nT : ℕ),
    ∃ z act ℓ ph y, OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y ∧ LawsFull T ∧
      TwistTrivialOnRational T ((ι : ℕ) + 1) ∧ (κ ι).n = D.R.nV ∧ (κ ι).LastPos ∧ DetOneOn U ℓ ∧
      Q _ _ _ (recPJ h ((ι : ℕ) + 1) (inR_succ ι)) p (κ ι) wL wF nT

variable {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {O : OnObj S P oc} {inc : P →* G} {U : Subgroup G}
  {ψ : U →* D.what₂.LLˣ}


theorem leafData_of_onTie_of_leafSpan (hS : LeafSpan O)
    (H : AtPair S fun v => ∀ i, TiedAt A hinj EX O inc U ψ (fun _ _ _ _ _ _ _ _ _ => True) v i) : LeafData O := by
  have key : ∀ v i, TiedAt A hinj EX O inc U ψ (fun _ _ _ _ _ _ _ _ _ => True) v i → (O.ThK v i).FG →
      (O.Th0 v i).FG ∧ O.Th0 v i ≤ (eig (O.ρ i) O.U O.ψ).restrictScalars (𝓞 D.what₂.LL) ∧
        sc ((Nat.card O.U : ℕ) : D.what₂.LL) (cut (eig (O.ρ i) O.U O.ψ) (O.ThK v i)) ≤ O.Th0 v i := by
    rintro v i ⟨T, _, R, κ, v₀, h, fw, p, ι, wL, wF, nT, z, act, ℓ, ph, y, t, hT, hxi, hn, hl, hdet, -⟩ hfg
    exact clauses_of_onTie t hT hxi hn hl hdet hfg
  exact fun w hw => ⟨fun i => key w i ((H w hw).1 i) ((hS w hw).1 i).2.1,
    fun i => key _ i ((H w hw).2 i) ((hS w hw).2 i).2.1⟩


end Main

section Pins

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section One

variable {T : Full D} [Algebra T.J.Q.c.F D.what₂.LL]

def HalfPin (R : RealDat D A T.J.Q.c.F) : Prop := T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal

def UnipPin (R : RealDat D A T.J.Q.c.F) (U : Subgroup G) : Prop :=
  ∀ g, g ∈ U ↔ ∀ PP : R.Pg, R.eG g PP ∈ unip (kP PP.1) D.R.r

variable {R : RealDat D A T.J.Q.c.F} {ι : Fin D.R.m}

theorem detOneOn_of_pins (hT : LawsFull T)
    {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)}
    (hℓ : LevelPin R ι ℓ) (hH : HalfPin R) {U : Subgroup G} (hU : UnipPin R U) : DetOneOn U ℓ := fun u hu =>
  detOne_of_levelPin hT hℓ hH fun PP => by
    rw [Matrix.det_of_upperTriangular fun _ _ h => ((hU u).1 hu PP).1 h]
    exact Finset.prod_eq_one fun a _ => ((hU u).1 hu PP).2 a

theorem twistTrivial_of_runPin (hT : LawsFull T) {n : ℕ} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ}
    (hR : RunPin R ι n v p) : TwistTrivialOnRational T ((ι : ℕ) + 1) := by
  obtain ⟨-, -, -, χ, hχ, hx⟩ := hR
  unfold TwistTrivialOnRational
  rw [hT.p.spaceW _ (inR_succ ι) _ T.toCore.good_σ₀]
  intro γ hγ
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D ι)).2.2.1 γ hγ
  exact Units.ext ((hx γ _ ha).trans (by rw [hχ.1.2]; rfl))

end One

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem kaR_lastPos (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) : (kaR Tp hK j).LastPos := by
  intro τ i hi
  have h1 := GlobalTheory.DepthBoundProbe.kappa_last Tp hK hj τ i hi
  have h2 : (1 : ℤ) ≤ Tp.TO := by have := Tp.TO_40; omega
  have : (1 : ℤ) ≤ ((kaR Tp hK j).aP τ i : ℤ) := by nlinarith
  exact_mod_cast this

variable {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}

variable (A) in

def PinnedAt (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D)
    (O : OnObj S P oc) (inc : P →* G) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ)
    (Q : ∀ (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ), WeightAlgebra.PJ D B P6 j → ℕ → (ka wL wF : WeightFamilies.Wt D j) → ℕ → Prop)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (i : Bs.J) : Prop :=
  ∃ (T : Full D) (_ : Algebra T.J.Q.c.F D.what₂.LL) (R : RealDat D A T.J.Q.c.F)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (p : ℕ) (ι : Fin D.R.m) (wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)) (nT : ℕ),
    ∃ z act ℓ ph y, OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y ∧ LawsFull T ∧
      κ ι = kaR Tp hK ((ι : ℕ) + 1) ∧ RunPin R ι (κ ι).n v p ∧ LevelPin R ι ℓ ∧ HalfPin R ∧ UnipPin R U ∧
      Q _ _ _ (recPJ h ((ι : ℕ) + 1) (inR_succ ι)) p (κ ι) wL wF nT

variable {Tp : ParamsT D L Pm} {hK : DV.KapDef D} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {O : OnObj S P oc}
  {inc : P →* G} {U : Subgroup G} {ψ : U →* D.what₂.LLˣ}





end Pins

end GlobalTheory.TraceLattice
end
end
