import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeanInfPosLogLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPairCoordinatesConjugateBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPointsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExistsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugatesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatioStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairUnitModulusFactor
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntertwinerSelfDualVacuumIsVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExistStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBoundMeansPosLogAreaNormalisedTheta

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.jet

theorem jet_bound_fix (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (hev : Even (a * d)) (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) (hGT : G ∈ Th D (tor0 D cc δ) L L')
    (y : VC D a d) (hy : LaQ D (tor0 D cc δ) L L' y)
    (n : D.what₂.Tau → ℕ) (B : ℝ) (hB : 1 ≤ B) (hn : ∀ τ, (n τ : ℝ) ≤ 2 * B)
    (ρ : Qbar →ₐ[ℚ] ℂ) (hρ : FixK D Qbar ρ) (T : Tup D a d n) :
    GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
    ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤
      ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 *
        (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) *
          normSq D (torConj D (tor0 D cc δ) Qbar ρ) (La D (torConj D (tor0 D cc δ) Qbar ρ) L L')
            (fnConj D Qbar ρ G) *
          (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  have hg1 : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨hdata, htors⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hg1).2 cc δ hc
  obtain ⟨hA, hAU, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hTh, -⟩ := GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
  obtain ⟨t', ht'⟩ := (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 Qbar ρ hdata.2.1 hdata.2.2
  obtain ⟨hN, -⟩ := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t' ht'
  obtain ⟨cc', δ', hc', -, hΛ⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc Qbar ρ hρ hdata.2.1 hdata.2.2 1 one_pos
  obtain ⟨π, hπ⟩ := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).2 Qbar ρ hρ hdata.1
  have hne : fnConj D Qbar ρ G ≠ 0 := by
    intro h
    rw [h, hΛ] at hN
    rw [hΛ] at ht'
    refine pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hg1 cc' δ' t' hc' ht') (hN.symm.trans ?_)
    simp [normSq]
  obtain ⟨m, hm, hmy⟩ := id hy
  obtain ⟨y', hy', -⟩ := GlobalTheory.T.galois_data_exists D cc δ hc Qbar ρ hρ hdata htors a d L L' h1 h2 y (2 * m) hy
    (by omega)
  have hgal := (GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints D cc δ hc Qbar ρ hρ hdata a d L L' h1 h2 1 (fun _ => 1) (fun _ => 0) G y y' m
    hGT hm hmy (fun _ => by simp) hy' (by rw [GlobalTheory.ConjJet.comb_one]; exact hA)
    (by rw [GlobalTheory.ConjJet.comb_one]; exact hAU y hy)).1
  rw [GlobalTheory.ConjJet.comb_one] at hgal
  have hdiff := GlobalTheory.ConjJet.U_diff D (torConj D (tor0 D cc δ) Qbar ρ) y' _ hTh.1
  obtain ⟨hmem, hcj⟩ := (GlobalTheory.ConjSeries.taylor_fnConj D a d Qbar ρ (U D (tor0 D cc δ) y G)
    (by rw [hgal]; exact hdiff) (by rw [hgal]; exact GlobalTheory.ConjJet.U_ne_zero D _ _ _ hne)).2 (hAU y hy) n T
  refine ⟨hmem, ?_⟩
  rw [hcj, hgal]
  have hr : 0 ≤ D.host.rdE := Real.rpow_nonneg (abs_nonneg _) _
  refine (GlobalTheory.MinorBound.minor_bound D a d n _ _ (area (lamConj Qbar ρ (lamOf D cc δ))) B
    (by rw [hΛ]; exact GlobalTheory.ConjJet.area_pos D hg1 cc' δ' hc') hB ?_ hn hdiff fun z => ?_).2 T
  · have := GlobalTheory.ConjJet.normSq_nonneg D (torConj D (tor0 D cc δ) Qbar ρ)
      (La D (torConj D (tor0 D cc δ) Qbar ρ) L L') (fnConj D Qbar ρ G)
    positivity
  · have := GlobalTheory.ConjJet.sup_perm D hg1 cc' δ' hc' (torConj D (tor0 D cc δ) Qbar ρ) π hΛ hπ a d L L' h1 h2 _
      hTh y' z
    rw [GlobalTheory.ConjJet.Hf_re, ← mul_div_assoc] at this
    exact this

theorem vacuum_mem_thetaSpace_pair (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ)
    (hc : Crv D cc δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) (a d : ℕ) (L L')
    (h1 : SD D L) (h2 : SD D L') (G : VC D a d → ℂ)
    (hG : ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G) : G ∈ Th D (tor0 D cc δ) L L' := by
  obtain ⟨b, κ, hb, -, rfl⟩ := hG
  obtain ⟨-, ⟨hd, hinv⟩, -⟩ := GlobalTheory.T.intertwinerUnitary_all D cc δ hc a d _ _ (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inr ⟨L, L', h1, h2, rfl⟩) _
    (GlobalTheory.VacuumMove.pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ t0 hc ht b hb.1)
  refine ⟨hd.const_mul κ, fun x hx z => ?_⟩
  have := hinv x hx z
  simp only [U] at this ⊢
  rw [show (tor0 D cc δ).abelian₂ = lamOf D cc δ from rfl, ← this]
  ring

theorem conj_jet_bound : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  intro D cc δ t0 hc ht a d L L' h1 h2 hev G hG y hy n B hB hn ρ t0' ht' T
  have hGT := vacuum_mem_thetaSpace_pair D cc δ t0 hc ht a d L L' h1 h2 G hG
  obtain ⟨hdata, -⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc
  obtain ⟨hA, -⟩ := GlobalTheory.T.thetaTaylorCoeffs_algebraic_at_complexMultiplication D cc δ hc t0 ht a d L L' h1 h2 hev G hG
  obtain ⟨hN, -⟩ := GlobalTheory.T.vacuumNorm_conj_cmPoints_all_embeddings D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA t0' ht'
  rw [← hN]
  obtain ⟨hfix | hfix, htor, hbar⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc Qbar ρ hdata
  · exact jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB hn ρ hfix T
  · obtain ⟨hmem, hle⟩ := jet_bound_fix D cc δ t0 hc ht a d L L' h1 h2 hev G hG hGT y hy n B hB
      hn (rhoBar Qbar ρ) hfix T
    refine ⟨hmem, ?_⟩
    obtain ⟨hTh, -⟩ := GlobalTheory.T.thetaVacua_conjugates_cmPoints D cc δ hc t0 ht a d L L' h1 h2 hev G hG Qbar ρ hdata hA
    have hn2 := ((hbar a d L L' (fnConj D Qbar ρ G)).2.2 hTh).2 h1 h2 0
    rw [GlobalTheory.ConjJet.U_zero] at hn2
    have hL : lamConj Qbar (rhoBar Qbar ρ) (lamOf D cc δ) =
        (lamConj Qbar ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom :=
      congrArg Tor.abelian₂ htor
    rw [GlobalTheory.ConjJet.cj_bar, (hbar a d L L' G).1, htor, hn2, hL, GlobalTheory.ConjJet.area_conj] at hle
    exact hle

end GlobalTheory.ArchFree.jet
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_jet_bound_vacuum_torsion_translate : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L', SD D L → SD D L' → Even (a * d) → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ∀ y, LaQ D (tor0 D cc δ) L L' y → ∀ (n : D.what₂.Tau → ℕ) (B : ℝ), 1 ≤ B → (∀ τ, (n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ T : Tup D a d n, GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧ ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (3 * (2 * ((fF D * a * d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * a * d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * a * d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (a * ∑ τ, n τ)) := by
  atlas_forward_decl GlobalTheory.ArchFree.jet.conj_jet_bound
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_under_adelic_pair_unit_modulus_factor : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even (N * N') → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (W : WeilO D cc δ N N' e0) (g : GA D N) (g' : GA D N') L₁ L₁', Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∃ c : ℂ, Mod1All c ∧ (W.Om g g' e0 = fun z => c * Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ L₁') e0 z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D N'), k' ∈ intG D N' → TrivAt D p (g : GL (Fin N) (AE D)) → TrivAt D p ((g' * k' : GA D N') : GL (Fin N') (AE D)) → ‖lamC lam c‖ = 1 := by
  first | exact @GlobalTheory.ArchFree.weilc.vacuum_under_adelic_pair | exact GlobalTheory.ArchFree.weilc.vacuum_under_adelic_pair | (intros; apply GlobalTheory.ArchFree.weilc.vacuum_under_adelic_pair <;> assumption)
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.NormSum.Expand
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.expand

theorem om_expand : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  intro D cc δ t0 Q hC _ P g g' L₁ L₁' hL hL'
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · exact ⟨0, 0, Fin.elim0, Fin.elim0, fun h => absurd h (by omega)⟩
  have hSD : ∀ (N : ℕ) (g : GA D N) L, Moves D (g : GL (Fin N) (AE D)) L → SD D L := by
    intro N g L hL
    obtain ⟨Lt, h1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    have : L = Lt g := by
      ext x; rw [hL x, (h1 g).1 x]
    rw [this]; exact (h1 g).2
  have hSD0 : ∀ N : ℕ, SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hW, hint, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La0 D (tor0 D cc δ) P.a P.d)
    (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  obtain ⟨-, -, -, -, -, -, hq⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hC P.a P.d (La D (tor0 D cc δ) L₁ L₁')
    (Or.inr ⟨_, _, hSD _ g _ hL, hSD _ g' _ hL', rfl⟩)
  have he0 : P.e0 ∈ Th D (tor0 D cc δ) (stdL D P.a) (stdL D P.d) := P.vac.1
  have hfix : ∀ x ∈ La0 D (tor0 D cc δ) P.a P.d, Wd D (tor0 D cc δ) x P.e0 = P.e0 := by
    intro x hx
    rw [hW x hx]; funext z; exact he0.2 x hx z
  have heT : P.e0 ∈ TT D (tor0 D cc δ) P.a P.d :=
    ⟨he0.1, 1, one_pos, fun x hx => by rw [one_nsmul]; exact hfix x hx⟩
  obtain ⟨c, hc1, hc2, hc3⟩ := GlobalTheory.T.vacuum_under_adelic_pair_unit_modulus_factor D cc δ hC P.a P.d (P.d_even.mul_left _) P.e0 he0 P.W g g'
    L₁ L₁' hL hL'
  obtain ⟨k, r, z, hz, hr1, hr2, hF⟩ := P.pres
  have hT : ∀ i, Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 ∈ TT D (tor0 D cc δ) P.a P.d := by
    intro i
    refine ⟨Wd_diff _ he0.1, Q, hQ, fun x hx => ?_⟩
    obtain ⟨m, hm⟩ := hint x hx _ (hz i)
    rw [Hf_nsmul_right, ← Hf_nsmul_left] at hm
    rw [Wd_comm _ _ m hm, hfix _ (nsmul_mem hx _)]
  have hQc : (Q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQ.ne'
  have key : ∀ i, ∃ y : VC D P.a P.d, Q • y ∈ La D (tor0 D cc δ) L₁ L₁' ∧
      P.W.Om g g' (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0) =
        Wd D (tor0 D cc δ) y (P.W.Om g g' P.e0) := by
    intro i
    obtain ⟨B, hB, h⟩ := approx_La (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1.1 _ _ hL hL' (hz i)
    obtain ⟨m, hm, hl⟩ := P.W.lift g g' ((Q : D.host.E)⁻¹ • B) P.e0 heT
    obtain ⟨B', h1, h2⟩ := h (m * Q) (by positivity)
    refine ⟨pt D (tor0 D cc δ) δ ((Q : D.host.E)⁻¹ • B'), ?_, ?_⟩
    · rw [pt_div, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hQc, one_smul]; exact h1
    · rw [← hl _ (closeTo_div hQ h2), pt_div, ← hB, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hQc, one_smul]
  choose y hy1 hy2 using key
  have hu : ∀ i, ∃ u : Qbar, (u : ℂ) = wdPh D (tor0 D cc δ) (y i) ∧ IsIntegral ℤ u ∧
      ∀ ρ : Qbar →+* ℂ, ‖ρ u‖ = 1 := by
    intro i
    obtain ⟨m, hm⟩ := hq _ (hy1 i)
    exact root_unity (by positivity) (wdPh_pow _ m hm)
  choose u hu1 hu2 hu3 using hu
  refine ⟨c, k, fun i => r i * u i, y, fun _ => ⟨hc1, hy1, fun i => ?_, fun ρ => ?_, ?_, hc3⟩⟩
  · rw [← mul_assoc]; exact (hr1 i).mul (hu2 i)
  · simpa only [map_mul, norm_mul, hu3, mul_one] using hr2 ρ
  · have hF' : P.F = ∑ i, (r i : ℂ) • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) P.e0 := by
      rw [hF]; funext w; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hF', (Om_sum P.W g g' Finset.univ _ _ hT).2]
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hy2, hc2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_mul, hu1]
    simp only [Wd, U]
    ring

end GlobalTheory.ArchFree.expand
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testVector_adelicPair_translates_movedLatticeVacuum : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), ∀ (g : GA D P.a) (g' : GA D P.d) L₁ L₁', Moves D (g : GL (Fin P.a) (AE D)) L₁ → Moves D (g' : GL (Fin P.d) (AE D)) L₁' → ∃ (c : ℂ) (k : ℕ) (r : Fin k → Qbar) (y : Fin k → VC D P.a P.d), 0 < Q → (Mod1All c ∧ (∀ i, Q • y i ∈ La D (tor0 D cc δ) L₁ L₁') ∧ (∀ i, IsIntegral ℤ ((Q : Qbar) ^ (P.a * P.d) * r i)) ∧ (∀ ρ : Qbar →+* ℂ, (∑ i, ‖ρ (r i)‖) ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d)) ∧ (P.W.Om g g' P.F = fun z => c * ∑ i, (r i : ℂ) * U D (tor0 D cc δ) (y i) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d) (La D (tor0 D cc δ) L₁ L₁') P.e0) z) ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (k' : GA D P.d), k' ∈ intG D P.d → TrivAt D p (g : GL (Fin P.a) (AE D)) → TrivAt D p ((g' * k' : GA D P.d) : GL (Fin P.d) (AE D)) → ‖lamC lam c‖ = 1) := by
  atlas_forward_decl GlobalTheory.ArchFree.expand.om_expand
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ArchFree.firstBasisVectorLike

open GlobalTheory.VacuumMove

theorem isVacuum_thetaIntertwiner_selfDual : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  rintro D cc δ t0 hc ht a d L L' L₁ L₁' hL hL' hL₁ hL₁' G ⟨b, κ, hb, hκ, rfl⟩
  obtain ⟨μ, hμ, h⟩ := GlobalTheory.T.admissible_characters_exist D cc δ hc a d _ _ _ (Or.inl ⟨_, b, hb, rfl⟩) (Or.inr ⟨L, L', hL, hL', rfl⟩)
    (Or.inr ⟨L₁, L₁', hL₁, hL₁', rfl⟩) _ (pullbackOrthonormal_normalizedTheta_mem_thetaSpace D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ t0 hc ht b hb.1)
  refine ⟨b, κ * μ, hb, mod1All_mul hκ hμ, funext fun z => ?_⟩
  rw [Iop_mul, mul_assoc κ μ]
  exact congrArg (κ * ·) (congrFun h z)

end GlobalTheory.ArchFree.firstBasisVectorLike
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_image_intertwiner_selfDual_pair : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (a d : ℕ) L L' L₁ L₁', SD D L → SD D L' → SD D L₁ → SD D L₁' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G → ThetaVectorUpToUnits D (tor0 D cc δ) t0 L₁ L₁' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (G : VC D a d → ℂ)) := by
  atlas_forward_decl GlobalTheory.ArchFree.firstBasisVectorLike.isVacuum_thetaIntertwiner_selfDual
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.coord

theorem coord_conj_le : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  intro D cc δ t0 Q hc ht0 P hQ B hB hn ρ t0' ht0' h T
  generalize hM : (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) = M
  have hev : Even (P.a * P.d) := P.d_even.mul_left _
  obtain ⟨Lt, hL, hL1, -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.a
  obtain ⟨Lt', hL', hL1', -⟩ := GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport D P.d
  have hs : SD D (stdL D P.a) := hL1 ▸ (hL 1).2
  have hs' : SD D (stdL D P.d) := hL1' ▸ (hL' 1).2
  have hjet : ∀ L L', SD D L → SD D L' → ∀ G, ThetaVectorUpToUnits D (tor0 D cc δ) t0 L L' G →
      ∀ y, LaQ D (tor0 D cc δ) L L' y →
      GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G) ∈ Qbar ∧
        ‖cj Qbar ρ (GL3Theta.applyAt0 D (minorPol D T) (U D (tor0 D cc δ) y G))‖ ^ 2 ≤ M := by
    intro L L' h1 h2 G hG y hy
    rw [← hM]
    exact GlobalTheory.T.conjugate_jet_bound_vacuum_torsion_translate D cc δ t0 hc ht0 P.a P.d L L' h1 h2 hev G hG y hy P.n B hB hn ρ t0' ht0' T
  have hM0 : 0 ≤ M :=
    (sq_nonneg _).trans (hjet _ _ hs hs' P.e0 P.vac.2.2.2.1 0 ⟨1, one_pos, by simp⟩).2
  have hterm : ∀ x, P.term x h T ∈ Qbar ∧ ‖cj Qbar ρ (P.term x h T)‖ ^ 2 ≤ (Q : ℝ) ^ (P.a * P.d) * M := by
    intro x
    obtain ⟨c, k, r, y, hy⟩ := GlobalTheory.T.testVector_adelicPair_translates_movedLatticeVacuum D cc δ t0 Q hc ht0 P x h (Lt x) (Lt' h) (hL x).1 (hL' h).1
    obtain ⟨⟨hcQ, hc1⟩, hy, -, hr, hF, -⟩ := hy hQ
    have hG := GlobalTheory.T.vacuum_image_intertwiner_selfDual_pair D cc δ t0 hc ht0 P.a P.d _ _ (Lt x) (Lt' h) hs hs' (hL x).2 (hL' h).2 P.e0
      P.vac.2.2.2.1
    have hGd := GlobalTheory.NormSum.CoordConj.differentiable_Iop (T := tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.vac.1.1
    change ThetaVectorUpToUnits D (tor0 D cc δ) t0 (Lt x) (Lt' h) (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0) at hG
    generalize Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) P.a P.d)
      (La D (tor0 D cc δ) (Lt x) (Lt' h)) P.e0 = G at hG hGd hF
    have e : P.W.Om x h P.F = ∑ i, (((⟨c, hcQ⟩ * r i : Qbar) : ℂ)) • U D (tor0 D cc δ) (y i) G := by
      rw [hF]
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, MulMemClass.coe_mul, mul_assoc]
    unfold Pair.term
    rw [e, GlobalTheory.NormSum.CoordConj.applyAt0_comb _ _ _ fun i => GlobalTheory.NormSum.CoordConj.differentiable_U _ hGd]
    refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ hM0 ?_ fun i => hjet _ _ (hL x).2 (hL' h).2 G hG _ ⟨Q, hQ, hy i⟩
    have h1 : ‖ρ ⟨c, hcQ⟩‖ = 1 := hc1 (ρ : Qbar →+* ℂ)
    simp only [map_mul, norm_mul, h1, one_mul]
    exact hr (ρ : Qbar →+* ℂ)
  haveI := (GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le D P.a).1
  haveI := Fintype.ofFinite (Cls D P.a (intG D P.a))
  have e : P.coord h T = ∑ x : Cls D P.a (intG D P.a),
      ((((gam D (intG D P.a) x.out : Qbar))⁻¹ : Qbar) : ℂ) * P.term x.out h T := by
    unfold Pair.coord
    rw [finsum_eq_sum_of_fintype]
    simp
  rw [e, mul_assoc]
  refine GlobalTheory.NormSum.CoordConj.comb_bound ρ _ _ _ _ (by positivity) ?_ fun x => hterm _
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [Nat.card_eq_fintype_card, Fintype.card, Finset.card_eq_sum_ones]
  push_cast
  refine Finset.sum_le_sum fun x _ => ?_
  rw [map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
  exact Nat.cast_inv_le_one _

end GlobalTheory.ArchFree.coord
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded : ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → ∀ (B : ℝ), 1 ≤ B → (∀ τ, (P.n τ : ℝ) ≤ 2 * B) → ∀ (ρ : Qbar →ₐ[ℚ] ℂ) t0', GL3Theta.IsTwoTorsionPointUnkilled D (lamConj Qbar ρ (lamOf D cc δ)) t0' → ∀ h T, P.coord h T ∈ Qbar ∧ ‖cj Qbar ρ (P.coord h T)‖ ^ 2 ≤ (Nat.card (Cls D P.a (intG D P.a)) : ℝ) ^ 2 * (Q : ℝ) ^ (P.a * P.d) * (((P.a.factorial : ℝ) ^ (∑ τ, P.n τ)) ^ 2 * (3 * (2 * ((fF D * P.a * P.d : ℕ) : ℝ) * D.host.rdE + 1) ^ (fF D * P.a * P.d) * nrm1Sq (lamConj Qbar ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj Qbar ρ (lamOf D cc δ)) t0') ^ (fF D * P.a * P.d) * (2 * Real.exp 1 * Real.pi * B / area (lamConj Qbar ρ (lamOf D cc δ))) ^ (P.a * ∑ τ, P.n τ))) := by
  atlas_forward_decl GlobalTheory.ArchFree.coord.coord_conj_le
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.means

open GlobalTheory.PositiveMeans

theorem exists_crv_conj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 (lamOf D cc δ) ∈ M) (h3 : g3 (lamOf D cc δ) ∈ M) :
    ∃ cc' δ', Crv D cc' δ' ∧ lamConj M ρ (lamOf D cc δ) = lamOf D cc' δ' := by
  obtain ⟨M', ρ', halg, hext⟩ := GlobalTheory.TwoTorsionPt.exists_extension M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [(hext _ h2).2, (hext _ h3).2]
  rw [hl]
  have hD : DataIn D (tor0 D cc δ) M' := by
    refine ⟨fun τ x => halg _ ?_, (hext _ h2).1, (hext _ h3).1⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.ThetaConj.useBar_holds D cc δ hc M' ρ' hD
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' ρ' hfix hD.2.1 hD.2.2 1 one_pos
    exact ⟨cc', δ', hc', e⟩
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.ConjCurve.galCurve_holds D cc δ hc M' (rhoBar M' ρ') hfix hD.2.1 hD.2.2 1 one_pos
    have hm : (lamConj M' ρ' (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc' δ' := by
      rw [← e]
      exact (congrArg Tor.abelian₂ hbar).symm
    generalize lamConj M' ρ' (lamOf D cc δ) = Λ at hm
    obtain ⟨-, -, hdisc, -, hO⟩ := GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
    have hd : TaylorLogMetric.discr Λ = 1 := by
      rw [← hm, TaylorLogMetric.discr, g2, g3, eisG_conj, eisG_conj] at hdisc
      apply (starRingEnd ℂ).injective
      rw [map_one, ← hdisc, TaylorLogMetric.discr, g2, g3]
      simp [map_ofNat]
    obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ)
      (by rw [hd]; exact one_ne_zero)
    obtain ⟨c, d, h, -, e'⟩ := GlobalTheory.ConjCurve.exists_crv D Λ L.ω₁ L.ω₂ (by simpa using L.indep.ne_zero 0)
      (fun z => (hL z).trans PeriodPair.mem_lattice) (fun r z hz => by
        obtain ⟨r', hr⟩ := exists_conj D r
        have h1 : (starRingEnd ℂ) z ∈ lamOf D cc' δ' := hm ▸ ⟨z, hz, rfl⟩
        have h4 : GlobalTheory.ConjCurve.embK D r' * (starRingEnd ℂ) z ∈ lamOf D cc' δ' := hO r' _ h1
        rw [hr, ← map_mul, ← hm] at h4
        obtain ⟨u, hu, e⟩ := h4
        have : u = _ := (starRingEnd ℂ).injective e
        exact this ▸ hu) hd 1 one_pos
    exact ⟨c, d, h, e'⟩

theorem means_le : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → wpF (lamOf D cc δ) t0 ∈ M → ∀ t : (M →ₐ[ℚ] ℂ) → ℂ, (∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)) → (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) / (Module.finrank ℚ M : ℝ) ≤ C * L ∧ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))) / (Module.finrank ℚ M : ℝ) ≤ C * L := by
  obtain ⟨C, hC, hA⟩ := GlobalTheory.LatticeAreaBound.area_bounded_of_discr_eq_one
  have hc1 : 0 ≤ Real.posLog C := Real.posLog_nonneg
  have hc2 : 0 ≤ Real.posLog (2 * Real.pi ^ 2) := Real.posLog_nonneg
  refine ⟨18 + 3 / 2 * (Real.posLog (2 * Real.pi ^ 2) + (Real.posLog C + 2)), by positivity, ?_⟩
  intro D cc δ t0 hc _ L hL hrd hdl M _ h2 h3 _ t ht
  obtain ⟨-, hlogd, hr1, -⟩ := GlobalTheory.T.derivationDenominators_and_hostField_sizes D (GlobalTheory.InducedType.induced_type D).1
  have hn : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have hcard : (Fintype.card (M →ₐ[ℚ] ℂ) : ℝ) = Module.finrank ℚ M := by
    exact_mod_cast AlgHom.card ℚ M ℂ
  have hper := GlobalTheory.T.mean_log_period_conjugates_eq_chowlaSelberg D (GlobalTheory.InducedType.induced_type D).1 cc δ hc M h2 h3
  have hd0 : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hpi := Real.pi_gt_three
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlp : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
  have hl2p : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt hd0.le, div_eq_iff hn.ne'] at hper
  have hB : Real.posLog (3 * (2 * D.host.rdE + 1)) ≤ 9 * L := by
    refine (Real.posLog_le_posLog (by positivity) (show _ ≤ 9 * D.host.rdE by linarith)).trans ?_
    rw [Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; linarith),
      Real.log_mul (by norm_num) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 9 by norm_num)
    linarith
  have key : ∀ ρ : M →ₐ[ℚ] ℂ,
      Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ ≤
        Real.posLog C - Real.log (area (lamConj M ρ (lamOf D cc δ)) / Real.pi) - Real.log Real.pi ∧
      Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) ≤
        (18 * L + 3 / 2 * Real.posLog (2 * Real.pi ^ 2)) +
          3 / 2 * Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ := by
    intro ρ
    obtain ⟨cc', δ', hc', e⟩ := exists_crv_conj hc M ρ h2 h3
    have ht' := ht ρ
    rw [e] at ht' ⊢
    obtain ⟨hΛ, -, hdisc, -, hO⟩ := GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc'
    obtain ⟨ha0, haC⟩ := hA _ hΛ hdisc
    constructor
    · rw [Real.log_div ha0.ne' (by positivity)]
      have h1 := Real.posLog_le_posLog ha0.le haC
      have h4 := Real.posLog_sub_posLog_inv (x := area (lamOf D cc' δ'))
      linarith
    · have := posLog_nrm_le _ hΛ hdisc ((GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.InducedType.induced_type D).1).1 cc' δ' hc'.1 hc'.2)
        (GlobalTheory.T.sigmaStar_value_le_meanSquare_genusOne D (GlobalTheory.InducedType.induced_type D).1 cc' δ' hc') ht'.1 (not_mem_lattice_of_isCMTorsionBasePoint ht' hO)
      linarith
  have s1 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ ≤
      (Real.posLog C + 2) * L * Module.finrank ℚ M := by
    refine (Finset.sum_le_sum fun ρ _ => (key ρ).1).trans ?_
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hper, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, hcard]
    have h5 := le_abs_self (logDerivativeAtOne D)
    have h6 : Real.posLog C ≤ Real.posLog C * L := le_mul_of_one_le_right hc1 hL
    have h7 : Real.posLog C - (Real.eulerMascheroniConstant + (Real.log (2 * Real.pi) - Real.log D.host.d / 2) -
      logDerivativeAtOne D) - Real.log Real.pi ≤ (Real.posLog C + 2) * L := by linarith
    have := mul_le_mul_of_nonneg_right h7 hn.le
    linarith
  have h8 : Real.posLog (2 * Real.pi ^ 2) ≤ Real.posLog (2 * Real.pi ^ 2) * L := le_mul_of_one_le_right hc2 hL
  constructor
  · rw [div_le_iff₀ hn]
    refine s1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by linarith)) hn.le)
    linarith
  · rw [div_le_iff₀ hn]
    refine (Finset.sum_le_sum fun ρ _ => (key ρ).2).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    have := mul_le_mul_of_nonneg_right h8 hn.le
    linarith

end GlobalTheory.ArchFree.means
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], g2 (lamOf D cc δ) ∈ M → g3 (lamOf D cc δ) ∈ M → wpF (lamOf D cc δ) t0 ∈ M → ∀ t : (M →ₐ[ℚ] ℂ) → ℂ, (∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)) → (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) / (Module.finrank ℚ M : ℝ) ≤ C * L ∧ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ)))) / (Module.finrank ℚ M : ℝ) ≤ C * L := by
  atlas_forward_decl GlobalTheory.ArchFree.means.means_le
end

section
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.norm

open GlobalTheory.ArchNorm

set_option maxHeartbeats 800000 in

theorem norm_meanInf_posLog_le : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (N : ℕ) (B L : ℝ) (P : Pair D cc δ t0 Q) (x : K), 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → P.Small N B → σ x = (P.norm : ℂ) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.conjugate_lattice_means_posLog_area_theta_bounded
  refine ⟨1100 + 4 * C₀, by positivity, ?_⟩
  intro D cc δ t0 Q hc ht hQ K _ _ _ σ N B L P x hN hB hL hrL hdL hsm hx
  obtain ⟨-, -, hr, hf, hcard, -⟩ := GlobalTheory.T.derivationDenominators_and_hostField_sizes D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1).2 cc δ hc
  obtain ⟨-, hcd, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D P.d
  obtain ⟨hfin, hch⟩ := hJ P.J P.J_le P.idx_ne
  have hca := (GlobalTheory.NormSum.cls_finite_card_le D P.a).2.1
  have hcT := (GlobalTheory.MinorBound.minor_bound D P.a P.d P.n (fun _ => 0) 0 1 B one_pos hB le_rfl hsm.2
    (differentiable_const _) (fun z => by simp)).1
  have hcoord := GlobalTheory.T.definiteThetaPair_coordinate_conjugates_bounded D cc δ t0 Q hc ht P hQ B hB hsm.2
  let _ : Fintype (Cls D P.d P.J) := Fintype.ofFinite _
  have hwp : wpF (lamOf D cc δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := mul_mem_lamOf D cc δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have hz : ∀ h T, P.coord h T ∈ Qbar := fun h T => by
    obtain ⟨t', ht'⟩ := (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 Qbar Qbar.val hdata.2.1 hdata.2.2
    exact (hcoord Qbar.val t' ht' h T).1
  let b := Module.finBasis ℚ K
  obtain ⟨M, hM1, hM2, hM⟩ := exists_galois
    (Set.range (fun i => σ (b i)) ∪
      Set.range (fun p : Cls D P.d P.J × Tup D P.a P.d P.n => P.coord p.1.out p.2) ∪
      {g2 (lamOf D cc δ), g3 (lamOf D cc δ), wpF (lamOf D cc δ) t0})
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.toFinite _)) (by
      rintro y ((⟨i, rfl⟩ | ⟨p, rfl⟩) | rfl | rfl | rfl)
      · exact mem_algebraicClosure_iff.2
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom σ.toRatAlgHom)
      · exact hz _ _
      · exact hdata.2.1
      · exact hdata.2.2
      · exact hwp)
  have hσ : ∀ y, σ y ∈ M := fun y => by
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact M.smul_mem (hM _ (Or.inl (Or.inl ⟨i, rfl⟩)))
  have h2 : g2 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h3 : g3 (lamOf D cc δ) ∈ M := hM _ (Or.inr (by simp))
  have h4 : wpF (lamOf D cc δ) t0 ∈ M := hM _ (Or.inr (by simp))
  have hzM : ∀ p : Cls D P.d P.J × Tup D P.a P.d P.n, P.coord p.1.out p.2 ∈ M :=
    fun p => hM _ (Or.inl (Or.inr ⟨p, rfl⟩))
  choose t htt using fun ρ : M →ₐ[ℚ] ℂ => (GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates D cc δ hc).2 M ρ h2 h3
  obtain ⟨hu, hv⟩ := hmean D cc δ t0 hc ht L hL hrL hdL M h2 h3 h4 t htt
  refine (GlobalTheory.ArchMean.meanInf_posLog_le K σ x M (Cls D P.d P.J × Tup D P.a P.d P.n)
    (fun p => ((gam D P.J p.1.out : ℚ))⁻¹) (fun p => ⟨P.coord p.1.out p.2, hzM p⟩) hσ
    (fun p => by positivity) ?_).trans ?_
  · rw [hx, Pair.norm, finsum_eq_sum_of_fintype, Fintype.sum_prod_type]
    push_cast
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Pair.sq, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Complex.mul_conj']
    push_cast
    rfl
  have hs : ((∑ τ, P.n τ : ℕ) : ℝ) ≤ 2 * fF D * B := by
    push_cast
    refine (Finset.sum_le_card_nsmul _ _ _ fun τ _ => hsm.2 τ).trans (le_of_eq ?_)
    rw [Finset.card_univ, hcard, nsmul_eq_mul]; ring
  have hf' : (1 : ℝ) ≤ fF D := by exact_mod_cast hf
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm0 : 0 ≤ Real.log (B * (2 * (N : ℝ))) := Real.log_nonneg (by nlinarith)
  have hfn : 1 ≤ (fF D : ℝ) * (2 * (N : ℝ)) := by nlinarith
  have hl0 : 0 ≤ Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := Real.log_nonneg (by nlinarith)
  have hq0 : 0 ≤ Real.log Q := Real.log_natCast_nonneg Q
  set E₀ : ℝ := 1100 * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) +
      1100 * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) +
      1100 * (N : ℝ) ^ 2 * Real.log Q with hE₀
  have key : ∀ ρ : M →ₐ[ℚ] ℂ,
      Real.posLog (∑ p : Cls D P.d P.J × Tup D P.a P.d P.n,
        ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) * ‖ρ ⟨P.coord p.1.out p.2, hzM p⟩‖ ^ 2) ≤
      E₀ + (4 * fF D * (N : ℝ) ^ 2 * Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) +
        4 * fF D * N * B * Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹) := by
    intro ρ
    obtain ⟨ρ', hρ⟩ := exists_extension M ρ
    have hl : lamConj Qbar ρ' (lamOf D cc δ) = lamConj M ρ (lamOf D cc δ) := by
      unfold lamConj
      rw [hρ _ h2, hρ _ h3]
    have hb := hcoord ρ' (t ρ) (hl ▸ htt ρ)
    rw [hl] at hb
    have h5 : 0 ≤ Real.posLog (nrm1Sq (lamConj M ρ (lamOf D cc δ))
        (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) (t ρ))) := Real.posLog_nonneg
    have h6 : 0 ≤ Real.posLog (area (lamConj M ρ (lamOf D cc δ)))⁻¹ := Real.posLog_nonneg
    refine posLog_le_of_le_exp (by positivity) (by positivity) (le_trans ?_
      (sizes (fF D) N P.a P.d (∑ τ, P.n τ) Q (Nat.card (Cls D P.d P.J)) (Fintype.card (Tup D P.a P.d P.n))
        _ _ B L D.host.rdE _ _ hf hN P.a_le hsm.1 hs hQ hB hL hr hrL (lattice_unitNormSq_nonneg _ _) (area_nonneg _)
        (hch.trans (Nat.mul_le_mul_left _ P.idx_le)) hcT hcd hca))
    refine sum_prod_le _ _ fun p => ?_
    · refine le_trans ?_ (hb p.1.out p.2).2
      have hg := (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D P.d P.J P.J_le p.1.out).1
      have hg1 : ((((gam D P.J p.1.out : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1 := by
        push_cast
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hg)
      have he : cj Qbar ρ' (P.coord p.1.out p.2) = ρ ⟨P.coord p.1.out p.2, hzM p⟩ := by
        unfold cj
        rw [hρ _ (hzM p)]
        unfold TaylorLogMetric.liftM
        rw [dif_pos (hzM p)]
      rw [he]
      exact mul_le_of_le_one_left (by positivity) hg1
  clear_value E₀
  have hM0 : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum fun ρ _ => key ρ) hM0.le).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, AlgHom.card, nsmul_eq_mul, add_div, add_div, mul_div_cancel_left₀ _ hM0.ne',
    mul_div_assoc, mul_div_assoc]
  have p1 := mul_le_mul_of_nonneg_left hu (show (0 : ℝ) ≤ 4 * fF D * N * B by positivity)
  have p2 := mul_le_mul_of_nonneg_left hv (show (0 : ℝ) ≤ 4 * fF D * (N : ℝ) ^ 2 by positivity)
  have p3 : 0 ≤ C₀ * fF D * N * B * L := by positivity
  have p4 : 0 ≤ C₀ * fF D * N * B * Real.log (B * (2 * (N : ℝ))) := by positivity
  have p5 : 0 ≤ C₀ * fF D * (N : ℝ) ^ 2 * Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B) := by positivity
  have p6 : 0 ≤ C₀ * (N : ℝ) ^ 2 * Real.log Q := by positivity
  rw [hE₀]
  linarith

end GlobalTheory.ArchFree.norm
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_meanInf_posLog_le_definiteThetaPair : ∃ C : ℝ, 0 < C ∧ ∀ (D : D7), ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → 0 < Q → ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (N : ℕ) (B L : ℝ) (P : Pair D cc δ t0 Q) (x : K), 1 ≤ N → 1 ≤ B → 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → P.Small N B → σ x = (P.norm : ℂ) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ C * fF D * (2 * (N : ℝ)) * B * (L + Real.log (B * (2 * (N : ℝ)))) + C * fF D * (N : ℝ) ^ 2 * (L + Real.log ((fF D : ℝ) * (2 * (N : ℝ)) * B)) + C * (N : ℝ) ^ 2 * Real.log Q := by
  atlas_forward_decl GlobalTheory.ArchFree.norm.norm_meanInf_posLog_le
end

section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchFree.st

theorem archSt : ArchSt := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.T.norm_meanInf_posLog_le_definiteThetaPair
  refine ⟨C, hC, ?_⟩
  intro D cc δ t0 Q hc ht hQ K _ _ _ σ ι N B L P P' zA zA' hN hB h1 hL hd hs hn i
  exact ⟨h D cc δ t0 Q hc ht hQ K σ N B L (P i) (zA i) hN hB h1 hL hd (hs i).1 (hn i).1,
    h D cc δ t0 Q hc ht hQ K σ N B L (P' i) (zA' i) hN hB h1 hL hd (hs i).2 (hn i).2⟩

end GlobalTheory.ArchFree.st
end
