import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
import Formalism.PieriBlockIdeals.StatementE
import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds
import Formalism.PieriBlockIdeals.PieriColumnMinors.CorollaryOfParamsSevenLinkageAlt
import Formalism.PieriBlockIdeals.PieriColumnMinors.RecursionInclusionExceptional
import Development.AutomorphicArithmetic.PrimeDiscriminants.ExcSet

section
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem expo_frob_indep : ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool), ({ W with fr := fr, cj := cj } : Wts ι).Ok P ∧
      ∀ l : ℕ, l.Prime → W.WRange P l → ({ W with fr := fr, cj := cj } : Wts ι).coarseWeightBound P l = W.coarseWeightBound P l := by
  intro P hH hL ι _ _ W hW fr cj
  have hW' : ({ W with fr := fr, cj := cj } : Wts ι).Ok P :=
    { anti := hW.anti, what₂ := hW.what₂, block := hW.block, centre := hW.centre, window := hW.window,
      cloud := hW.cloud, low := hW.low, thick := hW.thick, other := hW.other }
  refine ⟨hW', ?_⟩
  intro l hl hR
  have hN := (places_real_holds P hH hL ι W hW (fun _ => 0)).2
  have hN' := (places_real_holds P hH hL ι ({ W with fr := fr, cj := cj } : Wts ι) hW' (fun _ => 0)).2
  have hi : ({ W with fr := fr, cj := cj } : Wts ι).iW P l = W.iW P l := by
    funext τ
    unfold Wts.iW SizeData₂.depth
    obtain ⟨a1, a2⟩ := hN l hl hR.1 hR.2.2.1 τ
    obtain ⟨b1, b2⟩ := hN' l hl hR.1 hR.2.2.1 τ
    rw [a1, a2, b1, b2]
    rfl
  unfold Wts.coarseWeightBound
  rw [hi]
  rfl

end GlobalTheory
end

section
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory.ExpTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lIncl_of_models : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  intro K _ _ _ G _ _ Pl0 B ℓ Z w ι _ _ P W hN hl hR fr cj I X hC hX
  obtain ⟨hH, hL, hW, -⟩ := hN
  obtain ⟨hW', hJ⟩ := GlobalTheory.expo_frob_indep P hH hL ι W hW fr cj
  have hEq := hJ _ hl hR
  apply hC
  intro i
  obtain ⟨hu, hLk⟩ := hX i
  have hWI := Formalism.CohomologicalDescent.ShortWeightBounds.weight_inputs_of_linkage_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hR.1 hLk
  have h := (Formalism.CohomologicalDescent.Top.inclusion_w_seven_real_holds P hH hL ι (reFr W fr cj) hW' _ (X i) hl hu hR.1 hWI).1
  unfold reFr at h
  rw [hEq] at h
  exact h

end GlobalTheory.ExpTie
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePowerLatticeInclusion_of_localModels : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι), NumOk P W → (Formalism.EigenvalueLevelCeiling.plc w).Prime → W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam), Covers B ℓ Z w X → (∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) → LIncl B ℓ Z w (W.coarseWeightBound P (Formalism.EigenvalueLevelCeiling.plc w)) := by
  atlas_forward_decl GlobalTheory.ExpTie.lIncl_of_models
end

section
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.ExpTie

theorem exists_mul_eq_prW_pow {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (J : ℕ) {a : 𝓞 K}
    (ha : a ∈ w.asIdeal ^ (J * Formalism.L2.Col.eW w)) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ b : 𝓞 K, t * a = ((Formalism.L2.Col.prW w : ℕ) : 𝓞 K) ^ J * b := by
  have hm := (Formalism.L2.Col.algebraMap_mem_maximalIdeal_pow_iff w a (J * Formalism.L2.Col.eW w)).2 ha
  rw [mul_comm, pow_mul, ← Formalism.L2.Col.span_prW_ow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨y, hy⟩ := hm
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective w.asIdeal.primeCompl y
  refine ⟨t, t.2, b, ?_⟩
  apply IsLocalization.injective (Formalism.L2.Col.Ow w) w.asIdeal.primeCompl_le_nonZeroDivisors
  rw [map_mul, map_mul, hy, map_pow, map_natCast, mul_comm, mul_assoc, IsLocalization.mk'_spec]

theorem LIncl.jexpU_bounds {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : Formalism.L2.DIV.BlockDat K G Pl0} {ℓ : Formalism.L2.DIV.Lvl K G} {Z : Submodule K B.S.Forms} {w : HeightOneSpectrum (𝓞 K)} {J : ℕ}
    (h : LIncl B ℓ Z w J) : 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  have he : 0 < Formalism.L2.Col.eW w := Formalism.L2.Col.eW_pos w
  have hp : Formalism.EigenvalueLevelCeiling.plc w = Formalism.L2.Col.prW w :=
    Formalism.L2.Col.eq_prW_of_mem w (Formalism.EigenvalueLevelCeiling.plc_prime w) (Formalism.EigenvalueLevelCeiling.plc_mem w)
  have key : B.JexpW ℓ Z w ≤ J * Formalism.L2.Col.eW w := by
    unfold Formalism.L2.DIV.BlockDat.JexpW Formalism.L2.DIV.expW
    apply Nat.sInf_le
    intro a ha z hz
    obtain ⟨t, ht, b, htb⟩ := exists_mul_eq_prW_pow w J ha
    obtain ⟨s, hs, hsz⟩ := h z hz
    refine ⟨s * t, w.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
    have e : (s * t) • (a • z) = b • (s • ((((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 K) ^ J) • z)) := by
      rw [hp, smul_smul, smul_smul, smul_smul, mul_assoc, htb]
      congr 1
      ring
    rw [e]
    exact Submodule.smul_mem _ b hsz
  refine ⟨?_, ?_⟩
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    positivity
  · unfold Formalism.L2.DIV.BlockDat.JexpU
    rw [div_le_iff₀ (by exact_mod_cast he)]
    exact_mod_cast key

theorem jexpU_le_of_lIncl : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type)
    (B : Formalism.L2.DIV.BlockDat K G Pl0) (ℓ : Formalism.L2.DIV.Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ),
    LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => LIncl.jexpU_bounds h

end GlobalTheory.ExpTie
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 : Type) (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K)) (J : ℕ), LIncl B ℓ Z w J → 0 ≤ B.JexpU ℓ Z w ∧ B.JexpU ℓ Z w ≤ J := by
  atlas_forward_decl GlobalTheory.ExpTie.jexpU_le_of_lIncl
end

section
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem exponent_of_record_vs_formulas :
    Formalism.CohomologicalDescent.E.ExCut → ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
      ∀ l : ℕ, l.Prime → (¬ W.WRange P l → W.JA P l ≤ W.Jrec7 P l) ∧ (W.WRange P l → W.coarseWeightBound P l = W.Jrec7 P l) := by
  intro hC P hH hL ι _ _ W hW l hl
  refine ⟨fun hR => ?_, fun hR => ?_⟩
  · by_cases hc : (l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp
    · rw [seventh_recursion_eq_a_of_small_prime W P l hc]
    · have h1 : P.lJ < (l : ℝ) := not_le.mp fun h => hc (Or.inl h)
      have h2 : ¬ P.Excl l := fun h => hc (Or.inr (Or.inl h))
      have h3 : l ∉ W.Sp := fun h => hc (Or.inr (Or.inr h))
      have hh : P.h < (l : ℝ) := not_le.mp fun h => hR ⟨h1, h, h2, h3⟩
      have hb := Formalism.CohomologicalDescent.E.beyond_height_exceptional (Formalism.CohomologicalDescent.E.exIntervalLt_of_exCut hC) hC P hH hL ι W hW l hl h1 hh
      rw [hb.2.1]
      exact Nat.zero_le _
  · obtain ⟨h1, _, h2, h3⟩ := hR
    have hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) := by
      rintro (h | h | h)
      · exact absurd h (not_le.mpr h1)
      · exact h2 h
      · exact h3 h
    rw [seventh_recursion_eq_w_of_large_prime W P l hc]

end GlobalTheory
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ExpTie.Asm

open Formalism.L2.Indef Formalism.L2.Indef.Tree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem jexpU_le_jrec7 (hcut : Formalism.CohomologicalDescent.E.ExCut) {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G]
    [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (w : HeightOneSpectrum (𝓞 K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : Par) (W : Wts ι) (hN : NumOk P W)
    (hoff : ¬ W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → LIncl B ℓ Z w (W.JA P (Formalism.EigenvalueLevelCeiling.plc w)))
    (hin : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∃ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool) (I : Type) (X : I → HidaSetting ι P.Nr W.lam),
      Covers B ℓ Z w X ∧ ∀ i, ¬ IsUnit ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : (X i).O) ∧ WInputsLink P (reFr W fr cj) (X i) (Formalism.EigenvalueLevelCeiling.plc w)) :
    B.JexpU ℓ Z w ≤ (W.Jrec7 P (Formalism.EigenvalueLevelCeiling.plc w) : ℚ) := by
  have hp := Formalism.EigenvalueLevelCeiling.plc_prime w
  have hrec := GlobalTheory.exponent_of_record_vs_formulas hcut P hN.1 hN.2.1 ι W hN.2.2.1 _ hp
  by_cases hR : W.WRange P (Formalism.EigenvalueLevelCeiling.plc w)
  · obtain ⟨fr, cj, I, X, hc, hX⟩ := hin hR
    have h1 := GlobalTheory.T.primePowerLatticeInclusion_of_localModels K G Pl0 B ℓ Z w ι P W hN hp hR fr cj I X hc hX
    have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ h1).2
    rw [hrec.2 hR] at h2
    exact h2
  · have h2 := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion K G Pl0 B ℓ Z w _ (hoff hR)).2
    exact h2.trans (by exact_mod_cast hrec.1 hR)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem splitPartNumbers_exponent_eq_liftExponent (C CH : ℝ) (t : p.P.T) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    ((R2 p).num (F2 p) C CH).J0 t w j = (((blk p j t).JexpU (lvlL p) (subZ p j t) w : ℚ) : ℝ) := rfl

open Classical in

theorem hasExpBound_at (hcut : Formalism.CohomologicalDescent.E.ExCut) {c : OnConst} (O : Obj p c)
    (hm : O.m = (D.R.m : ℝ)) (hx : O.x = L.sc.x) (heps : O.eps = L.sc.eps) (hT2 : O.T2 = D.host.T2.card)
    (Pj : Fin D.R.m → Par) (Wj : Fin D.R.m → Wts D.what₂.Tau) (hD : ∀ j, Dict L j (Pj j) (Wj j))
    (hN : ∀ j, NumOk (Pj j) (Wj j))
    (hS : ∀ j t w, LIncl (blk p j t) (lvlL p) (subZ p j t) w ((Wj j).JA (Pj j) (Formalism.EigenvalueLevelCeiling.plc w)))
    (hM : ∀ j, ∀ w ∈ p.R.twPl, (Wj j).WRange (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) → ModelAt p j (Pj j) (Wj j) w) (C CH : ℝ) :
    HasExpBound ((R2 p).num (F2 p) C CH) O := by
  refine ⟨fun w _ j => ?_, fun j l => ((Wj j).Jrec7 (Pj j) l : ℝ), fun j => ⟨fun l => Nat.cast_nonneg _, fun Q hQ => ?_⟩,
    fun w hw j => ?_⟩
  · have h := (GlobalTheory.T.exponent_datum_le_of_primePowerLatticeInclusion _ _ _ _ _ _ w _ (hS j ((S2 p).μ w) w)).1
    rw [splitPartNumbers_exponent_eq_liftExponent]
    exact_mod_cast h
  · obtain ⟨hHyp, hLarge, hOk, X', A, hRows, hBig⟩ := hN j
    have hcard : Fintype.card D.what₂.Tau = (Pj j).f := by rw [← Nat.card_eq_fintype_card]; exact (hD j).card
    have h := UpperTheory.ExcSet.sum_exponent_log_le hcut D (Pj j) X' A hHyp hLarge hRows hBig D.what₂.Tau (Wj j) hOk hcard (hD j).f
      (hD j).special O.T2
      (by rw [hT2]; exact (hD j).thick) Q hQ
    have hxe : O.xe = (Pj j).L := by rw [(hD j).log]; show O.x ^ O.eps = _; rw [hx, heps]
    have hb : O.b = (Pj j).b := by rw [(hD j).b]; show Real.exp O.xe = _; rw [hxe, (hD j).log]; rfl
    have hm' : O.m = ((Pj j).m : ℝ) := by rw [hm, (hD j).m]
    show _ ≤ 30 * (O.T2 : ℝ) * O.m * O.b * O.xe ^ 2 + 2 * O.m * O.b
    rw [hxe, hb, hm']
    exact h
  · have hle := jexpU_le_jrec7 hcut (blk p j (p.R.mu w)) (lvlL p) (subZ p j (p.R.mu w)) w (Pj j) (Wj j) (hN j)
      (fun _ => hS j _ w) (fun hR => hM j w hw hR)
    show (((blk p j (p.R.mu w)).JexpU (lvlL p) (subZ p j (p.R.mu w)) w : ℚ) : ℝ) ≤ ((Wj j).Jrec7 (Pj j) (Formalism.EigenvalueLevelCeiling.plc w) : ℝ)
    exact_mod_cast hle

end Point

theorem expSt_of : Formalism.CohomologicalDescent.E.ExCut → NumSt → SumExpSt → ModelSt → ExpSt := by
  intro hcut hN hS hM
  obtain ⟨a, ha, H⟩ := (hN.and hS).and hM
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨⟨x1, N1⟩, ⟨x2, S1⟩⟩, ⟨x3, M1⟩⟩ := hK Fm CH hc hL
  refine ⟨0, fun c _ _ => ⟨max x1 (max x2 x3), fun x hx hle i p hp hMo r O hR => ?_⟩⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hle)
  have h3 : x3 ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hle)
  choose Pj Wj hPW using N1 x hx h1 i p hp hMo
  obtain ⟨st, hRT⟩ := hR.1.depth
  letI := st
  letI := hostAlg (Fm.D x i)
  intro C CH'
  exact hasExpBound_at p hcut O hRT.m_eq hRT.x_eq hRT.eps_eq hR.1.realisedChain_torus_eq Pj Wj (fun j => (hPW j).1) (fun j => (hPW j).2)
    (fun j t w => S1 x hx h2 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 t w)
    (fun j w hw hR' => M1 x hx h3 i p hp hMo j (Pj j) (Wj j) (hPW j).1 (hPW j).2 w hw hR') C CH'

end GlobalTheory.ExpTie.Asm

end
end
