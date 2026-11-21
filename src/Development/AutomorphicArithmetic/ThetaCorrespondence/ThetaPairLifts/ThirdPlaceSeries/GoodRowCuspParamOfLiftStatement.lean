import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialPartInBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialPartInBaseChange
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.PartNormO
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlAwayRepsum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRow

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.MuBlockLoc
theorem part_norm_o_alt (D : D7) (ht : SumRepresentations.tie0 D) (hT : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D) {j : ℕ} {π : D.nbc.AU j}
    {Pa : List (Part D.naut.CG)} (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (p : Part D.naut.CG) (hp : p ∈ Pa)
    (w : PlE D.host) (hu : D.naut.unr (D.naut.locG p.π w)) :
    ∀ α ∈ D.naut.frobEig (D.naut.locG p.π w), UpperTheory.GalN.OpenB (Formalism.ConjugateSelfDual.normV w) α ∧ (p.a = 1 → ‖α‖ = 1) := by
  intro α hα
  have hAut := ht.2.1
  obtain ⟨ha1, hd1, hcsd⟩ := hB.1 p hp
  have hle : ∀ τ, (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤
      D.nbc.infW j (D.nbc.wtAU j π) τ := fun τ => by
    rw [← hB.2.2.2.2.2 τ]; exact mem_isoInf D Pa p hp hd1 τ
  have hW := fun τ => D.nbc.infW_alg j (D.nbc.wtAU j π) τ
  have hnd : ∀ τ, (D.naut.infG p.π τ).Nodup := fun τ =>
    Multiset.Nodup.of_map _ (Multiset.nodup_of_le (hle τ) (hW τ).1)
  have hint : ∀ τ, ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ,
      z + ((p.d : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ z hz
    obtain ⟨k, hk⟩ := (hW τ).2 _ (Multiset.mem_of_le (hle τ) (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; push_cast; ring⟩
  rcases Int.even_or_odd ((D.R.nV : ℤ) - p.d - p.a + 1) with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hr : D.naut.ralg p.π := (D.naut.ralg_def _).2 fun τ => ⟨hnd τ, fun z hz => by
      obtain ⟨k, hk⟩ := hint τ z hz
      refine ⟨k + m, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = (m : ℂ) + m := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      linear_combination hk + (1 / 2 : ℂ) * hm'⟩
    exact (_root_.UpperTheory.GalN.tempo' hT p.a p.π ha1 hcsd hr w).part hu α hα
  · have hr : D.naut.ralg (D.naut.tw p.π D.naut.etaT) := (D.naut.ralg_def _).2 fun τ => by
      obtain ⟨s, hs, k0, hk0⟩ : ∃ s : ℂ, D.naut.infG D.naut.etaT τ = {s} ∧ ∃ k0 : ℤ, s = (k0 : ℂ) + 1 / 2 := by
        rcases (hAut.2.1 τ).1 with h | h
        · exact ⟨1 / 2, h, 0, by simp⟩
        · exact ⟨-(1 / 2), h, -1, by push_cast; ring⟩
      rw [D.naut.infG_tw _ _ τ s hs]
      refine ⟨(hnd τ).map (add_left_injective s), fun z hz => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
      obtain ⟨k, hk⟩ := hint τ y hy
      refine ⟨k + k0 + m + 1, ?_⟩
      have hm' : ((D.R.nV : ℤ) : ℂ) - ((p.d : ℤ) : ℂ) - ((p.a : ℤ) : ℂ) + 1 = 2 * (m : ℂ) + 1 := by
        exact_mod_cast hm
      push_cast at hm' ⊢
      rw [hk0]
      linear_combination hk + (1 / 2 : ℂ) * hm'
    exact (_root_.UpperTheory.GalN.tempo' hT p.a _ ha1 (D.naut.csd_tw _ _ hAut.1.1 hcsd) hr w).part_tw hAut hu α hα
end GlobalTheory.MuBlockLoc
namespace GlobalTheory.MuBlockLoc
theorem split_step_o_alt (D : D7) (Rw : RowSide D) (hL : _root_.GlobalTheory.HeightCounting.Up.ParityLaws D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j)
    (μ : D.naut.CG 1) (Pa : List (Part D.naut.CG)) (hA : LiftAt D Rw j σ π μ) (hR : RowLoc D Rw σ)
    (hB : SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa) (w : PlE D.host) (hs : IsSplitPl D.host w)
    (hg : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k))
    (hPa : ∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) (hμ : D.naut.unr (D.naut.locG μ w)) :
    (∃ p ∈ Pa, D.R.t ≤ p.d) ∧ ∀ p ∈ Pa, D.R.t ≤ p.d → p.d = D.R.t ∧
      D.naut.frobEig (D.naut.locG p.π w) = D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := by
  have hT := hL.tie0
  have hLP := hT.1
  have hAut := hT.2.1
  have heu := D.naut.etaT_unr w
  have hed : D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 := D.naut.locG_dim _ _
  obtain ⟨e, he⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ heu hed
  have hen : ‖e‖ = 1 := (D.naut.tempered_unr _ heu).1 (hAut.2.2.1 w) e (by rw [he]; exact Multiset.mem_singleton_self e)
  have he0 : e ≠ 0 := by intro h; rw [h] at hen; simp at hen
  obtain ⟨hbu, hbe⟩ := D.naut.etaTinv_def w
  have hbd : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {e⁻¹} := by rw [hbe, he]; simp
  have hbn : ‖e⁻¹‖ = 1 := by rw [norm_inv, hen, inv_one]
  obtain ⟨m, hm⟩ := GlobalTheory.MuBlock.frobEig_eq_single D.nd D.naut _ hμ (D.naut.locG_dim _ _)
  have hmt := (_root_.UpperTheory.GalN.tempo' hL.temp 1 μ le_rfl hA.csd (mu_ralg D Rw j σ π μ hA) w).1 rfl
  have hmn : ‖m‖ = 1 := (D.naut.tempered_unr _ hμ).1 hmt m (by rw [hm]; exact Multiset.mem_singleton_self m)
  have htw : D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) = {m * e⁻¹} := by
    rw [D.naut.locG_tw, D.naut.frobEig_char _ _ (e⁻¹) hμ hbu hbd hb, hm]; simp
  have hV := hA.loc w hs
  have hiso := GlobalTheory.MuBlock.frobEig_isoLoc D.nd D.naut Pa w hPa
  have hVu : D.naut.unr (D.nbc.locAU j π w) := by rw [← hB.2.2.2.1 w hs]; exact hiso.1
  have hinv : D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) = D.naut.lpUnr w {1} := by
    have hu := D.naut.unr_char _ _ hed hbu heu
    rw [D.naut.unr_eq_lpUnr _ hu, D.naut.frobEig_char _ _ e hbu heu hed he, hb]; simp [he0]
  have hX : D.naut.lpChar (D.nbc.locAU j π w) (D.naut.locG D.naut.etaT w) =
      D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) := by
    rw [hV, (hLP w (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w))
      (Rw.locR σ w) (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) 0 hbd hed).2.2.2.1, hinv]
    exact (hLP w _ (Rw.locR σ w) (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaT w) 0 hed hed).2.2.2.2.1
  have hXu : D.naut.unr (D.naut.lpSum (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)) := by
    rw [← hX]; exact D.naut.unr_char _ _ hed hVu heu
  obtain ⟨hWu, hSu⟩ := (D.naut.unr_sum _ _).1 hXu
  have hmu := GlobalTheory.MuBlock.frobEig_spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w hμ
  dsimp only at hmu
  have hVe : D.naut.frobEig (D.nbc.locAU j π w) =
      (D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹) +
      ((List.range D.R.t).map fun k => ({(m * e⁻¹) * ((Formalism.ConjugateSelfDual.normV w : ℕ) : ℂ) ^
        (((((D.R.t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum := by
    rw [hV, D.naut.frobEig_char _ _ _ hXu hbu hbd hb, D.naut.frobEig_sum _ _ hWu hSu, Multiset.map_add]
    rw [hmu.2, hm]
    congr 1
    rw [← Multiset.coe_mapAddMonoidHom, map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Multiset.coe_mapAddMonoidHom, Multiset.map_singleton]
    ring_nf
  have key := UpperTheory.GalN.string_count (Formalism.ConjugateSelfDual.normV w) D.R.t
    (Pa.map fun p => (p.d, D.naut.frobEig (D.naut.locG p.π w)))
    ((D.naut.frobEig (Rw.locR σ w)).map (· * e⁻¹)) (m * e⁻¹)
    (by exact_mod_cast GlobalTheory.LocalInv.one_lt_normV w) D.R.t_odd.pos
    (by rw [norm_mul, hmn, hbn, one_mul])
    (by
      intro x hx
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hx
      rw [norm_mul, hbn, mul_one]
      have := (hR w hs hg).2 α hα
      rwa [GlobalTheory.MuBlock.absNorm_eq_normV] at this)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      have k := _root_.GlobalTheory.MuBlockLoc.part_norm_o_alt D hT hL.temp hB p hp w (hPa p hp)
      refine ⟨(hB.1 p hp).2.1, ?_, fun α hα => (k α hα).1, fun ht α hα =>
        (k α hα).2 (UpperTheory.GalN.rank_one_of_long hB.2.2.1 hp (hB.1 p hp).1 ht)⟩
      intro h0
      change D.naut.frobEig (D.naut.locG p.π w) = 0 at h0
      have h1 := D.naut.frobEig_card _ (hPa p hp)
      rw [h0, D.naut.locG_dim] at h1
      have := (hB.1 p hp).1
      simp at h1
      omega)
    (by
      have hiso2 := hiso.2
      simp only [GlobalTheory.LocalInv.list_coe, List.map_map] at hiso2
      rw [List.map_map]
      exact hiso2.symm.trans ((congrArg D.naut.frobEig (hB.2.2.2.1 w hs)).trans hVe))
  refine ⟨?_, fun p hp hpt => ?_⟩
  · obtain ⟨x, hx, hxt⟩ := key.1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact ⟨p, hp, hxt⟩
  · obtain ⟨h1, h2⟩ := key.2 _ (List.mem_map_of_mem (f := fun p : Part D.naut.CG => (p.d, D.naut.frobEig (D.naut.locG p.π w))) hp) hpt
    exact ⟨h1, h2.trans htw.symm⟩
end GlobalTheory.MuBlockLoc
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.MuBlockLoc
end GlobalTheory.MuBlockLoc
namespace GlobalTheory.MuBlockLoc
theorem mu_block_mem_alt : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa →
    (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  intro D Rw hL j σ π μ Pa hA hR hB
  have hgood : ∀ᶠ w in Filter.cofinite, ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧
      D.naut.unr (D.naut.locG μ w)) ∧ ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k) := by
    refine Filter.Eventually.and (Filter.Eventually.and ?_ (D.naut.locG_unr_ae _)) ?_
    · exact (Filter.eventually_all_finite (List.finite_toSet Pa)).2 fun p _ => D.naut.locG_unr_ae p.π
    · exact Filter.eventually_all.2 fun k => (placesOver_finite D k).compl_mem_cofinite
  obtain ⟨w0, hw0, hs0⟩ := GlobalTheory.MuBlock.exists_split_not_mem D.nd hL.an.2.2.1 _ (Filter.eventually_cofinite.1 hgood)
  have hg0 : ((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w0)) ∧ D.naut.unr (D.naut.locG μ w0)) ∧
      ∀ k : Fin 2, w0 ∉ placesOver D.host.E (D.host.g k) := by
    have h := hw0
    simp only [Set.mem_setOf_eq, not_not] at h
    exact h
  obtain ⟨⟨p0, hp0, hpt⟩, -⟩ := _root_.GlobalTheory.MuBlockLoc.split_step_o_alt D Rw hL j σ π μ Pa hA hR hB w0 hs0 hg0.2 hg0.1.1 hg0.1.2
  have hall : ∀ w, (((∀ p ∈ Pa, D.naut.unr (D.naut.locG p.π w)) ∧ D.naut.unr (D.naut.locG μ w)) ∧
      ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) →
      IsSplitPl D.host w → p0.d = D.R.t ∧ D.naut.frobEig (D.naut.locG p0.π w) =
        D.naut.frobEig (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) :=
    fun w hw hs => (_root_.GlobalTheory.MuBlockLoc.split_step_o_alt D Rw hL j σ π μ Pa hA hR hB w hs hw.2 hw.1.1 hw.1.2).2 p0 hp0 hpt
  have htu : ∀ w, D.naut.unr (D.naut.locG μ w) →
      D.naut.unr (D.naut.locG (D.naut.tw μ D.naut.etaTinv) w) := fun w h => by
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ _) h (D.naut.etaTinv_def w).1
  obtain ⟨hd0, hf0⟩ := hall w0 hg0 hs0
  have ha0 : p0.a = 1 := by
    have h1 := D.naut.frobEig_card _ (hg0.1.1 p0 hp0)
    rw [hf0, D.naut.frobEig_card _ (htu w0 hg0.1.2), D.naut.locG_dim, D.naut.locG_dim] at h1
    exact h1.symm
  obtain ⟨a, π', d⟩ := p0
  dsimp only at ha0 hd0 hall hp0
  subst ha0 hd0
  have hν : π' = D.naut.tw μ D.naut.etaTinv := by
    refine hL.one π' _ ?_
    filter_upwards [hgood] with w hw hs
    rw [D.naut.unr_eq_lpUnr _ (hw.1.1 _ hp0), (hall w hw hs).2, ← D.naut.unr_eq_lpUnr _ (htu w hw.1.2)]
  subst hν
  exact hp0
end GlobalTheory.MuBlockLoc
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_piece_mem_base_change : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ → SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa := by
  atlas_forward_decl _root_.GlobalTheory.MuBlockLoc.mu_block_mem_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowCuspFromLift
theorem exists_isCuspParam_of_liftAt_good_index : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa →
    D.nd.goodRow σ → ∃ π', GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.IsCuspParam D Rw σ π' := by
  intro D Rw hP j σ π μ Pa hL hR hB hm hg
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := hP.tie0.1
  have hAut : SumRepresentations.At.TieAut D.nd D.naut := hP.tie0.2.1
  have hC := hP.cancel
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  obtain ⟨hB1, -, hB3, hB4, hB5, hB6⟩ := hB
  have hpos : ∀ p ∈ twistIso D.nd D.naut L D.naut.etaT, 1 ≤ p.a ∧ 1 ≤ p.d := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hB1 q (hLmem q hq)).1, (hB1 q (hLmem q hq)).2.1⟩
  have hrank : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = D.R.r := by
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    have hr : rankIso D.nd D.naut (L ++ [m]) = D.R.nV := by
      rw [← hB3]; unfold rankIso; exact ((hperm.map _).sum_eq).symm
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hloc : ∀ w, IsSplitPl D.host w →
      isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have e1 := hB4 w hw
    rw [hL.loc w hw, GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append,
      (hLP w (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)
        (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w)
        (D.naut.locG_dim _ w)).1] at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [GlobalTheory.RowThetaParam.isoLoc_cons, GlobalTheory.RowThetaParam.isoLoc_nil, D.naut.lpSum_zero]
      exact GlobalTheory.RowThetaParam.spehLoc_tw D.nd D.naut hLP hC ⟨1, μ, D.R.t⟩ D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, e3,
      (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2]
  obtain ⟨π', hπ'⟩ := GlobalTheory.RowCuspLabels.cusp_of_goodRow D Rw hP.lab σ hg _ hpos hrank hloc
  obtain ⟨q, hLq, hq⟩ := List.map_eq_singleton_iff.1 (show L.map _ = _ from hπ')
  obtain ⟨a, ρ, d⟩ := q
  simp only [Formalism.BasicNotions.Part.mk.injEq] at hq
  obtain ⟨rfl, h2, rfl⟩ := hq
  have h2' := eq_of_heq h2
  subst h2'
  have hmemq : (⟨D.R.r, ρ, 1⟩ : Part D.naut.CG) ∈ l₁ ++ m :: l₂ := hLmem _ (by rw [hLq]; exact List.mem_singleton_self _)
  have hsplit : ∀ w, IsSplitPl D.host w → D.naut.locG (D.naut.tw ρ D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have hs := hloc w hw
    rw [hπ', SphericalInertData.isoLoc_single] at hs
    exact hs
  have hinf : ∀ τ : D.what₂.Tau, D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) ∧
      D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun z => -z) := by
    intro τ
    have eA := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)
    have eB := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).1] at eA
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).2] at eB
    have fA := add_right_cancel eA
    have fB := add_right_cancel eB
    rw [hLq, isoInf_one] at fA fB
    have gA := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1).1
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).2).symm.trans (hL.eta τ).1)
    have gB := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).1).2
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).2).symm.trans (hL.eta τ).2)
    rw [D.naut.infG_tw _ _ _ _ gA, D.naut.infG_tw _ _ _ _ gB, fA, fB]
    simp [Multiset.map_map, Function.comp_def]
  refine ⟨D.naut.tw ρ D.naut.etaT, D.naut.csd_tw ρ D.naut.etaT hAut.1.1 (hB1 _ hmemq).2.2, GlobalTheory.RowRegAlg.ralg_of_infG D _ hinf, hsplit,
    fun w hw => ?_, fun w hw hw' => ?_, hinf⟩
  · have hu := (hB5 w hw).1
    rw [GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.unr_sum, hLq,
      SphericalInertData.isoLoc_single] at hu
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu.1 (D.naut.etaT_unr w)
  · rw [hsplit w hw]
    exact (hR w hw hw').1
end GlobalTheory.RowCuspFromLift
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCuspParam_of_bc_good_index : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ → SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa → D.nd.goodRow σ → ∃ π', GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.IsCuspParam D Rw σ π' := by
  atlas_forward_decl _root_.GlobalTheory.RowCuspFromLift.exists_isCuspParam_of_liftAt_good_index
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.ParAsm
theorem goodRowCuspParam_of_lift_alt : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D →
    (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) →
    GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  intro D Rw hL h45 hEFK hCM hdef hLift hLoc j hj1 hj2 σ hiso hgood
  obtain ⟨π, μ, hπ⟩ := hLift j hj1 hj2 σ hiso
  obtain ⟨Pa, hPa⟩ := h45 hEFK hCM j hj1 hj2 (one_le_nV D) (hdef j hj1 hj2) π hπ.sph
  have hmu := _root_.GlobalTheory.T.trivial_piece_mem_base_change D Rw hL j σ π μ Pa hπ (hLoc σ) hPa
  exact _root_.GlobalTheory.T.exists_isCuspParam_of_bc_good_index D Rw hL j σ π μ Pa hπ (hLoc σ) hPa hmu hgood
end GlobalTheory.ParAsm
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspParam_of_definite_liftAll : ∀ (D : D7) (Rw : RowSide D), _root_.GlobalTheory.HeightCounting.Up.ParityLaws D → SphericalInertData.Conclusion1 D → SphericalInertData.HypEFK D → SphericalInertData.HypCM D → (∀ j, 1 ≤ j → j ≤ D.R.m → (D.sp.V j).IsDefinite) → LiftAll D Rw → (∀ σ, RowLoc D Rw σ) → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D Rw := by
  atlas_forward_decl _root_.GlobalTheory.ParAsm.goodRowCuspParam_of_lift_alt
end
end
