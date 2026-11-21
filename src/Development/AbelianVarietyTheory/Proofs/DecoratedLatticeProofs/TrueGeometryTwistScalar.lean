import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionEqOneOffSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackTwistPlaceProperty
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.moved_mat {k Z : Type} [Field k] [Fintype Z] [DecidableEq Z] {n : ℕ} (β : Matrix (Fin n) Z k) (γ : Matrix Z (Fin n) k) (hγβ : γ * β = 1) (x : Matrix Z Z k) (e : Z ≃ Fin n) : β * x * γ * β.submatrix id e.symm = β.submatrix id e.symm * x.submatrix e.symm e.symm := by
  rw [Matrix.submatrix_mul_equiv β x id e.symm e.symm, Matrix.mul_assoc (β * x)]
  have h1 : γ * β.submatrix id e.symm = (γ * β).submatrix id e.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hγβ]
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem GlobalTheory.TopLevQ.suppAt_conj {D : D7} {e : AE D} {V : HSp D} (g b : GA D V) (hg : Formalism.L2.Theta.SuppAt e V g) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hm : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl
  have h1 : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hm, inv_mul_cancel]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have key : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hm, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hg' : (e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
    ext i j; exact hg i j
  have h2 : (e + (cA D) e) • (Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b) =
      Formalism.L2.Theta.mt V b⁻¹ * ((e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1)) * Formalism.L2.Theta.mt V b := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hg'] at h2
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

theorem GlobalTheory.TopLevQ.blk_iff {K : Type} [Field K] [ValuativeRel K] {κ τ s n : ℕ}
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin n) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (x : Matrix (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) K) :
    (∀ i j : Fin n, Formalism.L2.DIV.blk2 (κ + (s + 1)) j < Formalism.L2.DIV.blk2 (κ + (s + 1)) i →
      ValuativeRel.valuation K (x (e.symm i) (e.symm j)) < 1) ↔ GlobalTheory.StepData.MaxM x.toBlocks₂₁ := by
  have hlo : ∀ a : Fin κ ⊕ Fin (s + 1), (e (Sum.inl a)).val < κ + (s + 1) := by
    intro a; rw [he]; rcases a with a | a <;> simp [GlobalTheory.SymBridge.zPos] <;> omega
  have hhi : ∀ p : Fin (s + 2) × Fin τ, κ + (s + 1) ≤ (e (Sum.inr p)).val := by
    intro p; rw [he]; simp only [GlobalTheory.SymBridge.zPos]; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  constructor
  · intro h p a
    have := h (e (Sum.inr p)) (e (Sum.inl a)) (by
      simp only [Formalism.L2.DIV.blk2, if_pos (hlo a), if_neg (Nat.not_lt.2 (hhi p))]; omega)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · intro h i j hij
    have hj : j.val < κ + (s + 1) := by
      by_contra hc
      simp only [Formalism.L2.DIV.blk2, if_neg hc] at hij
      split_ifs at hij <;> omega
    have hi : ¬ i.val < κ + (s + 1) := by
      intro hc
      simp only [Formalism.L2.DIV.blk2, if_pos hc, if_pos hj] at hij
      omega
    obtain ⟨p, hp⟩ : ∃ p, e.symm i = Sum.inr p := by
      rcases hi' : e.symm i with a | p
      · exfalso; apply hi; have := hlo a; rw [← hi', Equiv.apply_symm_apply] at this; exact this
      · exact ⟨p, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, e.symm j = Sum.inl a := by
      rcases hj' : e.symm j with a | p
      · exact ⟨a, rfl⟩
      · exfalso; have := hhi p; rw [← hj', Equiv.apply_symm_apply] at this; omega
    rw [hp, ha]
    exact h p a

theorem GlobalTheory.TopLevQ.mem_levS_iff {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (y : GA D V) :
    y ∈ levS V β L ↔ y ∈ GfC V ∧ ((Lev.finE V y ∈ Formalism.L2.DIV.St β ∧
        (∀ PP' ∈ L.Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        ∀ PP' ∈ L.Q, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r)) ∧
        Formalism.L2.DIV.rTup β L (Lev.finE V y) ∈ L.P.H) := by
  show y ∈ GfC V ⊓ Subgroup.comap (Lev.finE V) (Formalism.L2.DIV.lev _ _ β L) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  show _ ∧ (_ ∈ Formalism.L2.DIV.parLev _ _ _ _ ∧ _) ↔ _
  rw [Formalism.L2.DIV.mem_parLev]
  simp only [GlobalTheory.LevSplit.finE_mem_UA, true_and]

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.red_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) V t β N → (Formalism.L2.Theta.mt V h).map q.pr * N = N * M → Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β → ∀ i j, ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j = 0 ↔ ValuativeRel.valuation k (M i j) < 1) := by
  intro D k _ _ _ _ q PP hPP V β t h N M hN hM hSt i j
  constructor
  · intro h0
    have := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j 0 (by rw [h0, map_zero])
    have e0 : (GlobalTheory.LocMod.ofSplit q).pr ((0 : 𝓞 D.host.E) : D.host.E) = 0 := by
      show (GlobalTheory.LocMod.ofSplit q).π ((incA D) ((0 : 𝓞 D.host.E) : D.host.E)) = 0
      rw [show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, map_zero]
    rwa [e0, sub_zero] at this
  · intro hv
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j)
    have h1 := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j z hz
    have h2 : ValuativeRel.valuation k ((GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) < 1 := by
      have e : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = M i j - (M i j - (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
    obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
    have h6 : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
    rw [h6, ← hred.ker, Formalism.L2.DIV.resS_oToS] at h2
    rw [← hz, h2]

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.TopLevQ.mem_levS_top_iff : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (pk W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (chrK W t)), ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2)), ∀ g, (ofSplit (a.Q PP ⟨t, hP⟩).q).IsLoc (a.Q PP ⟨t, hP⟩).FT g x → (a.g.bT⁻¹ * g * a.g.bT ∈ levS _ (pk W).βX (datXP (pk W) (lvP W) t) ↔ x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha1 ha2 t PP hP E x hx g hg
  have hTop : x ∈ ((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).levTop.J ↔ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k _ ∧ GlobalTheory.StepData.MaxM x.val.toBlocks₂₁ := by
    show x ∈ ((GlobalTheory.StepData.parahoric _ _ E.δ E.tame).toLevel.map (GlobalTheory.StepData.LatFrame.refl _ _).conj).J ↔ _
    rw [GlobalTheory.StepData.Level.mem_map]
    have e1 : (GlobalTheory.StepData.LatFrame.refl (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.Ix (Fin (I.rec7 l Z).R.k ⊕ Fin ((a.Q PP ⟨t, hP⟩).s + 1)) (Fin (I.rec7 l Z).R.t) ((a.Q PP ⟨t, hP⟩).s + 2))).conj.symm x = x := by
      ext i j
      simp [GlobalTheory.StepData.LatFrame.conj, GlobalTheory.StepData.LatFrame.refl, GlobalTheory.StepData.reGL_symm_val]
      rfl
    rw [e1]
    exact GlobalTheory.StepData.mem_parahoric
  rw [hTop]
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frameTop
  have hmv' : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit (a.Q PP ⟨t, hP⟩).q) (I.rec7 l Z).sp.X' a.g.bT (pk W).βX
      ((a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm) := hmv
  have hidem : Formalism.L2.NTheta.IsIdemAt (a.Q PP ⟨t, hP⟩).q.e PP := (a.Q PP ⟨t, hP⟩).idem
  have hβX : Formalism.IndefR.Links.IsSDFrame (I.rec7 l Z).sp.X' (pk W).βX (pk W).ΛX 1 := W.Q.charW.base.lev.βX
  obtain ⟨hGfC, hStIff, hoff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff (I.rec7 l Z) (a.Q PP ⟨t, hP⟩).k (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX
    (pk W).ΛX 1 hβX _ (a.Q PP ⟨t, hP⟩).FT e.symm a.g.bT hmv' g x hg
  obtain ⟨hsupp, hmat⟩ := hg
  have hM : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr * (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm =
      (a.Q PP ⟨t, hP⟩).FT.β.submatrix id e.symm * x.val.submatrix e.symm e.symm := by
    have h1 : (Formalism.L2.Theta.mt _ g).map (a.Q PP ⟨t, hP⟩).q.pr = (a.Q PP ⟨t, hP⟩).FT.β * x.val * (a.Q PP ⟨t, hP⟩).FT.γ := hmat
    rw [h1]
    exact GlobalTheory.TopLevQ.moved_mat _ _ (a.Q PP ⟨t, hP⟩).FT.γβ _ e
  have hsupp' : Formalism.L2.Theta.SuppAt (a.Q PP ⟨t, hP⟩).q.e _ (a.g.bT⁻¹ * g * a.g.bT) := GlobalTheory.TopLevQ.suppAt_conj g a.g.bT hsupp
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Ranks.r
    omega
  have hPg := (GlobalTheory.PkFrame.pk_frame_places W hW t PP hP 0 (by have := (a.Q PP ⟨t, hP⟩).hs; omega)).2
  have hord := GlobalTheory.TopLevQ.blk_iff e he x.val
  rw [← hr] at hord
  rw [GlobalTheory.TopLevQ.mem_levS_iff]
  have hred := GlobalTheory.TopLevQ.red_eq_zero_iff (a.Q PP ⟨t, hP⟩).q PP hidem (I.rec7 l Z).sp.X' (pk W).βX a.g.bT g _ _ hmv' hM
  constructor
  · rintro ⟨-, ⟨hSt, -, hQt⟩, -⟩
    refine ⟨hx, hord.1 fun i j hij => (hred hSt i j).1 ?_⟩
    exact (hQt PP hP) hij
  · rintro ⟨hx', hmax⟩
    have hSt : Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT) ∈ Formalism.L2.DIV.St (pk W).βX := hStIff.2 hx'
    have hone : ∀ PP' : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E, PP'.under (𝓞 (I.rec7 l Z).host.F) ≠ PP.under (𝓞 (I.rec7 l Z).host.F) →
        Formalism.L2.DIV.redFn (pk W).βX PP' (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 :=
      fun PP' hne => GlobalTheory.SplitOffRed.redFn_eq_one_off (a.Q PP ⟨t, hP⟩).q hidem _ _ _ hsupp' hSt PP' hne
    refine ⟨hGfC, ⟨hSt, fun PP' hPP' => ?_, fun PP' hPP' => ?_⟩, ?_⟩
    · rw [hone PP' (hPg PP' hPP')]
      exact Subgroup.one_mem _
    · by_cases hPe : PP' = PP
      · subst hPe
        intro i j hij
        exact (hred hSt i j).2 (hord.2 hmax i j hij)
      · rw [hone PP' fun hu => hPe (hW.pk.sel PP' PP ⟨t, hPP'⟩ ⟨t, hP⟩ hu)]
        exact Subgroup.one_mem _
    · have h1 : Formalism.L2.DIV.rTup (pk W).βX (datXP (pk W) (lvP W) t) (Lev.finE (I.rec7 l Z).sp.X' (a.g.bT⁻¹ * g * a.g.bT)) = 1 := by
        funext PP'
        show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (pk W).βX PP'.1 _) = 1
        rw [hone PP'.1 (hPg PP'.1 PP'.2)]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
      rw [h1]
      exact Subgroup.one_mem _

end
end
