import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostExOfPublished
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBaseOfRich
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.SplitGen

theorem exists_places {R : Ranks} (H : Host R) {p : ℕ} (hp : p.Prime) (hc : p % (H.QS * H.q * H.d) = 1)
    (ι : Type) [Fintype ι] (hι : Fintype.card ι = R.f) :
    ∃ φ : ι → HeightOneSpectrum (𝓞 H.F), Function.Injective φ ∧ ∀ v, (p : 𝓞 H.F) ∈ (φ v).asIdeal := by
  have h1 := Formalism.MainNotions.Gaps.LevGap.split_F H p hp (GlobalTheory.HostSplit.split_of_one_mod R H p hp hc).1
  have hpos : 0 < Module.finrank ℚ H.F := Module.finrank_pos
  have hfin : {v : HeightOneSpectrum (𝓞 H.F) | (p : 𝓞 H.F) ∈ v.asIdeal}.Finite :=
    Set.finite_of_ncard_pos (by rw [h1]; exact hpos)
  haveI := hfin.to_subtype
  have h2 : Nat.card ι = Nat.card {v : HeightOneSpectrum (𝓞 H.F) | (p : 𝓞 H.F) ∈ v.asIdeal} := by
    rw [Nat.card_coe_set_eq, h1, Formalism.MainNotions.Gaps.LevGap.finrank_F, Nat.card_eq_fintype_card, hι]
  obtain ⟨e⟩ := Finite.card_eq.1 h2
  exact ⟨fun v => (e v).1, Subtype.val_injective.comp e.injective, fun v => (e v).2⟩

theorem nonempty_errX : ∀ X : Stages, (∀ i, ∃ π : 𝓞 X.B.host.E, (π : X.B.host.E) ∈ X.B.host.K ∧
    (π : X.B.host.E) * X.B.host.conj (π : X.B.host.E) = (X.B.host.g i : X.B.host.E)) → Nonempty (ErrX X.toD7) := by
  intro X h
  choose pG hG1 hG2 using h
  choose pT hT1 hT2 hT3 using X.toD7.T_norm
  have hv : ∀ u, ∃ φ : (X.toD7.mem u).A.vT → HeightOneSpectrum (𝓞 X.toD7.host.F), Function.Injective φ ∧
      ∀ v, ((X.toD7.mem u).A.T : 𝓞 X.toD7.host.F) ∈ (φ v).asIdeal := by
    intro u
    letI := (X.toD7.mem u).A.vTFin
    refine exists_places X.toD7.host (X.toD7.mem u).A.T_prime ?_ _ (X.toD7.mem u).A.card_vT
    have h1 : (X.toD7.mem u).A.T = X.B.T u := X.C.A_T u
    rw [h1]
    exact X.B.T_cond u
  choose φ hφ1 hφ2 using hv
  exact ⟨⟨pG, hG1, hG2, pT, hT1, hT2, hT3, φ, hφ1, hφ2⟩⟩

end GlobalTheory.SplitGen
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.error_data_of_norm_generators : ∀ X : Stages, (∀ i, ∃ π : 𝓞 X.B.host.E, (π : X.B.host.E) ∈ X.B.host.K ∧ (π : X.B.host.E) * X.B.host.conj (π : X.B.host.E) = (X.B.host.g i : X.B.host.E)) → Nonempty (ErrX X.toD7) := by
  atlas_forward_decl GlobalTheory.SplitGen.nonempty_errX
end

section
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

namespace GlobalTheory.StandInStages

def reweight {B : Base} {C : Cols B} (W : RowsRest B C) (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ)
    (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ) : RowsRest B C :=
  { W with kaBig := kb, kaSmall := ks, Ij := fun _ _ _ => 0, jw := fun _ _ _ => 0 }

def retol {B : Base} {C : Cols B} {W : RowsRest B C} (V : DivStage B C W) (η : ℝ) : DivStage B C W :=
  { V with div := { V.div with etaF := η } }

theorem exists_stages_blocks (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ) (D : ℕ)
    (hD : 0 < Del) (hinj : Function.Injective letter)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1),
      (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0))
    (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ) :
    ∃ (C : Cols B) (W : RowsRest B C) (V : DivStage B C W) (S : SStage B C W) (_ : NStage B C W)
      (G : GJStage B C), S.s.Del = Del ∧ S.s.letter = letter ∧ V.div.etaF = η ∧ W.kaBig = kb ∧ W.kaSmall = ks ∧
      (∀ μ j w, W.Ij μ j w = 0) ∧ (∀ μ j w, W.jw μ j w = 0) ∧ W.Drows = D ∧ W.Dall = D ∧
      (∀ u, Nontrivial (W.Mu u)) ∧ (∀ u i, Nonempty ((C.mem u).C.cls i)) ∧ Nonempty G.jet.Sit := by
  obtain ⟨W₀, h1, h2, h3⟩ := StagesInhab.exists_rows B D
  let W := reweight W₀ kb ks
  have hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i) :=
    fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S, hS, hl, -⟩ := SStageInhab.exists_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => (StagesInhab.ipC_conj B u y x).symm) (fun u x _ h => StagesInhab.ipC_pos B u x h)
    (show W₀.Drows ≤ W₀.Dall by omega)
  obtain ⟨G, -, hG⟩ := (GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)
  exact ⟨_, GaloisStage.adapt W, retol V η, S, N, G, hS, hl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    h1, h2, h3, hc, hG⟩

theorem exists_stages_kapDef (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ) (D : ℕ)
    (hD : 0 < Del) (hinj : Function.Injective letter)
    (gap : ∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1),
      (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del)
    (hu : ∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ =
      (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) :
    ∃ X : Stages, X.B = B ∧ X.toD7.s.Del = Del ∧ X.toD7.div.etaF = η ∧ DV.KapDef X.toD7 ∧
      (∀ w j, X.toD7.what₂.Aj j w = 0) ∧ X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨C₀, W₀, V₀, S₀, N₀, G₀, -⟩ :=
    exists_stages_blocks B Del letter η D hD hinj gap hu (fun _ _ _ => 0) (fun _ _ _ => 0)
  obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C₀ W₀ V₀ S₀ N₀ G₀)
  obtain ⟨C, W, V, S, N, G, a1, -, a2, a3, a4, a5, a6, a7⟩ :=
    exists_stages_blocks B Del letter η D hD hinj gap hu kb ks
  refine ⟨⟨B, C, W, V, S, N, G⟩, rfl, a1, a2, fun j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩, fun w j => ?_, a7⟩
  · exact (congrArg (fun f => ((f j τ i : ℤ) : ℚ)) a3).trans ((hk j τ).1 i)
  · exact (congrArg (fun f => ((f j τ c : ℤ) : ℚ)) a4).trans ((hk j τ).2 c)
  · exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (a5 _ _ _) (a5 _ _ _)) (a6 _ _ _)

theorem exists_stages_prescribed : ∀ (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ), 0 < Del → 0 < η → Function.Injective letter → (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) → (∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) → ∃ X : Stages, X.B = B ∧ X.toD7.s.Del = Del ∧ X.toD7.div.etaF = η ∧ DV.KapDef X.toD7 ∧ ∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0 := by
  intro B Del letter η hD _ hinj gap hu
  obtain ⟨X, h1, h2, h3, h4, h5, -⟩ := exists_stages_kapDef B Del letter η 1 hD hinj gap hu
  exact ⟨X, h1, h2, h3, h4, fun w _ j _ _ => h5 w j⟩

end GlobalTheory.StandInStages

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stages_with_delta : ∀ (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ), 0 < Del → 0 < η → Function.Injective letter → (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) → (∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) → ∃ X : Stages, X.B = B ∧ X.toD7.s.Del = Del ∧ X.toD7.div.etaF = η ∧ DV.KapDef X.toD7 ∧ ∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0 := by
  atlas_forward_decl GlobalTheory.StandInStages.exists_stages_prescribed
end

section
noncomputable section

namespace GlobalTheory.FinalJoin2

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
open GlobalTheory.FieldSize GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.Pj Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons GlobalTheory.RunJoin
open GlobalTheory.Mem
open GlobalTheory.EX.OB

theorem exists_window_start (N y G : ℝ) (hN : 0 < N) (hG : 0 < G) : ∃ Ds : ℝ, 0 < Ds ∧
    y ≤ Real.log ((Ds / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / N) * G ^ (-(2 : ℝ) / N)) := by
  refine ⟨Real.exp (N * y + 2 * Real.log G), Real.exp_pos _, le_of_eq ?_⟩
  rw [Nat.cast_one, div_one, ← Real.exp_mul, Real.rpow_def_of_pos hG, ← Real.exp_add, Real.log_exp]
  field_simp
  ring

set_option maxHeartbeats 1000000 in

theorem exists_record_over_choices (hR : GlobalTheory.NT.RayField) (eps cD ch : ℝ) (C : FC) (h0 : 0 < eps) (h1 : eps < 1 / 52)
    (hC : Std C) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ)
      (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P), s.eps = eps → x0 ≤ s.x →
      ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R →
      ∃ D : D7, JointQ D ∧ Nonempty (ErrX D) ∧ DV.KapDef D ∧ HostArith D.host ∧
        ∃ L : SizeData₂ D, L.sc = s ∧ Val C cD ch L := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv hs hx hP hG
  obtain ⟨F, hfd, hrich, hsz⟩ := exists_rich_small_of_rayField hR (StdFrameObj.coordPre P Lv)
  obtain ⟨B, hB, hF, -⟩ := exists_base_of_rich _ F hfd hrich ∅ ∅ (by simp) (by simp)
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hDel : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < Delv s cD := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast this
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (StdFrameObj.coordPre P Lv).level_split
  have key : ∀ Q : Pre, Q = StdFrameObj.coordPre P Lv → ∃ letter : Q.Word → Fin (Q.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ w τ (l : ℕ) (h : l + 1 < Q.R.k - 1),
        (Q.hcW w τ).v ⟨l, by omega⟩ - (Q.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv s cD : ℚ)) ∧
      ∀ w τ (l : ℕ) (h : l < Q.R.k - 2), (Q.hcW w τ).u ⟨l + 1, by omega⟩ =
        (Q.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv s cD : ℚ) else 0) := by
    rintro Q rfl
    refine ⟨c, hP.inj, fun w τ l h => ?_, fun w τ l h => hP.code w τ l h⟩
    have h' : l + 1 < P.R.k - 1 := h
    have a1 := (hP.hc w).1 τ ⟨l, by omega⟩
    have a2 := (hP.hc w).1 τ ⟨l + 1, h'⟩
    refine (congrArg₂ (· - ·) a1 a2).trans ?_
    have : P.R.k - 2 - l = (P.R.k - 2 - (l + 1)) + 1 := by omega
    simp only [this]
    push_cast
    ring
  obtain ⟨letter, k1, k2, k3⟩ := key B.toPre hB
  obtain ⟨X, rfl, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_stages_with_delta B (Delv s cD : ℚ) letter (6 * s.x ^ (-C.P.CF)) hDel (by positivity) k1 k2 k3
  clear key k1 k2 k3 letter
  have hJ : JointQ X.toD7 := jointQ_of_small_field X F (hB ▸ hrich)
    ((congrArg (fun Q : Pre => ∀ L : ℝ, HostSz Q.host L → Sz F (poR Q.R L) (poR Q.R L)) hB).mpr hsz) hF
  have hE : Nonempty (ErrX X.toD7) := GlobalTheory.T.error_data_of_norm_generators X
    ((congrArg (fun Q : Pre => ∀ i, ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E)) hB).mpr hP.arith.1)
  clear hF hrich hsz
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  refine ⟨D, hJ, hE, e3, ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_⟩
  obtain ⟨L, l1, -, -, l4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog e1 hP.ct2
    hP.card e2 (fun u => by
      have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
      rw [e, hG, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) e4
  exact ⟨L, l1, l4⟩

end GlobalTheory.FinalJoin2

end
end
