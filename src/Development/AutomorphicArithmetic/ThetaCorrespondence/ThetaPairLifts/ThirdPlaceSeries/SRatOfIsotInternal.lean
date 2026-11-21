import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SRatOfIsotInternal
import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsCAtState
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHeckeAtZeroOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalHeckeAtLevelsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalHeckeAtLevels
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterPsiConditionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterPsiCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeReadingEigenvaluePlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenspaceSpanOfIsotypicInternal

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeckeFamRead
theorem rationalHecke_allSt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke x.m.z.R.toRealDat i := by
  intro hL hD hT hR
  have hrat := GlobalTheory.HeckeFamRead.rat_side hT (GlobalTheory.T.heckeTransform_cuspForms_reads_cosetSum hD hR) GlobalTheory.T.exists_rationalHecke_read_as_cosetSums
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hId.and (ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x _ i
  obtain ⟨hHo, -⟩ := H.1.2 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  exact hrat (Dof x) (GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize) i
end GlobalTheory.HeckeFamRead
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalHecke_of_levelA : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke x.m.z.R.toRealDat i := by
  atlas_forward_decl _root_.GlobalTheory.HeckeFamRead.rationalHecke_allSt_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState
open Formalism.BasicNotions.TH Formalism.IndefR.Mult
section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end
end GlobalTheory.HeightCounting.RatSide.HeckeAtState
namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState
open Formalism.BasicNotions.TH Formalism.IndefR.Mult
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
end GlobalTheory.HeightCounting.RatSide.HeckeAtState
namespace GlobalTheory.HeightCounting.RatSide.HeckeAtState
theorem heckeAtState_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∃ hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j), StabC (SOf x) hL' ∧ (∀ j Pl, hL' j 0 Pl = 1) ∧ HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' := by
  intro hL hD hT hR
  refine (_root_.GlobalTheory.T.rationalHecke_of_levelA hL hD hT hR).trans (StepW.of_all fun K B f T w _ _ H P x l => ?_)
  exact exists_heckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) (H P x l) (GlobalTheory.T.isGoodSplitHeckePlace_of_split_not_excluded P x)
end GlobalTheory.HeightCounting.RatSide.HeckeAtState
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RatHeckeBall
set_option maxHeartbeats 1600000 in
theorem ratHecke_keeps_ball_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  intro hLL hDec hI hT hRT
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hId : StepW Start Start := StepW.of_all fun _ _ _ _ _ _ _ h => h
  refine ((hId.and (ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev)).trans
    (StepW.of_all fun K B f T w hO _ H => ?_)
  intro P x _ hL' hstab hRd j k v hj1 hj2 hsp hPS hk la hla g hg hhg hball
  obtain ⟨hHo, -⟩ := H.1.2 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := H.2 (w.st x.o.Z) hO
  have hfin : Finite (TupU w.I (usedOf w.I T P.Wt)) := by
    have hs : ({τ | τ = (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T P.Wt))).1 ∨ τ ∈ tuOf w.I (usedOf w.I T P.Wt)} :
        Set _).Finite :=
      (Set.finite_singleton _).union (tuOf w.I (usedOf w.I T P.Wt)).finite_toSet
    exact hs.to_subtype
  let X := GlobalTheory.TwInputs.RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo hfin hHo hStd hSize
  have hS := GlobalTheory.T.heckeOperator_preserves_supLattice_realSide hDec hI hT hRT (Dof x) X (idxOf (Dof x) j)
  have hlow : ∀ p ∈ lowAll (Dof x), p ≠ 0 → ((p : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro p hp hp0 hm
    apply hPS
    rw [SbD, Set.Finite.mem_toFinset]
    exact ⟨p, hp, hp0, hm⟩
  have hgP : ∀ kk : Fin 2, (((Dof x).host.g kk : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := fun kk =>
    hlow _ (by fin_cases kk <;> simp [lowAll]) ((Dof x).host.g_prime kk).ne_zero
  have hso : Bridge.SplitOff v (X.R.Sb : Set (Formalism.L2.DIV.Pl (Dof x).host.E)) := by
    have hAll : X.R.Sb = X.R.Pg := X.char.allPl
    have hPg := X.char.lev.Pg
    refine ⟨(GlobalTheory.HeckeTieCompare.isSplitPl_iff v).1 hsp, fun h => ?_, fun Q hQ h => ?_⟩
    · rw [Finset.mem_coe, hAll] at h
      obtain ⟨kk, hkk⟩ := (hPg v).1 h
      exact hgP kk (GlobalTheory.StepLaw.typePrime_mem_of_div hkk)
    · rw [Finset.mem_coe, hAll] at hQ
      obtain ⟨kk, hkk⟩ := (hPg Q).1 hQ
      have hm := GlobalTheory.StepLaw.typePrime_mem_of_div hkk
      rw [h, Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.mem_conjP, map_natCast] at hm
      exact hgP kk hm
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt X.char.lev X.char.fam (idxOf (Dof x) j) hso hk
  have hg01 : (((Dof x).host.g 0 * (Dof x).host.g 1 : ℕ) : 𝓞 (Dof x).host.E) ∉ v.asIdeal := by
    intro hm
    rw [Nat.cast_mul] at hm
    rcases v.isPrime.mem_or_mem hm with h | h
    exacts [hgP 0 h, hgP 1 h]
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData X.R.toRealDat (idxOf (Dof x) j) v k α Rc := ⟨hso, hg01, hk, ha, hR⟩
  have hkd : HkDat x.m.z.R (SbD (Dof x)) (idxOf (Dof x) j) k v α Rc :=
    ⟨hsp, hPS, hlow 2 (by simp [lowAll, lowPr]) two_ne_zero, hk, ha, hR⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC X.R.toRealDat (idxOf (Dof x) j) v k = hkNorm x.m.z.R (idxOf (Dof x) j) k v := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC, hkNorm, inv_pow]
    all_goals rfl
  have hK := hS v k α Rc hd (hL' j k v) (fun y => by rw [e]; exact hRd j k v α Rc hj1 hj2 hkd y)
    (fun y hy => hstab j hj1 hj2 k v y hy) la hla
  exact hK.sup ⟨g, hg⟩ hball
end GlobalTheory.RatHeckeBall
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_reading_eigenvalue_place_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ (j k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ j → j ≤ (Dof x).R.m → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → k ≤ (Dof x).R.r → ∀ la : HeightOneSpectrum (𝓞 (SOf x).Ks), (∀ q : ℕ, q.Prime → (q : 𝓞 (Dof x).host.E) ∈ Pl.asIdeal → (q : 𝓞 (SOf x).Ks) ∉ la.asIdeal) → ∀ (f : (SOf x).WL j) (hf : f ∈ ((SOf x).A j).WK) (hg : hL' j k Pl f ∈ ((SOf x).A j).WK), (∀ y, ((SOf x).A j).nrm la y ⟨f, hf⟩ ≤ 1) → ∀ y, ((SOf x).A j).nrm la y ⟨hL' j k Pl f, hg⟩ ≤ 1 := by
  atlas_forward_decl _root_.GlobalTheory.RatHeckeBall.ratHecke_keeps_ball_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide
set_option maxHeartbeats 1600000 in
theorem intC_of_lvlPsi_stabC_heckeRd : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → IntC (SOf x) (SbD (Dof x)) θ hL' := by
  intro hL hDec hI hT hRT
  refine ((_root_.GlobalTheory.T.hecke_reading_eigenvalue_place_alt hL hDec hI hT hRT).and (_root_.GlobalTheory.HeightCounting.RatSide.formsC_at_state_alt hL)).trans
    (StepW.of_all fun K B f T w _ _ H P x hA θ hL' _ hstab hrd => ?_)
  obtain ⟨hB, hF⟩ := H
  intro j k Pl hj1 hj2 hsp hnot hk
  obtain ⟨-, -, Tf, hTf, hMK, hspan⟩ := hF P x hA j hj1 hj2
  obtain ⟨p, hp, hpP, hpN⟩ := GlobalTheory.SupPowNorm.exists_prime_dvd_card Pl
  have hW : ∀ y ∈ ((SOf x).A j).WK, hL' j k Pl y ∈ ((SOf x).A j).WK := fun y hy => hstab j hj1 hj2 k Pl y hy
  obtain ⟨n, hn⟩ := GlobalTheory.SupPowNorm.exists_pow_smul_mem_span ((SOf x).A j) (hL' j k Pl) Tf hTf
    (fun y hy => (hMK y hy).2) hspan hW hp hpN fun la hla g hg hb y =>
      hB P x hA hL' hstab hrd j k Pl hj1 hj2 hsp hnot hk la
        (fun q hq hqP => by rw [GlobalTheory.SupPowNorm.prime_eq_of_mem Pl hq hp hqP hpP]; exact hla) g hg (hW g hg) hb y
  exact ⟨n, fun y hy _ => hn y hy⟩
end GlobalTheory.HeightCounting.RatSide
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intC_state_of_lvlPsi_stabC_heckeRd : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → IntC (SOf x) (SbD (Dof x)) θ hL' := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.RatSide.intC_of_lvlPsi_stabC_heckeRd
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting
  GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 2000000
namespace GlobalTheory.HeightCounting.RatSide
theorem sRat_of_isotInternal_alt_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL := by
  intro hp hs hi hL
  have A := StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.formsC_at_state_alt hL) (StepW.and (_root_.GlobalTheory.HeightCounting.ThetaSt.main_alt_alt hL)
    (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.HeckeAtState.heckeAtState_alt hL hp.decay hs.hkTr hs.hkRead)
    (StepW.and (_root_.GlobalTheory.T.intC_state_of_lvlPsi_stabC_heckeRd hL hp.decay hs.hkInt hs.hkTr hs.hkRead) (_root_.GlobalTheory.HeightCounting.RatSide.eigenspace_span_of_isotypicInternal_alt hp hi hL))))
  refine StepW.trans A (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx
  obtain ⟨hF, hθ, hH, hI, hE⟩ := H
  obtain ⟨θ, θne, hlp⟩ := hθ P x hx
  obtain ⟨hL', hst, h0, hrd⟩ := hH P x hx
  obtain ⟨eig, hea, hsp⟩ := hE P x hx θ hL' θne hlp hst h0 hrd
  have hint := hI P x hx θ hL' hlp hst hrd
  have hrc := GlobalTheory.Mem.RatDatRExp.rhoStab_chiInLL0 (Dof x) _ _ _ _ _ x.m.z.core x.m.z.R x.m.z.F x.m.z.cG x.m.z.geo (kKsOf x)
    (hkOf x) x.m.z.pins x.m.inGeo
  exact ⟨⟨kKsOf x, hkOf x,
    { Sb := SbD (Dof x)
      rho := fun j a b => (hrc j a b).1
      chi := fun j a b => (hrc j a b).2
      ks := fun j a b => (hF P x hx j a b).1
      fd := fun j a b => (hF P x hx j a b).2.1
      mk_fg := fun j a b => (hF P x hx j a b).2.2
      hL := hL'
      hs := hst
      hL_zero := h0
      θ := θ
      θ_ne := θne
      eig := eig
      span := hsp
      hL_int := hint },
    { hecke := hrd
      eig := hea
      Sb_le := overSet_SbD _
      lvl := hlp.1
      psi := hlp.2 }⟩⟩
theorem sRat_of_isotInternal_inputs : GlobalTheory.Published.DiscreteSeriesUpqUnique → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN →
    (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL :=
  fun _ => _root_.GlobalTheory.HeightCounting.RatSide.sRat_of_isotInternal_alt_alt
end GlobalTheory.HeightCounting.RatSide
end
end
end
end
