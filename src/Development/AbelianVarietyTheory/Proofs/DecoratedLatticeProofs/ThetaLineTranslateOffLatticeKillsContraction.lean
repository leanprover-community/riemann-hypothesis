import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionLeClosureIsotropicHalves
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineSimilitudeMapsSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionAAScaledEqAtUnitSplitPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineMultipleMemSplitCoreLatticeCompletionIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLinkKappaPreservesSupportedMatrices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawCombinationsOperatorDatum

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LineProj

open GlobalTheory.IwaPlace

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {π : Mx D S.rank S.rank} (h : adj π ⬝ gA S = gA S ⬝ π) (x y : Fin S.rank → AE D) :
    hermAt S (π *ᵥ x) y = hermAt S x (π *ᵥ y) := by
  have e : (fun i => cA D ((π *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj π := by
    funext i
    rw [adj, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec (cA D) π y i
  have e2 : gA S *ᵥ (π *ᵥ x) = adj π *ᵥ (gA S *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact congrArg (· *ᵥ x) h.symm
  rw [hermAt_eq, hermAt_eq, e, e2]
  exact Matrix.dotProduct_mulVec _ _ _

theorem hermAt_smul (S : HSp D) (a : AE D) (x y : Fin S.rank → AE D) :
    hermAt S (a • x) y = hermAt S x (cA D a • y) := by
  simp only [hermAt, Pi.smul_apply, smul_eq_mul, map_mul, GlobalTheory.DualPairCheck.cA_cA]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermAt_add_left (S : HSp D) (x x' y : Fin S.rank → AE D) :
    hermAt S (x + x') y = hermAt S x y + hermAt S x' y := by
  simp only [hermAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem add_mem_intAt {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add]; exact add_mem ha.2 hb.2⟩

theorem proj_selfAdj {S A L : HSp D} (o : OrthDec S A L) :
    adj (o.jB ⬝ o.pB) ⬝ gA S = gA S ⬝ (o.jB ⬝ o.pB) := by
  rw [o.pB_eq]
  simp only [adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_mem_of_half (p : SplitPt D k) {S : HSp D} {M : Lat S} (hM : IsSelfDualC S M) {π : Mx D S.rank S.rank}
    (h : adj π ⬝ gA S = gA S ⬝ π)
    (hw : ∀ z ∈ latV S M (· = p.v), π *ᵥ (p.e • z) ∈ latV S M (· = p.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S M (· = p.v)) : π *ᵥ y ∈ latV S M (· = p.v) := by
  obtain ⟨hs, -, hd⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M p.v hM
  refine (hd _ (mulVec_mem_idAt π (hs y hy))).2 fun x hx => ?_
  have hy' : y = p.e • y + cA D p.e • y := by
    funext i
    rw [← add_smul, Pi.smul_apply, smul_eq_mul]
    exact ((FrameLat.idem_iff p (y i)).1 (hs y hy i)).symm
  rw [hy', Matrix.mulVec_add, hermAt_add_left]
  refine add_mem_intAt ((hd _ (hs _ (hw y hy))).1 (hw y hy) x hx) ?_
  rw [hermAt_mulVec S h, hermAt_smul, GlobalTheory.DualPairCheck.cA_cA, ← Matrix.mulVec_smul]
  exact (hd y (hs y hy)).1 hy _ (hw x hx)

theorem proj_frame {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    (x : n ⊕ Fin 1 → k) :
    (o.jB ⬝ o.pB).map p.pr *ᵥ (α₀.b *ᵥ x) = α₀.b *ᵥ Sum.elim 0 (x ∘ Sum.inr) := by
  have h1 : (o.jB ⬝ o.pB).map p.pr * o.jA.map p.pr = 0 := by
    rw [← Matrix.map_mul, Matrix.mul_assoc, o.pB_jA, Matrix.mul_zero]
    exact Matrix.map_zero _ (map_zero _)
  have h2 : (o.jB ⬝ o.pB) *ᵥ ratV (vecB o ζ) = ratV (vecB o ζ) := by
    have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
      funext i
      exact RingHom.map_mulVec (incA D) o.iB ζ i
    rw [e, Matrix.mulVec_mulVec, Matrix.mul_assoc, o.pB_jB, Matrix.mul_one]
  have h3 : (o.jB ⬝ o.pB).map p.pr *ᵥ (fun i => p.pr (ratV (vecB o ζ) i)) = fun i => p.pr (ratV (vecB o ζ) i) := by
    funext i
    have := RingHom.map_mulVec p.pr (o.jB ⬝ o.pB) (ratV (vecB o ζ)) i
    rw [h2] at this
    exact this.symm
  rw [IsSumFrame] at h
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_fromCols, ← Matrix.mul_assoc, h1, Matrix.zero_mul,
    ← Matrix.replicateCol_mulVec, h3, Matrix.fromCols_mulVec, Matrix.fromCols_mulVec_sumElim, Matrix.zero_mulVec,
    Matrix.mulVec_zero]

theorem proj_half {p : SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {S A L : HSp D} (o : OrthDec S A L)
    (ζ : Fin L.rank → D.host.E) {α : Frame p A n} {α₀ : Frame p S (n ⊕ Fin 1)} (h : IsSumFrame o ζ α α₀)
    {M : Lat S} {Λ : Submodule 𝒪[k] (n → k)} (hΛ : α₀.IsLat M (lastKer Λ)) {z : Fin S.rank → AE D}
    (hz : z ∈ latV S M (· = p.v)) : (o.jB ⬝ o.pB) *ᵥ (p.e • z) ∈ latV S M (· = p.v) := by
  have hb : α₀.b *ᵥ (α₀.b' *ᵥ fun i => p.pr (z i)) = fun i => p.pr (z i) := by
    rw [Matrix.mulVec_mulVec, α₀.bb', Matrix.one_mulVec]
  have h1 : (α₀.b' *ᵥ fun i => p.pr (z i)) ∈ lastKer Λ := by
    refine (hΛ _).2 ?_
    rw [hb]
    simp only [p.sec_pr]
    exact GlobalTheory.FinPlLoc.smul_latV p.v (FrameLat.e_mem_intAt p) hz
  have h2 : (Sum.elim 0 ((α₀.b' *ᵥ fun i => p.pr (z i)) ∘ Sum.inr) : n ⊕ Fin 1 → k) ∈ lastKer Λ :=
    GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨Λ.zero_mem, (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 h1).2⟩
  have h3 := (hΛ _).1 h2
  rw [← proj_frame o ζ h, hb] at h3
  convert h3 using 1
  funext i
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, ← p.sec_pr, RingHom.map_mulVec]
  rfl

theorem lineProj_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ B S α α₀ M LS Λ hM hLS h x hx
  have hπ : ∀ y ∈ latV B.V₀ M P, (B.o.jB ⬝ B.o.pB) *ᵥ y ∈ latV B.V₀ M P := by
    intro y hy
    refine (GlobalTheory.FinPlLoc.part_lat P B.V₀ M _ hM.1).2 ⟨mulVec_mem_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
    obtain ⟨i, rfl⟩ := (hP.mem v).1 hv
    rw [← Matrix.mulVec_smul]
    exact mulVec_mem_of_half (p i) hM (proj_selfAdj B.o) (fun z hz => proj_half B.o B.ζ (h i).1 (h i).2 hz)
      (GlobalTheory.FinPlLoc.smul_latV _ he hy)
  obtain ⟨hx1, hx2⟩ := (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P x).1 hx
  have e : (B.o.resS S).symm (0, (B.o.resS S x).2) = x ⬝ (B.o.jB ⬝ B.o.pB) := by
    rw [OrthDec.resS_symm_apply, OrthDec.resS_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc]
  rw [e]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D B.V₀ S M LS hM hLS P _).2 ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx1 i l)
  · have := hx2 _ (hπ y hy)
    rwa [Matrix.mulVec_mulVec] at this

end GlobalTheory.LineProj
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineProjection_mem_homLatticeCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x ∈ latO B.V₀ S (M : Set _) (LS : Set _) P, (B.o.resS S).symm (0, (B.o.resS S x).2) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P := by
  atlas_forward_decl GlobalTheory.LineProj.lineProj_mem_latO
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SplitHalves

variable {D : D7}

theorem sum_idem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    {p : ι → SplitPt D k} {I : List ι} {P : Pl D → Prop} [DecidableEq ι] (hP : Places p I P) :
    ∑ i ∈ I.toFinset, GlobalTheory.FinPlLoc.idem D (· = (p i).v) = GlobalTheory.FinPlLoc.idem D P := by
  classical
  rw [← sub_eq_zero]
  apply GlobalTheory.FinPlLoc.eq_zero_of_comp
  · rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.infPart_pair, Finset.sum_const_zero, sub_zero]
  · intro w
    rw [map_sub, map_sum]
    simp only [GlobalTheory.FinPlLoc.compAt_idem]
    by_cases hw : P w
    · obtain ⟨j, rfl⟩ := (hP.mem w).1 hw
      rw [Finset.sum_eq_single j (fun i _ hij => if_neg (fun h => hij (hP.inj h.symm)))
        (fun hj => absurd (List.mem_toFinset.2 (hP.all j)) hj), if_pos rfl, if_pos hw, sub_self]
    · rw [Finset.sum_eq_zero (fun i _ => if_neg (fun h => hw ((hP.mem w).2 ⟨i, h⟩))), if_neg hw, sub_self]

theorem mem_intAt_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  intro D k _ _ _ _ ι p I P hP a
  classical
  have hsec1 : ∀ i, (p i).sec 1 ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff (p i) 1 1).2 (by simp)
  have hcsec1 : ∀ i, cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := fun i => by
    simpa using (GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff (p i) 1 1).2 (by simp)
  constructor
  · intro h
    have hr := (GlobalTheory.IwaIdeals.mem_intAt_iff.1 h).2
    refine ⟨h.1, fun i => ⟨?_, ?_⟩⟩
    · have h1 : a * (p i).sec 1 ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hsec1 i)).2⟩
      simpa using (GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff (p i) a 1).1 h1
    · have h1 : a * cA D ((p i).sec 1) ∈ intAt D (· = (p i).v) := GlobalTheory.IwaIdeals.mem_intAt_iff.2
        ⟨Ideal.mul_mem_left _ _ (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1),
          mul_mem hr (GlobalTheory.IwaIdeals.mem_intAt_iff.1 (hcsec1 i)).2⟩
      simpa using (GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff (p i) a 1).1 h1
  · rintro ⟨hid, hh⟩
    refine ⟨hid, ?_⟩
    have ha : a = ∑ i ∈ I.toFinset, (a * (p i).sec 1 + a * cA D ((p i).sec 1)) := by
      conv_lhs => rw [← (GlobalTheory.FinPlLoc.mem_idAt_iff P a).1 hid, ← sum_idem hP, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      set ε := GlobalTheory.FinPlLoc.idem D (· = (p i).v)
      have h1 : ε * a ∈ idAt D (· = (p i).v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
      have h2 := (GlobalTheory.FinPl.FrameLat.idem_iff (p i) _).1 h1
      have he : ε * (p i).sec 1 = (p i).sec 1 :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.sec_mem_idAt _ _)
      have hce : ε * cA D ((p i).sec 1) = cA D ((p i).sec 1) :=
        (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPl.FrameLat.csec_mem_idAt (p := p i) 1)
      rw [GlobalTheory.FinPl.FrameLat.sec_one] at he hce ⊢
      calc ε * a = ((p i).e + cA D (p i).e) * (ε * a) := h2.symm
        _ = (ε * (p i).e) * a + (ε * cA D (p i).e) * a := by
          rw [add_mul, mul_left_comm, ← mul_assoc, mul_left_comm (cA D (p i).e), ← mul_assoc]
        _ = a * (p i).e + a * cA D (p i).e := by rw [he, hce, mul_comm (p i).e, mul_comm (cA D (p i).e)]
    rw [ha, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_add]
    exact add_mem ((GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff (p i) a 1).2 (by simpa using (hh i).1)).2
      ((GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff (p i) a 1).2 (by simpa using (hh i).2)).2

end GlobalTheory.FinPl.SplitHalves

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ a : AE D, a ∈ intAt D P ↔ a ∈ idAt D P ∧ ∀ i, (p i).pr a ∈ 𝒪[k] ∧ (p i).pr (cA D a) ∈ 𝒪[k] := by
  atlas_forward_decl GlobalTheory.FinPl.SplitHalves.mem_intAt_iff_halves
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 400000

namespace GlobalTheory.FinPl.ScalarDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl.FrameLat

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w =>
    (Submodule.mem_iInf _).1 hw ⟨w.1, fun hp => w.2 (hPQ _ hp)⟩⟩

theorem pr_eq_zero (q : SplitPt D k) {w : Pl D} (hw : w ≠ q.v) {a : AE D} (ha : a ∈ idAt D (· = w)) : q.pr a = 0 := by
  have h1 : q.e * a ∈ idAt D (· = w) := Ideal.mul_mem_left _ _ ha
  have h2 : q.e * a ∈ idAt D (· = q.v) := Ideal.mul_mem_right _ _ (e_mem_idAt q)
  unfold idAt at h1 h2
  have h0 : q.e * a = 0 := by
    apply GlobalTheory.FinPlLoc.eq_zero_of_comp
    · exact RingHom.mem_ker.1 (Ideal.mem_inf.1 h1).1
    · intro u
      by_cases hu : u = w
      · subst hu
        exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h2).2 ⟨u, hw⟩)
      · exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h1).2 ⟨u, hu⟩)
  rw [← q.pr_sec (q.pr a), q.sec_pr, h0, map_zero]

theorem pr_cA_xi_int (q : SplitPt D k) (hU : q.UnitAA) :
    q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] ∧ q.pr (cA D (incA D D.host.xi0⁻¹)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [GlobalTheory.SplitLineSim.pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := hU.1 _ hc
  have a1 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1.1).1 h2.1).2
  have a2 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.2.1).1 h2.2).2
  rw [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at a1 a2
  exact ⟨a1, a2⟩

theorem cond_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP h h' hh hh' hs hhe d hd
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hv : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  have hne_v : ∀ i j, i ≠ j → (p i).v ≠ (p j).v := fun i j hij e => hij (hP.inj e)
  have hU := fun i => pr_cA_xi_int (p i) (hP.unit i)
  have hprod : ∀ i, (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr (cA D (incA D D.host.xi0)) = 1 := by
    intro i
    rw [← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one, map_one]
  have hch : cA D (incA D h) = incA D h := by
    rw [cA_incA, hhe, star_mul, star_mul, star_star, hs]
    ring_nf
  have hx1 : incA D D.host.xi0⁻¹ * incA D h = cA D (incA D D.host.xi0) * incA D h' := by
    rw [cA_incA, ← map_mul, ← map_mul, hhe, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hX : ∀ c, incA D D.host.xi0⁻¹ * cA D d * c * incA D h =
      cA D (incA D D.host.xi0) * (cA D d * incA D h') * c := fun c => by
    linear_combination (cA D d * c) * hx1
  have hcX : ∀ c, cA D (incA D D.host.xi0⁻¹ * cA D d * c * incA D h) =
      cA D (incA D D.host.xi0⁻¹) * d * (cA D c * incA D h) := fun c => by
    simp only [map_mul, Formalism.L2.Theta.cA_cA, hch]
    ring
  constructor
  · intro hdc c hc hcc
    refine (GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).2 ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc), fun i => ⟨?_, ?_⟩⟩
    · rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).1 (hdc i).2) (hcc i).1
    · rw [hcX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).2 (hdc i).1) (hcc i).2
  · intro H i
    have hsup : ∀ {a : AE D}, a ∈ idAt D (· = (p i).v) → a ∈ idAt D P :=
      fun ha => idAt_mono (fun w hw => by rw [hw]; exact hv i) ha

    have hcond1 : ∀ j, (p j).pr ((p i).sec 1) ∈ 𝒪[k] ∧
        (p j).pr (cA D ((p i).sec 1)) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      by_cases hij : j = i
      · subst hij
        rw [(p j).pr_sec, GlobalTheory.SplitLineSim.pr_cA_sec, zero_mul]
        exact ⟨one_mem _, zero_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) 1),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) 1), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h1 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (sec_mem_idAt (p i) 1)) hcond1)).2 i).1
    rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr, (p i).pr_sec, mul_one] at h1

    have hh0 : (p i).pr (incA D h) ≠ 0 := by
      intro h0
      have := congrArg (p i).pr (congrArg (incA D) (mul_inv_cancel₀ hh))
      rw [map_mul (incA D), map_mul (p i).pr, h0, zero_mul, map_one, map_one] at this
      exact zero_ne_one this
    have hcond2 : ∀ j, (p j).pr (cA D ((p i).sec ((p i).pr (incA D h))⁻¹)) ∈ 𝒪[k] ∧
        (p j).pr (cA D (cA D ((p i).sec ((p i).pr (incA D h))⁻¹))) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      rw [Formalism.L2.Theta.cA_cA]
      by_cases hij : j = i
      · subst hij
        rw [GlobalTheory.SplitLineSim.pr_cA_sec, (p j).pr_sec, inv_mul_cancel₀ hh0]
        exact ⟨zero_mem _, one_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) ((p i).pr (incA D h))⁻¹),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h2 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹)) hcond2)).2 i).2
    rw [hcX, Formalism.L2.Theta.cA_cA] at h2
    have e3 : (p i).pr (cA D (incA D D.host.xi0⁻¹) * d * ((p i).sec ((p i).pr (incA D h))⁻¹ * incA D h)) =
        (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d := by
      simp only [map_mul, (p i).pr_sec]
      rw [inv_mul_cancel₀ hh0, mul_one]
    rw [e3] at h2
    refine ⟨?_, ?_⟩
    · have e2 : (p i).pr d = (p i).pr (cA D (incA D D.host.xi0)) *
          ((p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d) := by
        linear_combination (-(p i).pr d) * hprod i
      rw [e2]; exact mul_mem (hU i).1 h2
    · have e1 : (p i).pr (cA D d) * (p i).pr (incA D h') = (p i).pr (cA D (incA D D.host.xi0⁻¹)) *
          ((p i).pr (cA D (incA D D.host.xi0)) * ((p i).pr (cA D d) * (p i).pr (incA D h'))) := by
        linear_combination (-((p i).pr (cA D d) * (p i).pr (incA D h'))) * hprod i
      rw [e1]; exact mul_mem (hU i).2 h1

end GlobalTheory.FinPl.ScalarDual

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_lineConditions_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  atlas_forward_decl GlobalTheory.FinPl.ScalarDual.cond_dual
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Corev.mem_latO_line_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  intro D k _ _ _ _ ι p I P hP n'' _ _ σ B' γ γ₀ M' Λ' hM' hγ S LS hLS x hx
  have hu : (B'.o.resT S).symm (0, x) = B'.o.jB ⬝ x := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
  have hMx : MxAt P (B'.o.jB ⬝ x) := by
    intro i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)
  obtain ⟨hrk, hne⟩ := B'.line
  have hr : ∀ r r' : Fin B'.L.rank, r = r' := fun r r' => Fin.ext (by omega)
  let r₀ : Fin B'.L.rank := ⟨0, by omega⟩
  have hζ : B'.ζ r₀ ≠ 0 := by
    intro h0
    apply hne
    have : B'.ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
    rw [this, Matrix.mulVec_zero, dotProduct_zero]
  have hjB : ∀ d : AE D, B'.o.jB *ᵥ (d • ratV B'.ζ) = fun r => d * incA D (vecB B'.o B'.ζ r) := by
    intro d
    funext r
    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have key : ∀ y, (B'.o.jB ⬝ x) *ᵥ y ∈ latV B'.V₀ M' P ↔ ∃ d : AE D, d ∈ idAt D P ∧
      (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧
        (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k]) := by
    intro y
    rw [← Matrix.mulVec_mulVec]
    constructor
    · intro h
      have hz : ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ ∈ idAt D P := by
        simp only [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r₀ j)
      set d : AE D := ((x : Matrix _ _ (AE D)) *ᵥ y) r₀ * incA D (B'.ζ r₀)⁻¹ with hd
      have hdI : d ∈ idAt D P := Ideal.mul_mem_right _ _ hz
      have hzd : (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ := by
        funext r
        rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, hd, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
      rw [hzd, hjB] at h
      exact ⟨d, hdI, hzd, (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).1 h⟩
    · rintro ⟨d, hdI, hzd, hc⟩
      rw [hzd, hjB]
      exact (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n'' B'.V₀ B'.A B'.L B'.o B'.ζ B'.line γ γ₀ M' Λ' hM' hγ d hdI).2 hc
  rw [hu, GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D S B'.V₀ LS M' hLS hM' P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP B'.V₀ M']
  constructor
  · rintro ⟨-, h⟩ y hy
    exact (key y).1 (h y hy)
  · intro h
    exact ⟨hMx, fun y hy => (key y).2 (h y hy)⟩
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lineHomLatticeCompletion_iff_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  atlas_forward_decl GlobalTheory.Corev.mem_latO_line_iff
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.SelfDualCompl

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := by
  show Algebra.TensorProduct.map (AlgHom.id _ _) _ (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

def hA (S : HSp D) (y s : Fin S.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j

theorem intAt_zero (P : Pl D → Prop) : (0 : AE D) ∈ intAt D P :=
  ⟨zero_mem _, by rw [map_zero]; exact zero_mem _⟩

theorem intAt_add {P : Pl D → Prop} {a b : AE D} (ha : a ∈ intAt D P) (hb : b ∈ intAt D P) : a + b ∈ intAt D P :=
  ⟨add_mem ha.1 hb.1, by rw [map_add]; exact add_mem ha.2 hb.2⟩

theorem intAt_neg {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : -a ∈ intAt D P :=
  ⟨neg_mem ha.1, by rw [map_neg]; exact neg_mem ha.2⟩

theorem hA_zero_left (S : HSp D) (s : Fin S.rank → AE D) : hA S 0 s = 0 := by
  simp [hA]

theorem hA_add_left (S : HSp D) (y y' s : Fin S.rank → AE D) : hA S (y + y') s = hA S y s + hA S y' s := by
  simp [hA, mul_add, Finset.sum_add_distrib]

theorem hA_neg_left (S : HSp D) (y s : Fin S.rank → AE D) : hA S (-y) s = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_zero_right (S : HSp D) (y : Fin S.rank → AE D) : hA S y 0 = 0 := by
  simp [hA]

theorem hA_add_right (S : HSp D) (y s s' : Fin S.rank → AE D) : hA S y (s + s') = hA S y s + hA S y s' := by
  simp [hA, add_mul, Finset.sum_add_distrib]

theorem hA_neg_right (S : HSp D) (y s : Fin S.rank → AE D) : hA S y (-s) = -hA S y s := by
  simp [hA, Finset.sum_neg_distrib]

theorem hA_gen (S : HSp D) (α β : Af D.host.F) (x x' : Fin S.rank → D.host.E) :
    hA S (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x j)) (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x' i)) =
      pairA D.host.F 0 (β * α) ⊗ₜ[D.host.F] (∑ i, ∑ j, star (x' i) * HSpace.gram S i j * x j) := by
  simp only [hA, cA_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← TensorProduct.tmul_sum,
    pairA_mul]

theorem hA_mem {S : HSp D} {LS : Lat S} (hS : IsSelfDualC S LS) {P : Pl D → Prop} {y s : Fin S.rank → AE D}
    (hy : y ∈ latV S LS P) (hs : s ∈ latV S LS P) : hA S y s ∈ intAt D P := by
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨β, hβi, hβ, a, ha, x', hx', rfl⟩ := hs
    rw [Set.mem_singleton_iff] at ha
    subst ha
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      rw [hA_gen]
      obtain ⟨c, hc⟩ := (hS.2 x).1 hx x' hx'
      rw [← hc]
      refine ⟨pair_mem_idAt P _ (fun v hv => by rw [map_mul, hα v hv, mul_zero]) _, ?_⟩
      rw [finPart_pair]
      exact AddSubgroup.subset_closure ⟨β * α, GlobalTheory.FinPl.LatMem.intAf_mul' hβi hαi, c, rfl⟩
    | zero => rw [hA_zero_left]; exact intAt_zero P
    | add y y' _ _ h h' => rw [hA_add_left]; exact intAt_add h h'
    | neg y _ h => rw [hA_neg_left]; exact intAt_neg h
  | zero => rw [hA_zero_right]; exact intAt_zero P
  | add s s' _ _ h h' => rw [hA_add_right]; exact intAt_add h h'
  | neg s _ h => rw [hA_neg_right]; exact intAt_neg h

theorem wachExpansion_smul_compatible {S : HSp D} {LS : Lat S} (P : Pl D → Prop) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    (idem D P * finIn D z) • (fun l => incA D (s l)) ∈ latV S LS P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, o, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨ePl D P * a, GlobalTheory.FinPl.LatMem.intAf_mul' (ePl_int P) ha,
      fun w hw => by rw [map_mul, evalV_ePl, if_neg hw, zero_mul], 1, rfl, o • s, LS.smul_mem o hs, ?_⟩
    funext l
    simp only [Pi.smul_apply, smul_eq_mul, idem, finIn_tmul, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, pairA_mul,
      mul_one, one_mul]
    congr 1
  | zero => rw [map_zero, mul_zero, zero_smul]; exact zero_mem _
  | add z z' _ _ h h' => rw [map_add, mul_add, add_smul]; exact add_mem h h'
  | neg z _ h => rw [map_neg, mul_neg, neg_smul]; exact neg_mem h

theorem smul_mem {S : HSp D} {LS : Lat S} {P : Pl D → Prop} {c : AE D} (hc : c ∈ intAt D P) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) : c • (fun l => incA D (s l)) ∈ latV S LS P := by
  have h1 : idem D P * c = c := (mem_idAt_iff P c).1 hc.1
  have h2 : c = finIn D (finPart D c) := eq_finIn (infPart_of_idAt hc.1)
  have := wachExpansion_smul_compatible P hs hc.2
  rwa [← h2, h1] at this

theorem cA_test (P : Pl D → Prop) (e : D.host.E) :
    cA D (pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * e)) = idem D P * incA D (star e) := by
  rw [cA_tmul, idem, incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, mul_one]

theorem selfDual_latV : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop)
    (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) →
    (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  intro D S LS hS P y hy
  refine ⟨fun h s hs => hA_mem hS h hs, fun h => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hS
  let t : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (ePl D P) ⊗ₜ[D.host.F] (1 * s' i l)
  have ht : ∀ i, t i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨ePl D P, ePl_int P, fun w hw => by rw [evalV_ePl, if_neg hw], 1, rfl, s' i, hs' i, rfl⟩
  have hyeq : y = ∑ i, hA S y (t i) • (fun a => incA D (s i a)) := by
    funext a
    have hya : y a = idem D P * y a := ((mem_idAt_iff P (y a)).1 (hy a)).symm
    have hsum : ∀ j, idem D P * y j * incA D (if a = j then 1 else 0) = if a = j then idem D P * y j else 0 := by
      intro j
      split_ifs <;> simp
    calc y a = ∑ j, idem D P * y j * incA D (if a = j then 1 else 0) := by
          rw [Finset.sum_congr rfl fun j _ => hsum j, Finset.sum_ite_eq, if_pos (Finset.mem_univ a)]
          exact hya
      _ = ∑ j, idem D P * y j * incA D (∑ i, s i a * ∑ k, star (s' i k) * HSpace.gram S k j) := by
          simp only [hdual]
      _ = _ := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hA, t, cA_test, map_sum, map_mul, Finset.mul_sum,
            Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [hyeq]
  exact sum_mem fun i _ => smul_mem (h (t i) (ht i)) (hs i)

end GlobalTheory.FinPl.SelfDualCompl
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual : ∀ (D : D7) (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ r, y r ∈ idAt D P) → (y ∈ latV S LS P ↔ ∀ s ∈ latV S LS P, (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * y j) ∈ intAt D P) := by
  atlas_forward_decl GlobalTheory.FinPl.SelfDualCompl.selfDual_latV
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LineProj

variable {D : D7}

theorem latV_le_of {S : HSp D} (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w → P' w) :
    GlobalTheory.FinPl.latV S L P ≤ GlobalTheory.FinPl.latV S L P' := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul
  refine AddSubgroup.closure_mono ?_
  rintro y ⟨α, hα, hP, a, ha, x, hx, rfl⟩
  exact ⟨α, hα, fun v hv => hP v fun h' => hv (h v h'), a, ha, x, hx, rfl⟩

theorem row_iA {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    star (vecB o ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0 := by
  show star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀ ᵥ* o.iA = 0
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, o.orth,
    Matrix.vecMul_zero]

theorem row_vecB {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) :
    (star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  show (star (o.iB *ᵥ ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ (o.iB *ᵥ ζ) = _
  rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, o.isoB]

theorem star_self {L : HSp D} (ζ : Fin L.rank → D.host.E) :
    star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, gram_conjTranspose, ← Matrix.dotProduct_mulVec]

theorem sum_incA_mulVec {s t : ℕ} (ρ : Fin s → D.host.E) (N : Matrix (Fin s) (Fin t) D.host.E) (u : Fin t → AE D) :
    ∑ j, incA D (ρ j) * (rat N *ᵥ u) j = ∑ a, incA D ((ρ ᵥ* N) a) * u a := by
  simp only [rat, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj

variable {D : D7}

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {q : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n] {S₀ A L : HSp D} {o : OrthDec S₀ A L} {ζ : Fin L.rank → D.host.E}
  {α : Frame q A n} {α₀ : Frame q S₀ (n ⊕ Fin 1)} {M : Lat S₀} {Λ : Submodule 𝒪[k] (n → k)}

theorem e_vecB_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) :
    (fun r => q.e * incA D (vecB o ζ r)) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  let y0 : n ⊕ Fin 1 → k := Sum.elim 0 (fun _ => 1)
  have hb0 : α₀.b *ᵥ y0 = fun r => q.pr (incA D (vecB o ζ r)) := by
    rw [hsum, Matrix.fromCols_mulVec]
    funext r
    have h1 : y0 ∘ Sum.inl = 0 := Sum.elim_comp_inl _ _
    rw [Pi.add_apply, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y0,
      Sum.elim_inr, mul_one]
    rfl
  have hy0 : y0 ∈ lastKer Λ := by
    refine GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.2 ⟨?_, ?_⟩
    · show (Sum.elim 0 (fun _ => 1) : n ⊕ Fin 1 → k) ∘ Sum.inl ∈ Λ
      rw [Sum.elim_comp_inl]; exact zero_mem _
    · exact one_mem _
  have h := (hlat y0).1 hy0
  rw [hb0] at h
  simpa only [q.sec_pr] using h

theorem pr_coeff_mem (hsum : IsSumFrame o ζ α α₀) (hlat : α₀.IsLat M (lastKer Λ)) {m : Fin S₀.rank → AE D} {c : AE D}
    (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r))
    (hem : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v)) : q.pr c ∈ 𝒪[k] := by
  let pu : Fin A.rank → k := fun a => q.pr ((o.pA *ᵥ m) a)
  let y : n ⊕ Fin 1 → k := Sum.elim (α.b' *ᵥ pu) (fun _ => q.pr c)
  have hbx : α₀.b *ᵥ y = fun r => q.pr (m r) := by
    rw [hsum, Matrix.fromCols_mulVec]
    have h1 : (o.jA.map q.pr * α.b) *ᵥ (y ∘ Sum.inl) = o.jA.map q.pr *ᵥ pu := by
      show (o.jA.map q.pr * α.b) *ᵥ (α.b' *ᵥ pu) = _
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, α.bb', Matrix.mul_one]
    rw [h1]
    funext r
    rw [hmdec r, RingHom.map_add, RingHom.map_mul, RingHom.map_mulVec, Pi.add_apply]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Fin.sum_univ_one, Function.comp_apply, y,
      Sum.elim_inr]
    exact mul_comm _ _
  have hy : y ∈ lastKer Λ := by
    refine (hlat y).2 ?_
    rw [hbx]
    simpa only [q.sec_pr] using hem
  exact (GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mem_lastKer.1 hy).2

theorem pr_cA_mem {P : Pl D → Prop} {a : AE D} (ha : a ∈ intAt D P) : q.pr (cA D a) ∈ 𝒪[k] := by
  rw [q.int_iff, q.sec_pr, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) ((FrameLat.cA_int_iff a).2 ha.2)

theorem e_mul_mem (hM : IsSelfDualC S₀ M) {P : Pl D → Prop} {m : Fin S₀.rank → AE D}
    (hm : m ∈ GlobalTheory.FinPl.latV S₀ M P) : (fun r => q.e * m r) ∈ GlobalTheory.FinPl.latV S₀ M (· = q.v) := by
  refine FrameLat.mem_of_pairing hM (fun r => Ideal.mul_mem_right _ _ (FrameLat.e_mem_idAt q)) fun s hs => ?_
  have h : FrameLat.pairing S₀ s (fun r => q.e * m r) = q.e * FrameLat.pairing S₀ s m := by
    simp only [FrameLat.pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h, RingHom.map_mul]
  exact FrameLat.mul_mem_intAE (GlobalTheory.UpMem.finPart_e_int q) (FrameLat.pairing_int hM hs hm)

end Local

theorem pairing_eq {S₀ A L : HSp D} (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E) (e c : AE D)
    {m : Fin S₀.rank → AE D} (hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r)) :
    (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * (c * incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) ⬝ᵥ vecB o ζ)) := by
  have h1 : (∑ a, ∑ b, cA D (e * incA D (vecB o ζ a)) * incA D (HSpace.gram S₀ a b) * m b) =
      cA D e * ∑ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b := by
    simp only [RingHom.map_mul, FrameLat.cA_incA, Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.star_apply]; ring
  rw [h1]
  congr 1
  have h2 : ∀ b, incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * m b =
      incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * (o.jA *ᵥ (o.pA *ᵥ m)) b +
        c * (incA D ((star (vecB o ζ) ᵥ* HSpace.gram S₀) b) * incA D (vecB o ζ b)) := fun b => by
    rw [hmdec b]; ring
  simp only [h2, Finset.sum_add_distrib]
  rw [OrthDec.jA, sum_incA_mulVec, row_iA]
  simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero, zero_add, ← Finset.mul_sum, ← RingHom.map_mul,
    ← map_sum]
  rfl

end GlobalTheory.LineProj

namespace GlobalTheory.LineProj

set_option maxHeartbeats 1000000 in

theorem lineProj_mem : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  intro D k _ _ _ _ ι p I P hP n _ _ S₀ A L o ζ hζ α α₀ M Λ hM hfr m hm
  have hr : L.rank = 1 := hζ.1
  let i0 : Fin L.rank := ⟨0, by omega⟩
  have hsub : ∀ j : Fin L.rank, j = i0 := fun j => Fin.ext (by have := j.2; simp only [i0]; omega)
  have hz0 : ζ i0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [hsub j, h0]; rfl
    rw [this]; simp
  have hmid : ∀ r, m r ∈ idAt D P := FrameLat.latV_supp hm
  set c : AE D := (o.pB *ᵥ m) i0 * incA D (ζ i0)⁻¹ with hc
  have hcid : c ∈ idAt D P := by
    refine Ideal.mul_mem_right _ _ ?_
    show (∑ j, o.pB i0 j * m j) ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmid j)
  have hpB : o.pB *ᵥ m = fun j => c * incA D (ζ j) := by
    funext j
    rw [hsub j, hc, mul_assoc, ← RingHom.map_mul, inv_mul_cancel₀ hz0, RingHom.map_one, mul_one]
  have hjB : o.jB *ᵥ (o.pB *ᵥ m) = fun r => c * incA D (vecB o ζ r) := by
    rw [hpB]; funext r
    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, vecB, map_sum, RingHom.map_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmdec : ∀ r, m r = (o.jA *ᵥ (o.pA *ᵥ m)) r + c * incA D (vecB o ζ r) := by
    intro r
    have h : m = o.jA *ᵥ (o.pA *ᵥ m) + o.jB *ᵥ (o.pB *ᵥ m) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
    conv_lhs => rw [h]
    rw [Pi.add_apply, hjB]
  rw [hjB]
  refine (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n S₀ A L o ζ hζ α α₀ M Λ hM hfr c hcid).2 fun i => ?_
  obtain ⟨hsum, hlat⟩ := hfr i
  have hvP : P (p i).v := (hP.mem _).2 ⟨i, rfl⟩
  have hpre : (p i).pr (p i).e = 1 := by rw [← FrameLat.sec_one, (p i).pr_sec]
  refine ⟨pr_coeff_mem hsum hlat hmdec (e_mul_mem hM hm), ?_⟩
  have hzP := latV_le_of M (P := (· = (p i).v)) (P' := P) (fun w hw => by rw [hw]; exact hvP) (e_vecB_mem hsum hlat)
  have hH := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S₀ M hM P m hmid).1 hm _ hzP
  have h := pr_cA_mem (q := p i) hH
  rw [pairing_eq o ζ (p i).e c hmdec, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, cA_cA, hpre, one_mul,
    FrameLat.cA_incA, row_vecB, star_self, RingHom.map_mul] at h
  exact h

end GlobalTheory.LineProj

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineProjection_mem_splitCoreCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n : Type) [Fintype n] [DecidableEq n] (S₀ A L : HSp D) (o : OrthDec S₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : ∀ i, Frame (p i) A n) (α₀ : ∀ i, Frame (p i) S₀ (n ⊕ Fin 1)) (M : Lat S₀) (Λ : ι → Submodule 𝒪[k] (n → k)), IsSelfDualC S₀ M → (∀ i, IsSumFrame o ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ m ∈ latV S₀ M P, o.jB *ᵥ (o.pB *ᵥ m) ∈ latV S₀ M P := by
  atlas_forward_decl GlobalTheory.LineProj.lineProj_mem
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem doubleSum_eq_dotProduct_mapMatrix_mulVec {R K : Type*} [CommRing R] {m n : ℕ} (g : R → R) (f : K → R)
    (s : Fin m → R) (G : Matrix (Fin m) (Fin n) K) (v : Fin n → R) :
    (∑ i, ∑ j, g (s i) * f (G i j) * v j) = (fun i => g (s i)) ⬝ᵥ (G.map f *ᵥ v) := by
  simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem ringHom_conjTranspose_smul_dotProduct_adjoint {R : Type*} [CommRing R] {m n : ℕ} (σ : R →+* R) (c : R)
    (s : Fin m → R) (Y : Matrix (Fin n) (Fin m) R) (G : Matrix (Fin n) (Fin n) R)
    (a : Fin n → R) :
    (fun i => σ (s i)) ⬝ᵥ ((c • ((Y.map σ)ᵀ * G)) *ᵥ a)
      = c * ((fun k => σ ((Y *ᵥ s) k)) ⬝ᵥ (G *ᵥ a)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec]
  congr 2
  funext k
  simp [vecMul, mulVec, dotProduct, map_sum, map_mul, mul_comm]

set_option maxHeartbeats 2000000 in

theorem kappa_adj : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  intro D ρ B L' ζ' l S x a s
  simp only [Link.κ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]
  have hG : gA S * giA S = 1 := by
    have h := Matrix.mul_nonsing_inv (HSpace.gram S) (gram_isUnit_det S)
    have h2 : (HSpace.gram S * (HSpace.gram S)⁻¹).map (incA D)
        = (1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E).map (incA D) := by rw [h]
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h2
    exact h2
  rw [doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D) s, doubleSum_eq_dotProduct_mapMatrix_mulVec (cA D) (incA D)]
  rw [show (HSpace.gram S).map (incA D) = gA S from rfl,
    show (HSpace.gram B.L).map (incA D) = gA B.L from rfl]
  have hG' : ∀ N : Mx D S.rank B.L.rank, HMul.hMul (gA S) (HMul.hMul (giA S) N) = N := by
    intro N
    rw [← Matrix.mul_assoc, hG]
    exact Matrix.one_mul N
  rw [Matrix.mulVec_mulVec, Matrix.mul_smul, hG']
  exact ringHom_conjTranspose_smul_dotProduct_adjoint (cA D) _ s _ _ a

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLinkKappa_adjoint_tau_factor : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (x : WO S L') (a : Fin B.L.rank → AE D) (s : Fin S.rank → AE D), (∑ i, ∑ j, cA D (s i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ a) j) = incA D (-D.host.xi0⁻¹) * ∑ i, ∑ j, cA D ((((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ s) i) * incA D (HSpace.gram B.L i j) * a j := by
  atlas_forward_decl GlobalTheory.kappa_adj
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.KapLatSupp

theorem mxAt_embed_kappa : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S T A : HSp D) (o : OrthDec T A L') (P : Pl D → Prop) (x : WO S L'), MxAt P x → MxAt P ((B.o.resS S).symm (0, l.κ S x)) ∧ MxAt P ((o.resT S).symm (0, x)) := by
  intro D ρ B L' ζ' l S T A o P x hx
  refine ⟨?_, ?_⟩
  · rw [OrthDec.resS_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_r GlobalTheory.LastOpPf.mxAt_zero _)
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LinkKapMx.mxAt_linkKappa D ρ B L' ζ' l S P x hx) _)
  · rw [OrthDec.resT_symm_apply]
    exact GlobalTheory.LastOpPf.mxAt_add (GlobalTheory.LastOpPf.mxAt_mul_l _ GlobalTheory.LastOpPf.mxAt_zero) (GlobalTheory.LastOpPf.mxAt_mul_l _ hx)

end GlobalTheory.KapLatSupp
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.KappaLeft

theorem latV_mem_idAt {D : D7} {S : HSp D} {L : Lat S} {P : Pl D → Prop} {y : Fin S.rank → AE D}
    (hy : y ∈ latV S L P) : ∀ r, y r ∈ idAt D P := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, rfl⟩ := hw
    intro r
    exact GlobalTheory.FinPl.LatMem.tmul_mem_idAt hα _
  | zero => intro r; exact zero_mem _
  | add x y _ _ hx hy => intro r; exact add_mem (hx r) (hy r)
  | neg x _ hx => intro r; exact neg_mem (hx r)

end GlobalTheory.Corev.KappaLeft

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Corev.kappa_mem_latO_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x : WO S B'.L, MxAt P x → ((B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ)) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP n' _ _ ρ σ B B' l S α α₀ M LS Λ hM hLS hα x hx
  have hcA : ∀ e : D.host.E, cA D (incA D e) = incA D (star e) := fun e => rfl
  have hMx : MxAt P ((B.o.resS S).symm (0, l.κ S x)) :=
    (GlobalTheory.KapLatSupp.mxAt_embed_kappa D ρ B B'.L B'.ζ l S B'.V₀ B'.A B'.o P x hx).1
  have hu : (B.o.resS S).symm (0, l.κ S x) = l.κ S x ⬝ B.o.pB := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]

  have hline : ∀ (L : HSp D) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ v : Fin L.rank → AE D,
      (∀ r, v r ∈ idAt D P) → ∃ c : AE D, c ∈ idAt D P ∧ v = c • ratV ζ := by
    intro L ζ hL v hv
    obtain ⟨hrk, hne⟩ := hL
    have hr : ∀ r r' : Fin L.rank, r = r' := fun r r' => Fin.ext (by omega)
    let r₀ : Fin L.rank := ⟨0, by omega⟩
    have hζ : ζ r₀ ≠ 0 := by
      intro h0
      apply hne
      have : ζ = 0 := funext fun r => by rw [hr r r₀, h0]; rfl
      rw [this, Matrix.mulVec_zero, dotProduct_zero]
    refine ⟨v r₀ * incA D (ζ r₀)⁻¹, Ideal.mul_mem_right _ _ (hv r₀), ?_⟩
    funext r
    rw [hr r r₀, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hζ, map_one, mul_one]
  have hjB : ∀ c : AE D, B.o.jB *ᵥ (c • ratV B.ζ) = fun r => c * incA D (vecB B.o B.ζ r) := by
    intro c
    funext r
    simp only [Matrix.mulVec, dotProduct, OrthDec.jB, rat, Matrix.map_apply, ratV, Pi.smul_apply, smul_eq_mul, vecB,
      map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpj : ∀ c : AE D, B.o.pB *ᵥ (B.o.jB *ᵥ (c • ratV B.ζ)) = c • ratV B.ζ := by
    intro c
    rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]

  have hsupp : ∀ m : Fin B.V₀.rank → AE D, ∀ r, (((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m) r ∈ idAt D P := by
    intro m r
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hMx r j)

  have hpair : ∀ (y : Fin S.rank → AE D) (d c : AE D), (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ →
      (∑ i, ∑ j, cA D (y i) * incA D (HSpace.gram S i j) * ((l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ)) j) =
        incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) := by
    intro y d c hxy
    rw [GlobalTheory.T.besselLinkKappa_adjoint_tau_factor D ρ B B'.L B'.ζ l S x (c • ratV B.ζ) y]
    have h1 : ((rat l.τ : Matrix _ _ (AE D)) * (x : Matrix _ _ (AE D))) *ᵥ y = d • ratV (-B.ζ) := by
      rw [← Matrix.mulVec_mulVec, hxy, Matrix.mulVec_smul, ← l.map]
      congr 1
      funext i
      simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, ratV, map_sum, map_mul]
    rw [h1]
    have hh : incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) =
        ∑ i, ∑ j, incA D (star (B.ζ i)) * incA D (HSpace.gram B.L i j) * incA D (B.ζ j) := by
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Finset.mul_sum, mul_assoc]
    rw [hh, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, ratV, Pi.neg_apply, map_mul, map_neg, hcA, star_neg]
    ring
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D B.V₀ S M LS hM hLS P, GlobalTheory.T.latticeCompletionAAScaled_eq_at_unitSplitPlaces D k ι p I P hP S LS]
  constructor
  · rintro ⟨-, h⟩ y hy
    have hz : ∀ r, ((x : Matrix _ _ (AE D)) *ᵥ y) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hx r j)
    obtain ⟨d, hdI, hxd⟩ := hline B'.L B'.ζ B'.line _ hz
    refine ⟨d, hdI, hxd, fun c hc hl => ?_⟩
    have hm : (fun r => c * incA D (vecB B.o B.ζ r)) ∈ latV B.V₀ M P :=
      (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).2 hl
    have h1 := h _ hm
    have hI := hsupp (fun r => c * incA D (vecB B.o B.ζ r))
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ (fun r => c * incA D (vecB B.o B.ζ r)) =
        (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← hjB, ← Matrix.mulVec_mulVec, hpj]
    rw [heq] at h1 hI
    have h2 := (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).1 h1 y hy
    rwa [hpair y d c hxd] at h2
  · intro h
    refine ⟨hMx, fun m hm => ?_⟩
    have hv : ∀ r, (B.o.pB *ᵥ m) r ∈ idAt D P := by
      intro r
      simp only [Matrix.mulVec, dotProduct]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (GlobalTheory.Corev.KappaLeft.latV_mem_idAt hm j)
    obtain ⟨c, hc, hcv⟩ := hline B.L B.ζ B.line _ hv
    have hjp := GlobalTheory.T.lineProjection_mem_splitCoreCompletion D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα m hm
    rw [hcv, hjB] at hjp
    have hl := (GlobalTheory.T.lineMultiple_mem_splitCoreLattice_completion_iff D k ι p I P hP n' B.V₀ B.A B.L B.o B.ζ B.line α α₀ M Λ hM hα c hc).1 hjp
    have hI := hsupp m
    have heq : ((B.o.resS S).symm (0, l.κ S x) : Matrix _ _ (AE D)) *ᵥ m = (l.κ S x : Matrix _ _ (AE D)) *ᵥ (c • ratV B.ζ) := by
      rw [hu, ← Matrix.mulVec_mulVec, hcv]
    rw [heq] at hI ⊢
    refine (GlobalTheory.T.latticeCompletionAtPlaces_selfDual_of_selfDual D S LS hLS P _ hI).2 fun s hs => ?_
    obtain ⟨d, -, hxd, hd⟩ := h s hs
    rw [hpair s d c hxd]
    exact hd c hc hl
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_mem_lineLatticeCompletion_iff_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' : Type) [Fintype n'] [DecidableEq n'] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (Λ : ι → Submodule 𝒪[k] (n' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i))) → ∀ x : WO S B'.L, MxAt P x → ((B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ)) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ∈ intAt D P) := by
  atlas_forward_decl GlobalTheory.Corev.kappa_mem_latO_iff
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaLat

theorem star_self_pair : ∀ (D : D7) (L : HSp D) (ζ : Fin L.rank → D.host.E), star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  intro D L ζ
  have hG := GlobalTheory.MixModel.gram_conjTranspose L
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hG, Matrix.dotProduct_mulVec]

theorem kappa_line_lat_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ (B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P) := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ρ σ B B' l S α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr x hx
  rw [GlobalTheory.T.mem_lineHomLatticeCompletion_iff_scalar D k ι p I P hP n'' σ B' γ γ₀ M' Λ' hM' (fun i => ⟨(hfr i).2.1, (hfr i).2.2.2⟩) S LS hLS x hx,
    GlobalTheory.T.kappa_mem_lineLatticeCompletion_iff_scalar D k ι p I P hP n' ρ σ B B' l S α α₀ M LS Λ hM hLS (fun i => ⟨(hfr i).1, (hfr i).2.2.1⟩) x hx]
  have h1 : (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ≠ 0 := B.line.2
  have h2 : (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ) ≠ 0 := B'.line.2
  have h3 := star_self_pair D B'.L B'.ζ
  have h4 : (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) = D.host.xi0 * star D.host.xi0 * (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ) := l.norm
  exact forall₂_congr fun y _ => exists_congr fun d => and_congr_right fun hd => and_congr_right fun _ =>
    GlobalTheory.T.splitPlace_lineConditions_dual D k ι p I P hP _ _ h1 h2 h3 h4 d hd

end GlobalTheory.KappaLat
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_maps_besselLineLattice_iff_split : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ (B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P) := by
  atlas_forward_decl GlobalTheory.KappaLat.kappa_line_lat_iff
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LinkKapInv

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj starAdj)

variable {D : D7}

theorem isHalf_mul_l {e : AE D} {l m n : ℕ} (A : Mx D l m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (A * x) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hx k j]

theorem isHalf_mul_r {e : AE D} {l m n : ℕ} {x : Mx D l m} (hx : IsHalf e x) (A : Mx D m n) : IsHalf e (x * A) :=
  fun i j => by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hx i k]

theorem isHalf_smul {e : AE D} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (c • x) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hx i j]

theorem isHalf_adj {e : AE D} {m n : ℕ} {x : Mx D m n} (hx : IsHalf e x) : IsHalf (cA D e) (adj x) :=
  fun i j => by
    show cA D e * cA D (x j i) = cA D (x j i)
    rw [← map_mul, hx j i]

def tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (_l : Link B L' ζ') :
    Matrix (Fin L'.rank) (Fin B.L.rank) D.host.E := fun i j => -(B.ζ j)⁻¹ * ζ' i

theorem mul_tauPlus {ρ : ℕ} {B : BesLev D ρ} {L' : HSp D} {ζ' : Fin L'.rank → D.host.E} (l : Link B L' ζ') :
    l.τ * tauPlus l = 1 := by
  obtain ⟨hr, hq⟩ := B.line
  have hsub : ∀ a b : Fin B.L.rank, a = b := fun a b => Fin.ext (by have := a.2; have := b.2; omega)
  have hne : ∀ a, B.ζ a ≠ 0 := by
    intro a ha
    apply hq
    have h0 : B.ζ = 0 := funext fun b => by rw [hsub b a]; exact ha
    rw [h0]; simp
  funext a b
  rw [hsub b a, Matrix.one_apply_eq, Matrix.mul_apply]
  have hm := congrFun l.map a
  rw [Pi.neg_apply, Matrix.mulVec, dotProduct] at hm
  simp only [tauPlus]
  calc ∑ k, l.τ a k * (-(B.ζ a)⁻¹ * ζ' k) = -(B.ζ a)⁻¹ * ∑ k, l.τ a k * ζ' k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ = 1 := by rw [hm, neg_mul_neg, inv_mul_cancel₀ (hne a)]

theorem kappa_inv : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ')
    (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧
      ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  intro D ρ B L' ζ' l S P h
  refine ⟨(rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h, ?_, fun hh => ?_, fun e he => ?_⟩
  · show ofAdj B.L S ((rat l.τ : Mx D B.L.rank L'.rank) * ((rat (tauPlus l) : Mx D L'.rank B.L.rank) * starAdj B.L S h)) = h
    rw [← Matrix.mul_assoc, ← rat_mul, mul_tauPlus l, rat_one, Matrix.one_mul, GlobalTheory.LastOpPf.ofAdj_starAdj]
  · exact GlobalTheory.LastOpPf.mxAt_mul_l _ (GlobalTheory.LastOpPf.mxAt_smul _ (GlobalTheory.LastOpPf.mxAt_mul_l _
      (GlobalTheory.LastOpPf.mxAt_mul_r (GlobalTheory.LastOpPf.mxAt_adj hh) _)))
  · exact isHalf_mul_l _ (isHalf_smul _ (isHalf_mul_l _ (isHalf_mul_r (isHalf_adj he) _)))

end GlobalTheory.LinkKapInv
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLink_kappa_surjective_supported_conjugateHalf : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (l : Link B L' ζ') (S : HSp D) (P : Pl D → Prop) (h : WO B.L S), ∃ x : WO S L', l.κ S x = h ∧ (MxAt P h → MxAt P x) ∧ ∀ e : AE D, IsHalf e h → IsHalf (cA D e) x := by
  atlas_forward_decl GlobalTheory.LinkKapInv.kappa_inv
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinPl.LineVanish

variable {D : D7}

theorem mxAt_mul_right' {P : Pl D → Prop} {m n r : ℕ} {u : Mx D m n} (hu : MxAt P u) (N : Mx D n r) :
    MxAt P (u * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hu i k)

theorem fin_of_mxAt' {P : Pl D → Prop} {m n : ℕ} {u : Mx D m n} (hu : MxAt P u) : u.map (infPart D) = 0 := by
  ext i j
  exact RingHom.mem_ker.1 (Ideal.mem_inf.1 (hu i j)).1

theorem isHalf_mul_right {e : AE D} {m n r : ℕ} {u : Mx D m n} (hu : IsHalf e u) (N : Mx D n r) :
    IsHalf e (u * N) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [← mul_assoc, hu i k]

theorem isHalf_mul_left {e : AE D} {m n r : ℕ} (N : Mx D r m) {u : Mx D m n} (hu : IsHalf e u) :
    IsHalf e (N * u) := by
  intro i j
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hu k j]

theorem contr_smul_left' {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (vL : VolM D B'.L.rank S.rank) (c : ℂ) (f₁ : WO B.V₀ S → ℂ) (f₂ : WO S B'.V₀ → ℂ) :
    GlobalTheory.Unf.contr l S vL (c • f₁) f₂ = c • GlobalTheory.Unf.contr l S vL f₁ f₂ := by
  funext u v
  simp only [GlobalTheory.Unf.contr, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext w
  ring

theorem step3 : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V T : HSp D) (LV : Lat V) (LT : Lat T), IsSelfDualC V LV → IsSelfDualC T LT → ∀ y : WO V T, MxAt P y → y ∉ latO V T (LV : Set _) (LT : Set _) P → ∃ u ∈ latO V T (LV : Set _) (LT : Set _) P, (∃ e, IsSplitIdem D e ∧ IsHalf e u) ∧ ψ (symplO V T u y) ≠ 1 := by
  intro D k _ _ _ _ ι p I P hP ψ hψ V T LV LT hLV hLT y hy hout
  by_contra hno
  push_neg at hno
  apply hout
  have hadd : ∀ a b : WO V T, symplO V T (a + b) y = symplO V T a y + symplO V T b y := by
    intro a b
    have h := GlobalTheory.SplitScalar.symplO_sub_left V T (a + b) b y
    rw [add_sub_cancel_right] at h
    rw [h]; ring
  have hneg : ∀ a : AF D.host.F, ψ a = 1 → ψ (-a) = 1 := by
    intro a ha
    calc ψ (-a) = ψ (-a) * ψ a := by rw [ha, mul_one]
      _ = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  let K : AddSubgroup (WO V T) :=
    { carrier := {u | ψ (symplO V T u y) = 1}
      zero_mem' := by
        simp only [Set.mem_setOf_eq, GlobalTheory.SplitScalar.symplO_zero_left, AddChar.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hadd, AddChar.map_add_eq_mul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h0 : symplO V T (-a) y = -symplO V T a y := by
          have := hadd (-a) a
          rw [neg_add_cancel, GlobalTheory.SplitScalar.symplO_zero_left] at this
          exact eq_neg_of_add_eq_zero_left this.symm
        rw [h0]; exact hneg _ ha }
  rw [GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ V T LV LT hLV hLT P y hy]
  intro u' hu'
  have hK : u' ∈ K := (AddSubgroup.closure_le K).2 (fun u hu => hno u hu.1 hu.2)
    (GlobalTheory.T.homLatticeCompletion_le_closure_isotropicHalves D k ι p I P hP V T _ _ u' hu')
  rw [GlobalTheory.SplitScalar.symplO_skew]
  exact hneg _ hK

set_option maxHeartbeats 2000000 in

theorem vanish : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ψ hψ ρ σ B B' l S vL α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr y hy hout f₁ f₂ h₁ h₂
  classical

  have hyM : MxAt P ((B.o.resS S).symm (0, y)) := by
    rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]
    exact mxAt_mul_right' hy _
  obtain ⟨u, hu, ⟨e, he, heu⟩, hψu⟩ := step3 D k ι p I P hP ψ hψ B.V₀ S M LS hM hLS _ hyM hout
  set h := (B.o.resS S u).2 with hh
  have hhN : (B.o.resS S).symm (0, h) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P :=
    GlobalTheory.T.lineProjection_mem_homLatticeCompletion D k ι p I P hP n' ρ B S α α₀ M LS Λ hM hLS (fun i => ⟨(hfr i).1, (hfr i).2.2.1⟩) u hu
  have hhalf : IsHalf e h := isHalf_mul_right heu _
  have hhmx : MxAt P h := by
    have := ((GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D B.V₀ S M LS hM hLS P _).1 hhN).1
    have h2 : (B.o.resS S ((B.o.resS S).symm (0, h))).2 = h := by rw [AddEquiv.apply_symm_apply]
    rw [← h2]; exact mxAt_mul_right' this _
  have hpair : symplO B.V₀ S ((B.o.resS S).symm (0, h)) ((B.o.resS S).symm (0, y)) =
      symplO B.V₀ S u ((B.o.resS S).symm (0, y)) := by
    rw [B.o.symplO_resS, B.o.symplO_resS S u, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.SplitScalar.symplO_zero_right, GlobalTheory.SplitScalar.symplO_zero_right]

  obtain ⟨x', hkx, hxmx, hxhalf⟩ := GlobalTheory.T.besselLink_kappa_surjective_supported_conjugateHalf D ρ B B'.L B'.ζ l S P h
  have hx'N : (B'.o.resT S).symm (0, x') ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P := by
    rw [GlobalTheory.T.kappa_maps_besselLineLattice_iff_split D k ι p I P hP n' n'' ρ σ B B' l S α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr x' (hxmx hhmx), hkx]
    exact hhN
  have hx'half : IsHalf (cA D e) ((B'.o.resT S).symm (0, x')) := by
    rw [OrthDec.resT_symm_apply, Matrix.mul_zero, zero_add]
    exact isHalf_mul_left _ (hxhalf e hhalf)
  have hf₂ : heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x')) f₂ = f₂ :=
    h₂.2.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he) _ hx'N hx'half
  have hf₁ : heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x')) f₁ = f₁ := by
    rw [hkx]
    exact h₁.2.2 e he _ hhN (by
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add]; exact isHalf_mul_right hhalf _)
  have hth : IsThetaFunO ψ B.V₀ S (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) :=
    GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (fin_of_mxAt' hyM) h₁.1
  have hmove := GlobalTheory.T.besselLineContraction_heisenberg_invariant D ψ hψ ρ σ B B' l S vL _ f₂ hth h₂.1 x'
  rw [hf₂, GlobalTheory.SplitScalar.heisO_comm, hf₁, contr_smul_left', hkx, hpair] at hmove
  set C := GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂
  have : (ψ (symplO B.V₀ S u ((B.o.resS S).symm (0, y))) - 1) • C = 0 := by
    rw [sub_smul, hmove, one_smul, sub_self]
  exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hψu)

end GlobalTheory.FinPl.LineVanish
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLine_translate_off_lattice_kills_contraction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ y : WO B.L S, MxAt P y → (B.o.resS S).symm (0, y) ∉ latO B.V₀ S (M : Set _) (LS : Set _) P → ∀ f₁ f₂, Vac ψ B.V₀ S M LS P f₁ → Vac ψ S B'.V₀ LS M' P f₂ → GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, y)) f₁) f₂ = 0 := by
  atlas_forward_decl GlobalTheory.FinPl.LineVanish.vanish
end
