import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesDisjointTwistPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixReductionEqZeroOffPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ConjHalfSplitInt

theorem frMapAdj_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  intro D S T βS βT Pg Q eg eQ hg hQ _ _ x hx
  have hx' : cA D (eg + eQ) • x = x := (GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_iff' _ _).1 hx
  have hsplit : x = cA D eg • x + cA D eQ • x := by rw [← add_smul, ← map_add, hx']
  have hA : ∀ e : AE D, frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := fun e => by
    rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, Formalism.L2.Theta.cA_cA]
  have hint : ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P →
      toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun e P h => by
    rw [← GlobalTheory.ExportSeries.idem_eq h]
    unfold GlobalTheory.ExportSeries.idem
    rw [map_sum]
    exact sum_mem fun PP hPP => GlobalTheory.RedHalfDrop.int_idemAt ⟨e, h⟩ hPP
  constructor
  · intro h
    rw [hA, hA]
    exact ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hg) (h i j),
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hQ) (h i j)⟩
  · rintro ⟨h1, h2⟩
    rw [hsplit, GlobalTheory.PlaceVec.frMapAdj_add]
    intro i j
    rw [Matrix.add_apply]
    exact add_mem (h1 i j) (h2 i j)

end GlobalTheory.ConjHalfSplitInt
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointFrame_integral_iff_parts_conj_half : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  first | exact @GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff | exact GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff | (intros; apply GlobalTheory.ConjHalfSplitInt.frMapAdj_int_iff <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.TwoStepRed

theorem redM_part_eq {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D))
    (βT : GL (Fin T.rank) (EAf D)) (P R : Finset (Pl D.host.E)) (e f : AE D)
    (hP : IsIdemSum e P) (hR : IsIdemSum f R) (hd : Disjoint P R) (x : WO S T)
    (hx : IsHalf (cA D (e + f)) x) (hN : IsIntM (frMapAdj S T βS βT x)) :
    ∀ PP ∈ P, redM PP (frMapAdj S T βS βT (cA D e • x)) = redM PP (frMapAdj S T βS βT x) := by
  intro PP hPP
  have hsplit : x = cA D e • x + cA D f • x := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, ← map_add, hx i j]
  have h1 : frMapAdj S T βS βT x
      = frMapAdj S T βS βT (cA D e • x) + toEAf D f • frMapAdj S T βS βT x := by
    conv_lhs => rw [hsplit]
    rw [GlobalTheory.PlaceVec.frMapAdj_add, GlobalTheory.RedHalfDrop.frMapAdj_smul_eq βS βT (cA D f) x, cA_cA]
  have hc : toEAf D f ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
    rw [← GlobalTheory.ExportSeries.idem_eq hR]
    unfold GlobalTheory.ExportSeries.idem
    rw [show (toEAf D) (∑ Q ∈ R, GlobalTheory.ExportSeries.idemAt Q) = ∑ Q ∈ R, (toEAf D) (GlobalTheory.ExportSeries.idemAt Q) from
      map_sum (toEAf D).toAddMonoidHom _ _]
    exact sum_mem (fun Q hQ => GlobalTheory.RedHalfDrop.int_idemAt ⟨f, hR⟩ hQ)
  rw [eq_sub_of_add_eq h1.symm]
  exact GlobalTheory.RedHalfDrop.redM_sub_smul PP hN hc
    (GlobalTheory.AdjRedOff.resS_idemSum_eq_zero hR hc (fun h => Finset.disjoint_left.mp hd hPP h))

theorem redM_twoStep : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  intro D S T βS βT Pg Q eg eQ hg hQ hd _ x hx hN
  exact ⟨redM_part_eq S T βS βT Pg Q eg eQ hg hQ hd x hx hN,
    redM_part_eq S T βS βT Q Pg eQ eg hQ hg hd.symm x (by rwa [add_comm]) hN⟩

end GlobalTheory.TwoStepRed
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → IsIntM (frMapAdj S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT (cA D eg • x)) = redM PP (frMapAdj S T βS βT x)) ∧ (∀ PP ∈ Q, redM PP (frMapAdj S T βS βT (cA D eQ • x)) = redM PP (frMapAdj S T βS βT x)) := by
  first | exact @GlobalTheory.TwoStepRed.redM_twoStep | exact GlobalTheory.TwoStepRed.redM_twoStep | (intros; apply GlobalTheory.TwoStepRed.redM_twoStep <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.TwoStepModel

open GlobalTheory.ExportSeries

theorem datum_eq_tensorHalf {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {Pg Q : Finset (Pl D.host.E)} {eg eQ : AE D} (hg : IsIdemSum eg Pg) (hq : IsIdemSum eQ Q) (hd : Disjoint Pg Q)
    (he : IsIdemSum (eg + eQ) (Pg ∪ Q)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    (fun x => if IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) =
      tensorHalf (cA D eQ) (cA D eg)
        (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) else 0)
        (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj S T βS βT x) then
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) else 0) := by
  have hA := GlobalTheory.T.adjointFrame_integral_iff_parts_conj_half D S T βS βT Pg Q eg eQ hg hq hd he
  have hB := GlobalTheory.T.reduction_adjointFrame_conj_half_two_parts D S T βS βT Pg Q eg eQ hg hq hd he
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hcg : ∀ x : WO S T, IsHalf (cA D eg) (cA D eg • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heg]) x
  have hcQ : ∀ x : WO S T, IsHalf (cA D eQ) (cA D eQ • x) :=
    fun x => GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_smul (by rw [← map_mul, heQ]) x
  funext x
  rw [tensorHalf_apply]
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  by_cases hx : IsHalf (cA D (eg + eQ)) x
  · have hx' : IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_pos hx', mul_one]
    by_cases hi : IsIntM (frMapAdj S T βS βT x)
    · obtain ⟨i1, i2⟩ := (hA x hx).1 hi
      obtain ⟨r1, r2⟩ := hB x hx hi
      have c1 : IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x) := ⟨hx, hi⟩
      have c2 : IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x)) := ⟨hcQ x, i2⟩
      have c3 : IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x)) := ⟨hcg x, i1⟩
      rw [if_pos c1, if_pos c2, if_pos c3, mul_comm]
      congr 1
      · exact GlobalTheory.PlaceVec.omegaQ_congr Q _ ξ _ fun PP hPP => (r2 PP hPP).symm
      · exact GlobalTheory.PlaceVec.omegaK_congr Pg fun PP hPP => (r1 PP hPP).symm
    · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hi h.2
      rw [if_neg c1]
      have := mt (hA x hx).2 hi
      rcases not_and_or.1 this with h | h
      · have c3 : ¬ (IsHalf (cA D eg) (cA D eg • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eg • x))) := fun h' => h h'.2
        rw [if_neg c3, mul_zero]
      · have c2 : ¬ (IsHalf (cA D eQ) (cA D eQ • x) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := fun h' => h h'.2
        rw [if_neg c2, zero_mul]
  · have c1 : ¬ (IsHalf (cA D (eg + eQ)) x ∧ IsIntM (frMapAdj S T βS βT x)) := fun h => hx h.1
    have hx' : ¬ IsHalf (cA D eQ + cA D eg) x := hc ▸ hx
    rw [if_neg c1, if_neg hx', mul_zero]

end GlobalTheory.TwoStepModel

namespace GlobalTheory.ConjTwist

theorem isThetaAt_vP_twoStep : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0) (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ (R.Q t) → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i) (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg → IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 fg (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) (R.vP i t) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t eg eQ fg hg hq hfg
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hC.thP.vP i t
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hd := GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    (R.Q t) (fun y => omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he (R.xiR t)]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.ConjTwist

end
end
