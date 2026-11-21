import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BaseAt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ConjSecondFactor
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardCells
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BlockRetr
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TargetFact
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumShift
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbSumGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefNotInt

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def tauU : UP p →* UP p where
  toFun x := ⟨tau p x, tau_mem_UP p x.2⟩
  map_one' := by ext1; exact (tau p).map_one
  map_mul' x y := by ext1; exact (tau p).map_mul x y

theorem tauU_tauU (x : UP p) : tauU p (tauU p x) = x := by
  ext1; exact tau_tau p x

def piU (πa : UP p →* UP p) : UP p →* UP p := (tauU p).comp (πa.comp (tauU p))

def piG (πa : UP p →* UP p) (x : GG p) : GG p :=
  if h : x ∈ UP p then ((piU p πa ⟨x, h⟩ : UP p) : GG p) else 1

theorem piG_of (πa : UP p →* UP p) (x : UP p) : piG p πa x = ((piU p πa x : UP p) : GG p) := by
  unfold piG; rw [dif_pos x.2]

theorem mem_StP_iff (x : GG p) :
    x ∈ StP M δ u u' w p ↔ x ∈ UP p ∧ x • Y0 M δ u u' w p = Y0 M δ u u' w p :=
  ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩

theorem fixes_base_iff (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (x : UP p) :
    (x : GG p) • Y0 M δ u u' w p = Y0 M δ u u' w p ↔ ((tauU p x : UP p) : GG p) • a.mat = a.mat := by
  rw [← (hB.choose_spec.2 (tauU p x))]
  constructor
  · intro h
    show tau p x • _ = _
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

theorem retr_of (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
    (hD : CountAb.Data (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)
    (hB : BaseAt M δ u u' w p a) :
    Formalism.L2.SG.Pf.ProdEP2Core.Retr (StP M δ u u' w p) (UP p) (piG p πa) := by
  refine ⟨fun x hx => ((mem_StP_iff M δ u u' w p x).1 hx).1, fun x hx y hy => ?_, fun x hx => ?_, fun s hs => ?_⟩
  · have ex : piG p πa x = ((piU p πa ⟨x, hx⟩ : UP p) : GG p) := piG_of p πa ⟨x, hx⟩
    have ey : piG p πa y = ((piU p πa ⟨y, hy⟩ : UP p) : GG p) := piG_of p πa ⟨y, hy⟩
    have exy : piG p πa (x * y) = ((piU p πa (⟨x, hx⟩ * ⟨y, hy⟩) : UP p) : GG p) :=
      piG_of p πa (⟨x, hx⟩ * ⟨y, hy⟩)
    rw [exy, ex, ey, map_mul]
    rfl
  · rw [show x = ((⟨x, hx⟩ : UP p) : GG p) from rfl, piG_of]
    refine (mem_StP_iff M δ u u' w p _).2 ⟨(piU p πa ⟨x, hx⟩).2, ?_⟩
    rw [fixes_base_iff M δ u u' w p a hB]
    have h1 : tauU p (piU p πa ⟨x, hx⟩) = πa (tauU p ⟨x, hx⟩) := by
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
    rw [h1]
    exact hD.mem _
  · obtain ⟨hsU, hsY⟩ := (mem_StP_iff M δ u u' w p s).1 hs
    rw [show s = ((⟨s, hsU⟩ : UP p) : GG p) from rfl, piG_of]
    have hfix : tauU p ⟨s, hsU⟩ ∈ MulAction.stabilizer (UP p) a.mat :=
      (fixes_base_iff M δ u u' w p a hB ⟨s, hsU⟩).1 hsY
    have h2 : piU p πa ⟨s, hsU⟩ = ⟨s, hsU⟩ := by
      simp only [piU, MonoidHom.comp_apply, hD.id _ hfix, tauU_tauU]
    rw [h2]

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

theorem conjugator_mem_unipotent (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    g0 M δ hA L U hL hU ∈ UP p :=
  ⟨lOf_loUni M δ hA L U hL hU, ρOf_upUni M δ hA L U hL hU⟩

theorem H_le_UP (X : MP p) : KP M p ⊓ StabX p X ≤ UP p := fun h hh =>
  ⟨Formalism.L2.SG.Pf.ProdEP2Cut.loUni_of_int M hh.1.1, Formalism.L2.SG.Pf.ProdEP2Cut.upUni_of_int M hh.1.2⟩

theorem XP_eq (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    XP M δ u u' w L U = g0 M δ hA L U hL hU • Y0 M δ u u' w p := rfl



theorem mem_Ag_iff (x : GG p) : x ∈ Ag M δ u u' (p := p) w ↔ x ∈ StP M δ u u' w p ∧ x ∈ KP M p := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, h1⟩, h2, rfl⟩

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.CountAb

variable {G 𝒳 : Type} [Group G] [MulAction G 𝒳]
variable (W : 𝒳) (S N' K : Subgroup G) (π : G →* G) (g : G)

theorem index_eq_relIndex (hD : Data W S N' K π) :
    ((Hk W K g).map (πk W S N' K π hD)).index = ((Hs W K g).map π).relIndex (K ⊓ S) := by
  let e : ↥(K ⊓ S) →* ↥(Ak S K) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simp only [Ak, Subgroup.mem_subgroupOf]; exact x.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Function.Surjective e := fun a =>
    ⟨⟨a.1.1, a.1.2, by have h := a.2; simp only [Ak, Subgroup.mem_subgroupOf] at h; exact h⟩, rfl⟩
  rw [← Subgroup.index_comap_of_surjective _ he]
  unfold Subgroup.relIndex
  congr 1
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨k, hk, hkx⟩
    refine ⟨k.1, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hk
    · have h2 := congrArg (fun y : ↥(Ak S K) => ((y : ↥K) : G)) hkx
      simpa [πk, e] using h2
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy.1⟩, ?_, ?_⟩
    · simpa [Hk, Subgroup.mem_subgroupOf] using hy
    · apply Subtype.ext
      apply Subtype.ext
      simpa [πk, e] using hyx

theorem card_cells' (hD : Data W S N' K π) :
    Nat.card (Quotient (cellRel W N' K g)) = ((Hs W K g).map π).relIndex (K ⊓ S) := (card_cells W S N' K π g hD).trans (index_eq_relIndex W S N' K π g hD)

end Formalism.L2.SG.Pf.CountAb
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

theorem tauU_inj : Function.Injective (tauU p) := fun x y h => by
  rw [← tauU_tauU p x, ← tauU_tauU p y, h]

theorem tau_KP_iff (x : GG p) : tau p x ∈ KP M p ↔ x ∈ KP M p :=
  ⟨fun h => by have := tau_mem_KP M p h; rwa [tau_tau] at this, fun h => tau_mem_KP M p h⟩

section Parts

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a)

def gU : UP p := tauU p ⟨g0 M δ hA L U hL hU, conjugator_mem_unipotent M δ hA L U hL hU⟩ * hB.choose

theorem gU_smul : ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • a.mat =
    phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' w L U) := by
  rw [XP_eq M δ u u' w hA L U hL hU, phi_smul p δ _ _ w (conjugator_mem_unipotent M δ hA L U hL hU), hB.choose_spec.1]
  show ((tau p (g0 M δ hA L U hL hU) * (hB.choose : GG p)) : GG p) • a.mat = _
  rw [mul_smul]

theorem mem_H_iff (x : UP p) :
    (x : GG p) ∈ KP M p ⊓ StabX p (XP M δ u u' w L U) ↔
      tauU p x ∈ CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB) := by
  show (x : GG p) ∈ KP M p ∧ (x : GG p) • XP M δ u u' (p := p) w L U = XP M δ u u' (p := p) w L U ↔
    tau p x ∈ KP M p ∧ (tauU p x : UP p) • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) =
      (gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat
  rw [tau_KP_iff]
  apply and_congr Iff.rfl
  have e : ∀ y : UP p, (y • ((gU M δ u u' w hA L U hL hU a hB : UP p) • a.mat) : MP p) =
      (y : GG p) • (((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p)) := fun y => rfl
  have e2 : ((gU M δ u u' w hA L U hL hU a hB : UP p) • (a.mat : MP p) : MP p) =
      ((gU M δ u u' w hA L U hL hU a hB : UP p) : GG p) • (a.mat : MP p) := rfl
  rw [e2, gU_smul]
  constructor
  · intro h
    show tau p (x : GG p) • phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U) =
      phi p δ (D.mem u).A.T (D.mem u').A.T w (XP M δ u u' (p := p) w L U)
    rw [← phi_smul p δ _ _ w x.2, h]
  · intro h
    apply phi_inj p δ (D.mem u).A.T (D.mem u').A.T w
    rw [phi_smul p δ _ _ w x.2]
    exact h

end Parts

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape Formalism.L2.SG.Pf.ProdEP2Core

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) {p : PlF D}

section Parts2

variable (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (hB : BaseAt M δ u u' w p a) (πa : UP p →* UP p)
  (hD : CountAb.Data a.mat (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa)

theorem img_eq :
    img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U)) (H_le_UP M _) =
      (((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).map (tauU p)).map (UP p).subtype := by
  ext z
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hU' := H_le_UP M _ hh
    have hy := (mem_H_iff M δ u u' w hA L U hL hU a hB ⟨h, hU'⟩).1 hh
    refine ⟨tauU p (πa (tauU p ⟨h, hU'⟩)), ⟨πa (tauU p ⟨h, hU'⟩), ⟨_, hy, rfl⟩, rfl⟩, ?_⟩
    exact (piG_of p πa ⟨h, hU'⟩).symm
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    refine ⟨((tauU p y : UP p) : GG p), ?_, ?_⟩
    · exact (mem_H_iff M δ u u' w hA L U hL hU a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hy)
    · show piG p πa ((tauU p y : UP p) : GG p) = _
      rw [piG_of]
      simp only [piU, MonoidHom.comp_apply, tauU_tauU]
      rfl

include hB in
theorem Ag_eq :
    Ag M δ u u' (p := p) w =
      (((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat).map (tauU p)).map (UP p).subtype := by
  ext z
  rw [mem_Ag_iff]
  constructor
  · rintro ⟨hS, hK⟩
    obtain ⟨hzU, hzY⟩ := (mem_StP_iff M δ u u' w p z).1 hS
    have hfix := (fixes_base_iff M δ u u' w p a hB ⟨z, hzU⟩).1 hzY
    refine ⟨⟨z, hzU⟩, ⟨tauU p ⟨z, hzU⟩, ⟨?_, ?_⟩, tauU_tauU p _⟩, rfl⟩
    · show ((tauU p ⟨z, hzU⟩ : UP p) : GG p) ∈ KP M p
      exact tau_mem_KP M p hK
    · exact hfix
  · rintro ⟨_, ⟨y, ⟨hyK, hyS⟩, rfl⟩, rfl⟩
    refine ⟨(mem_StP_iff M δ u u' w p _).2 ⟨(tauU p y).2, ?_⟩, ?_⟩
    · exact (fixes_base_iff M δ u u' w p a hB (tauU p y)).2 (by rw [tauU_tauU]; exact hyS)
    · exact tau_mem_KP M p hyK

include hD in

theorem countAt_of_parts (v : ℝ)
    (hv : (Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) : ℝ) = v)
    (hpos : Nat.card (Quotient (CountAb.cellRel a.mat πa.ker (KU M p) (gU M δ u u' w hA L U hL hU a hB))) ≠ 0) :
    CountAt M δ u u' w hA L U hL hU v := by
  have hcard := CountAb.card_cells' (a.mat) (MulAction.stabilizer (UP p) a.mat) πa.ker (KU M p) πa
    (gU M δ u u' w hA L U hL hU a hB) hD
  have hidx : (img (retr_of M δ u u' w p a πa hD hB) (KP M p ⊓ StabX p (XP M δ u u' (p := p) w L U))
      (H_le_UP M _)).relIndex (Ag M δ u u' (p := p) w) =
      ((CountAb.Hs a.mat (KU M p) (gU M δ u u' w hA L U hL hU a hB)).map πa).relIndex
        ((KU M p) ⊓ MulAction.stabilizer (UP p) a.mat) := by
    rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB,
      Subgroup.relIndex_map_map_of_injective _ _ Subtype.val_injective,
      Subgroup.relIndex_map_map_of_injective _ _ (tauU_inj (p := p))]
  refine ⟨UP p, piG p πa, retr_of M δ u u' w p a πa hD hB, H_le_UP M _, conjugator_mem_unipotent M δ hA L U hL hU, ?_, ?_, ?_⟩
  · rw [img_eq M δ u u' w hA L U hL hU a hB πa hD, Ag_eq M δ u u' w a hB]
    apply Subgroup.map_mono
    apply Subgroup.map_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hD.kπ z hz.1, hD.mem z⟩
  · rw [hidx, ← hcard]
    exact hpos
  · rw [hidx, ← hcard, hv]

end Parts2

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf Formalism.MainNotions.LocalOrbitGerms
open Classical

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

section Cells

variable (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1))

def VaSet : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E) :=
  {v | (∀ i, v i i = 1) ∧ (∀ i j, i < j → v i j = 0) ∧
    ∀ i j : Fin (m + 1), i ≠ j → Loc.sameBlock a.blocks (i : ℕ) (j : ℕ) = true → v i j = 0}

def CellPair : Type :=
  {p : Matrix (Fin (m + 1)) (Fin (m + 1)) E × Matrix (Fin (m + 1)) (Fin (m + 1)) E //
    p.1 ∈ VaSet a ∧ (∀ i, p.2 i i = 1) ∧ ∀ i j, j < i → p.2 i j = 0}

theorem intLow_inv_mul {n : ℕ} {l : Matrix (Fin n) (Fin n) E} (h : TieN.IntLow M l) : l⁻¹ * l = 1 := by
  apply Matrix.nonsing_inv_mul
  have hd : l.det = 1 := by
    rw [Matrix.det_of_lowerTriangular l (fun i j hij => h.2.1 i j hij)]
    simp [h.1]
  rw [hd]
  exact isUnit_one

theorem intUp_mul_inv {n : ℕ} {l : Matrix (Fin n) (Fin n) E} (h : TieN.IntUp M l) : l * l⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  have hd : l.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => h.2.1 i j hij)]
    simp [h.1]
  rw [hd]
  exact isUnit_one

def cellSetoid : Setoid (CellPair a) where
  r p p' := (∃ l, TieN.IntLow M l ∧ p'.1.1 = l * p.1.1) ∧ (∃ ρ, TieN.IntUp M ρ ∧ p'.1.2 = p.1.2 * ρ)
  iseqv := by
    refine ⟨fun p => ⟨⟨1, LocOrbCut.intLow_one M, by rw [Matrix.one_mul]⟩, ⟨1, LocOrbCut.intUp_one M, by rw [Matrix.mul_one]⟩⟩,
      fun {p p'} h => ?_, fun {p p' p''} h h' => ?_⟩
    · obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := h
      refine ⟨⟨l⁻¹, LocOrbCut.intLow_inv M hl, ?_⟩, ⟨ρ⁻¹, LocOrbCut.intUp_inv M hρ, ?_⟩⟩
      · rw [e1, ← Matrix.mul_assoc, intLow_inv_mul M hl, Matrix.one_mul]
      · rw [e2, Matrix.mul_assoc, intUp_mul_inv M hρ, Matrix.mul_one]
    · obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := h
      obtain ⟨⟨l', hl', e1'⟩, ⟨ρ', hρ', e2'⟩⟩ := h'
      refine ⟨⟨l' * l, LocOrbCut.intLow_mul M hl' hl, ?_⟩, ⟨ρ * ρ', LocOrbCut.intUp_mul M hρ hρ', ?_⟩⟩
      · rw [e1', e1, Matrix.mul_assoc]
      · rw [e2', e2, Matrix.mul_assoc]

end Cells

section Reindex

variable {m : ℕ} (a : Loc.Pt E (m + 1))

abbrev eA : Fin (m + 1) ≃ Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum := finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a).symm

abbrev rhoA (X : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) E := X.submatrix (eA a) (eA a)

theorem eA_val (i : Fin (m + 1)) : ((eA a i : Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) : ℕ) = (i : ℕ) := rfl

theorem eA_lt {i j : Fin (m + 1)} : eA a i < eA a j ↔ i < j := by
  rw [Fin.lt_iff_val_lt_val, eA_val, eA_val, ← Fin.lt_iff_val_lt_val]

theorem rhoA_mul (X Y : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
    rhoA a (X * Y) = rhoA a X * rhoA a Y :=
  (Matrix.submatrix_mul_equiv X Y (eA a) (eA a) (eA a)).symm

theorem rhoA_one : rhoA a (1 : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) = 1 :=
  Matrix.submatrix_one_equiv (eA a)

theorem rhoA_pt : rhoA a (Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) = a.mat :=
  (Formalism.MainNotions.LocalModelPeriodLattices.mat_eq a).symm

theorem rhoA_apply (X : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)
    (x y : Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) : X x y = rhoA a X ((eA a).symm x) ((eA a).symm y) := by
  simp [rhoA]

abbrev sbA : Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum → Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum → Bool :=
  fun x y => Loc.sameBlock a.blocks (x : ℕ) (y : ℕ)

private theorem sameBlock_eq_true_iff_blk_eq {K : Type} [CommRing K] : ∀ (bs : List (Kˣ × ℕ+)) (x y : ℕ),
    x < (List.map (fun b : Kˣ × ℕ+ => ((b.2 : ℕ+) : ℕ)) bs).sum →
    y < (List.map (fun b : Kˣ × ℕ+ => ((b.2 : ℕ+) : ℕ)) bs).sum →
    (Loc.sameBlock bs x y = true ↔
      Formalism.DoubleCosetMeasures.blk (List.map (fun b : Kˣ × ℕ+ => ((b.2 : ℕ+) : ℕ)) bs) x =
        Formalism.DoubleCosetMeasures.blk (List.map (fun b : Kˣ × ℕ+ => ((b.2 : ℕ+) : ℕ)) bs) y)
  | [], x, y, hx, _ => by simp at hx
  | (u, s) :: bs, x, y, hx, hy => by
    simp only [List.map_cons, List.sum_cons] at hx hy
    simp only [Loc.sameBlock, List.map_cons, Formalism.DoubleCosetMeasures.blk]
    by_cases h1 : x < (s : ℕ) <;> by_cases h2 : y < (s : ℕ)
    · simp [h1, h2]
    · have h2' : (s : ℕ) ≤ y := by omega
      simp [h1, h2, h2']
      omega
    · have h1' : (s : ℕ) ≤ x := by omega
      simp [h1, h2, h1']
    · have ih := sameBlock_eq_true_iff_blk_eq bs (x - s) (y - s) (by omega) (by omega)
      have h1' : (s : ℕ) ≤ x := by omega
      have h2' : (s : ℕ) ≤ y := by omega
      simp [h1, h2, h1', h2', ih]

theorem sbA_iff (x y : Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) :
    sbA a x y = true ↔ Formalism.DoubleCosetMeasures.blk (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 x = Formalism.DoubleCosetMeasures.blk (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 y := by
  exact sameBlock_eq_true_iff_blk_eq a.blocks x y x.2 y.2

theorem isCoordA : Grp.IsCoord (K := E) (PW (sbA a))
    (Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) :=
  Grp.isCoord_low _ _ (sbA a) (sbA_iff a)

theorem va_of_lowW (g : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) :
    rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix _ _ E) ∈ VaSet a := by
  obtain ⟨x, hx⟩ := ((isCoordA a).mem (g : GL _ E)).1 g.2
  rw [hx]
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij hsb => ?_⟩
  · simp [Matrix.submatrix_apply, mk]
  · have hne : eA a i ≠ eA a j := (eA a).injective.ne (ne_of_lt hij)
    have hlt : eA a i < eA a j := (eA_lt a).2 hij
    simp only [Matrix.submatrix_apply, mk, hne, if_false]
    rw [dif_neg]
    intro hp
    exact absurd hp.1 (not_lt.2 hlt.le)
  · have hne : eA a i ≠ eA a j := (eA a).injective.ne hij
    have hs : sbA a (eA a i) (eA a j) = true := by
      simp only [sbA, eA_val]
      exact hsb
    simp only [Matrix.submatrix_apply, mk, hne, if_false]
    rw [dif_neg]
    intro hp
    have h2 : sbA a (eA a i) (eA a j) = false := hp.2
    rw [hs] at h2
    exact Bool.noConfusion h2

theorem lowW_of_va {v : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (hv : v ∈ VaSet a) :
    ∃ g : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2,
      rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix _ _ E) = v := by
  set X : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E :=
    v.submatrix (eA a).symm (eA a).symm with hXdef
  have hval : ∀ b : Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum, (((eA a).symm b : Fin (m + 1)) : ℕ) = (b : ℕ) := by
    intro b
    have h := eA_val a ((eA a).symm b)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  have hX : mk (PW (sbA a)) (fun p => X p.1.1 p.1.2) = X := by
    apply Dec.mk_coords
    · intro b
      simp [hXdef, hv.1]
    · intro b c hbc hP
      simp only [hXdef, Matrix.submatrix_apply]
      have hne : (eA a).symm b ≠ (eA a).symm c := (eA a).symm.injective.ne hbc
      by_cases hlt : b < c
      · apply hv.2.1
        rw [← eA_lt a]
        simpa using hlt
      · have hcb : c < b := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hbc)
        have hsb : sbA a b c = true := by
          by_contra h
          exact hP ⟨hcb, by simpa using h⟩
        apply hv.2.2 _ _ hne
        rw [hval b, hval c]
        exact hsb
  have hdet : X.det = 1 := by
    rw [← hX]
    exact (isCoordA a).det _
  let gU : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E := Matrix.nonsingInvUnit X (by rw [hdet]; exact isUnit_one)
  have hmem : gU ∈ Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 :=
    ((isCoordA a).mem gU).2 ⟨_, hX.symm⟩
  refine ⟨⟨gU, hmem⟩, ?_⟩
  show X.submatrix (eA a) (eA a) = v
  ext i j
  simp [hXdef]

theorem up_of_upUniG (g : Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) :
    (∀ i, rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix _ _ E) i i = 1) ∧
      ∀ i j, j < i → rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix _ _ E) i j = 0 := by
  have hg : Formalism.DoubleCosetMeasures.IsUpUni ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
      Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := g.2
  exact ⟨fun i => hg.2 _, fun i j hij => hg.1 ((eA_lt a).2 hij)⟩

theorem upUniG_of_up {u : Matrix (Fin (m + 1)) (Fin (m + 1)) E} (h1 : ∀ i, u i i = 1)
    (h2 : ∀ i j, j < i → u i j = 0) :
    ∃ g : Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum,
      rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix _ _ E) = u := by
  set X : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E :=
    u.submatrix (eA a).symm (eA a).symm with hXdef
  have hup : Formalism.DoubleCosetMeasures.IsUpUni X := by
    constructor
    · intro b c hcb
      simp only [hXdef, Matrix.submatrix_apply]
      apply h2
      rw [← eA_lt a]
      simpa using hcb
    · intro b
      simp [hXdef, h1]
  have hdet : X.det = 1 := by
    rw [Matrix.det_of_upperTriangular hup.1]
    simp [hup.2]
  let gU : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E := Matrix.nonsingInvUnit X (by rw [hdet]; exact isUnit_one)
  have hmem : gU ∈ Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum := hup
  refine ⟨⟨gU, hmem⟩, ?_⟩
  show X.submatrix (eA a) (eA a) = u
  ext i j
  simp [hXdef]

end Reindex

section Count

variable (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1))

abbrev vOf (g : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
  rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
    Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)

abbrev uOf (g : Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) : Matrix (Fin (m + 1)) (Fin (m + 1)) E :=
  rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
    Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)

theorem rhoA_gl_mul (g h : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
    rhoA a (((g * h : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) :
      Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
    rhoA a (g : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
      rhoA a (h : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := by
  rw [Units.val_mul, rhoA_mul]

theorem rhoA_gl_inv (g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
    rhoA a (g : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
      rhoA a (((g⁻¹ : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) :
        Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) = 1 := by
  rw [← rhoA_gl_mul, mul_inv_cancel, Units.val_one, rhoA_one]

theorem rhoA_gl_inv' (g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
    rhoA a (((g⁻¹ : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) :
        Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
      rhoA a (g : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) = 1 := by
  rw [← rhoA_gl_mul, inv_mul_cancel, Units.val_one, rhoA_one]

theorem isInt_of_rhoA {X : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E}
    (h : ∀ i j, rhoA a X i j ∈ M.R) : Formalism.DoubleCosetMeasures.IsInt M.R X := fun x y => by
  rw [rhoA_apply a X x y]; exact h _ _

theorem rel_low (g g' : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) :
    g' * g⁻¹ ∈ Formalism.DoubleCosetMeasures.intSub M.R (Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) ↔
      ∃ l, TieN.IntLow M l ∧ vOf a g' = l * vOf a g := by
  have hcoe : ((g' * g⁻¹ : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) :
      GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
      (g' : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) * (g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)⁻¹ := by
    simp
  constructor
  · intro hmem
    obtain ⟨hI, _⟩ := hmem
    refine ⟨vOf a (g' * g⁻¹), ⟨(va_of_lowW a (g' * g⁻¹)).1, (va_of_lowW a (g' * g⁻¹)).2.1, ?_⟩, ?_⟩
    · intro i j
      exact hI _ _
    · show rhoA a ((g' : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) = _
      rw [← rhoA_gl_mul, hcoe, inv_mul_cancel_right]
  · rintro ⟨l, hl, he⟩
    have he' : rhoA a ((g' : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
        l * rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := he
    have hL : rhoA a (((g' * g⁻¹ : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) :
        GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) = l := by
      rw [hcoe, rhoA_gl_mul, he', Matrix.mul_assoc, rhoA_gl_inv, Matrix.mul_one]
    have hY := rhoA_gl_inv' a ((g' * g⁻¹ : Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) :
        GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)
    rw [hL] at hY
    have hinv := Matrix.inv_eq_left_inv hY
    refine ⟨isInt_of_rhoA M a (fun i j => ?_), isInt_of_rhoA M a (fun i j => ?_)⟩
    · rw [hL]
      exact hl.2.2 i j
    · rw [← hinv]
      exact (LocOrbCut.intLow_inv M hl).2.2 i j

theorem rel_up (g g' : Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) :
    g⁻¹ * g' ∈ Formalism.DoubleCosetMeasures.intSub M.R (Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) ↔
      ∃ ρ, TieN.IntUp M ρ ∧ uOf a g' = uOf a g * ρ := by
  have hcoe : ((g⁻¹ * g' : Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) :
      GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
      (g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)⁻¹ * (g' : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := by
    simp
  constructor
  · intro hmem
    obtain ⟨hI, _⟩ := hmem
    refine ⟨uOf a (g⁻¹ * g'), ⟨(up_of_upUniG a (g⁻¹ * g')).1, (up_of_upUniG a (g⁻¹ * g')).2, ?_⟩, ?_⟩
    · intro i j
      exact hI _ _
    · show rhoA a ((g' : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) = _
      rw [← rhoA_gl_mul, hcoe, mul_inv_cancel_left]
  · rintro ⟨ρ, hρ, he⟩
    have he' : rhoA a ((g' : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
        rhoA a ((g : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) * ρ := he
    have hL : rhoA a (((g⁻¹ * g' : Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) :
        GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) :
          Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) = ρ := by
      rw [hcoe, rhoA_gl_mul, he', ← Matrix.mul_assoc, rhoA_gl_inv', Matrix.one_mul]
    have hY := rhoA_gl_inv a ((g⁻¹ * g' : Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) :
        GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)
    rw [hL] at hY
    have hinv := Matrix.inv_eq_right_inv hY
    refine ⟨isInt_of_rhoA M a (fun i j => ?_), isInt_of_rhoA M a (fun i j => ?_)⟩
    · rw [hL]
      exact hρ.2.2 i j
    · rw [← hinv]
      exact (LocOrbCut.intUp_inv M hρ).2.2 i j

end Count

section Main

variable (M : Loc.Model F E) {m : ℕ} (a : Loc.Pt E (m + 1))

def pairOf (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) : CellPair a :=
  ⟨(vOf a q.1.out, uOf a q.2.out), va_of_lowW a _, up_of_upUniG a _⟩

theorem zQ_eq (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) :
    LocOrbCut.zQ M.R a q = (pairOf M a q).1.1 * a.mat * (pairOf M a q).1.2 := by
  rw [← rhoA_pt a]
  show rhoA a _ = rhoA a _ * rhoA a _ * rhoA a _
  rw [← rhoA_mul, ← rhoA_mul]
  rfl

private theorem mem_of_cellSetoid_rel_of_mem (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E))
    (hO : ∀ Z ∈ O, ∀ l ρ, TieN.IntLow M l → TieN.IntUp M ρ → l * Z * ρ ∈ O)
    {p p' : CellPair a} (h : (cellSetoid M a).r p p') (hp : p.1.1 * a.mat * p.1.2 ∈ O) :
    p'.1.1 * a.mat * p'.1.2 ∈ O := by
  obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := h
  rw [e1, e2]
  have h' := hO _ hp l ρ hl hρ
  simpa only [Matrix.mul_assoc] using h'

theorem cellCos_bijOn (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E))
    (hO : ∀ Z ∈ O, ∀ l ρ, TieN.IntLow M l → TieN.IntUp M ρ → l * Z * ρ ∈ O) :
    Set.BijOn (fun q => Quotient.mk (cellSetoid M a) (pairOf M a q))
      {q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) | LocOrbCut.zQ M.R a q ∈ O}
      {c : Quotient (cellSetoid M a) | ∃ p : CellPair a, Quotient.mk _ p = c ∧ p.1.1 * a.mat * p.1.2 ∈ O} := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    refine ⟨pairOf M a q, rfl, ?_⟩
    rw [← zQ_eq]
    exact hq
  · intro q _ q' _ he
    have hr : (cellSetoid M a).r (pairOf M a q) (pairOf M a q') := Quotient.exact he
    obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := hr
    have h1 := (rel_low M a q.1.out q'.1.out).2 ⟨l, hl, e1⟩
    have h2 := (rel_up M a q.2.out q'.2.out).2 ⟨ρ, hρ, e2⟩
    apply Prod.ext
    · rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
      apply Quotient.sound
      exact QuotientGroup.rightRel_apply.2 h1
    · rw [← Quotient.out_eq q.2, ← Quotient.out_eq q'.2]
      exact QuotientGroup.eq.2 h2
  · rintro c ⟨p, rfl, hp⟩
    obtain ⟨g, hg⟩ := lowW_of_va a p.2.1
    obtain ⟨h, hh⟩ := upUniG_of_up a p.2.2.1 p.2.2.2
    let q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) := (Quotient.mk _ g, QuotientGroup.mk h)
    have hq1 : g * (q.1.out)⁻¹ ∈ Formalism.DoubleCosetMeasures.intSub M.R (Formalism.DoubleCosetMeasures.lowW E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2) :=
      QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q.1))
    obtain ⟨l, hl, el⟩ := (rel_low M a q.1.out g).1 hq1
    have hq2 : (q.2.out)⁻¹ * h ∈ Formalism.DoubleCosetMeasures.intSub M.R (Formalism.DoubleCosetMeasures.upUniG E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) :=
      QuotientGroup.eq.1 (Quotient.out_eq q.2)
    obtain ⟨ρ, hρ, er⟩ := (rel_up M a q.2.out h).1 hq2
    have hr : (cellSetoid M a).r (pairOf M a q) p :=
      ⟨⟨l, hl, by rw [← hg]; exact el⟩, ⟨ρ, hρ, by rw [← hh]; exact er⟩⟩
    refine ⟨q, ?_, Quotient.sound hr⟩
    show LocOrbCut.zQ M.R a q ∈ O
    rw [zQ_eq]
    exact mem_of_cellSetoid_rel_of_mem M a O hO ((cellSetoid M a).iseqv.symm hr) hp

theorem cellCos (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E))
    (hO : ∀ Z ∈ O, ∀ l ρ, TieN.IntLow M l → TieN.IntUp M ρ → l * Z * ρ ∈ O) :
    {q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) | LocOrbCut.zQ M.R a q ∈ O}.ncard =
      {c : Quotient (cellSetoid M a) | ∃ p : CellPair a, Quotient.mk _ p = c ∧ p.1.1 * a.mat * p.1.2 ∈ O}.ncard := by
  have hb := cellCos_bijOn M a O hO
  rw [← hb.image_eq, Set.ncard_image_of_injOn hb.injOn]

theorem cellCos_finite_iff (O : Set (Matrix (Fin (m + 1)) (Fin (m + 1)) E))
    (hO : ∀ Z ∈ O, ∀ l ρ, TieN.IntLow M l → TieN.IntUp M ρ → l * Z * ρ ∈ O) :
    {q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) | LocOrbCut.zQ M.R a q ∈ O}.Finite ↔
      {c : Quotient (cellSetoid M a) | ∃ p : CellPair a, Quotient.mk _ p = c ∧ p.1.1 * a.mat * p.1.2 ∈ O}.Finite := by
  have hb := cellCos_bijOn M a O hO
  rw [← hb.image_eq, Set.finite_image_iff hb.injOn]

end Main

end Formalism.L2.SG.Pf.Coef
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}

def uLo (X : MP p) (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) : GLp p :=
  Matrix.nonsingInvUnit X (by rw [Formalism.L2.SG.Pf.FibQ.det_lower p h1 h2]; exact isUnit_one)

def uUpU (X : MP p) (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) : GLp p :=
  Matrix.nonsingInvUnit X (by rw [Formalism.L2.SG.Pf.FibQ.det_upper p h1 h2]; exact isUnit_one)

def pairOfU (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
    (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (x : UP p) (hx : πa x = 1) :
    Formalism.L2.SG.Pf.Coef.CellPair a :=
  ⟨(((x : GG p).1 : GLp p).val, (((x : GG p).2.unop : GLp p)).val),
    by
      obtain ⟨h1, h2⟩ := (hker x).1 hx
      exact ⟨fun i => (h1 i i).2 rfl, fun i j hij => (h1 i j).1 hij, fun i j hij hb => h2 i j hij hb⟩,
    fun i => (x.2.2 i i).2 rfl, fun i j hij => (x.2.2 i j).1 hij⟩

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

theorem first_value_mul (x y : UP p) : (((x * y : UP p) : GG p).1 : GLp p).val =
    (((x : GG p).1 : GLp p).val) * (((y : GG p).1 : GLp p).val) := rfl

theorem second_value_mul (x y : UP p) : ((((x * y : UP p) : GG p).2.unop : GLp p)).val =
    ((((y : GG p).2.unop : GLp p)).val) * ((((x : GG p).2.unop : GLp p)).val) := rfl

def fC : Quotient (CountAb.cellRel (a.mat) πa.ker (KU M p) g) → Quotient (Formalism.L2.SG.Pf.Coef.cellSetoid (M p) a) :=
  Quotient.lift (fun x => Quotient.mk _ (pairOfU a πa hker x.1 (MonoidHom.mem_ker.1 x.2.1))) (by
    intro x y hxy
    apply Quotient.sound
    have hk : (y : UP p) * (x : UP p)⁻¹ ∈ KU M p := hxy.1
    have hy : (y : UP p) = ((y : UP p) * (x : UP p)⁻¹) * (x : UP p) := by group
    refine ⟨⟨((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val, hk.1, ?_⟩,
      ⟨((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p).val, hk.2, ?_⟩⟩
    · show (((y : UP p) : GG p).1 : GLp p).val = _
      conv_lhs => rw [hy]
      rw [first_value_mul]
      rfl
    · show ((((y : UP p) : GG p).2.unop : GLp p)).val = _
      conv_lhs => rw [hy]
      rw [second_value_mul]
      rfl)

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

theorem fC_inj : Function.Injective (fC M a πa hker g) := by
  intro X Y hXY
  induction X using Quotient.inductionOn with
  | h x =>
    induction Y using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      obtain ⟨⟨l, hl, e1⟩, ⟨ρ, hρ, e2⟩⟩ := Quotient.exact hXY
      have e1' : (((y : UP p) : GG p).1 : GLp p).val = l * (((x : UP p) : GG p).1 : GLp p).val := e1
      have e2' : ((((y : UP p) : GG p).2.unop : GLp p)).val = ((((x : UP p) : GG p).2.unop : GLp p)).val * ρ := e2
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show Formalism.MainNotions.S.TieN.IntLow (M p) ((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).1 : GLp p).val
        rw [first_value_mul]
        have : (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val * (((x : UP p) : GG p).1 : GLp p).val = 1 := by
          rw [← first_value_mul, inv_mul_cancel]; rfl
        rw [e1', Matrix.mul_assoc]
        rw [show (((x : UP p) : GG p).1 : GLp p).val * (((((x : UP p)⁻¹ : UP p) : GG p).1 : GLp p)).val = 1 by
          rw [← first_value_mul, mul_inv_cancel]; rfl, Matrix.mul_one]
        exact hl
      · show Formalism.MainNotions.S.TieN.IntUp (M p) (((((y : UP p) * (x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p)).val
        rw [second_value_mul, e2', ← Matrix.mul_assoc]
        rw [show ((((((x : UP p)⁻¹ : UP p) : GG p).2.unop : GLp p))).val *
            ((((x : UP p) : GG p).2.unop : GLp p)).val = 1 by rw [← second_value_mul, mul_inv_cancel]; rfl, Matrix.one_mul]
        exact hρ
      · show (y : UP p) * (x : UP p)⁻¹ ∈ πa.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, MonoidHom.mem_ker.1 x.2.1, MonoidHom.mem_ker.1 y.2.1, inv_one,
          mul_one]

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) {p : PlF D}
  (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (πa : UP p →* UP p)
  (hker : ∀ x : UP p, πa x = 1 ↔ ((x : GG p).1 : GLp p).val ∈ Va p a) (g : UP p)

def mkUP (X Y : MP p) (hX : IsLoUni X) (hY : IsUpUni Y) : UP p :=
  ⟨(uLo X (fun a b h => (hX a b).1 h) (fun a => (hX a a).2 rfl),
      MulOpposite.op (uUpU Y (fun a b h => (hY a b).1 h) (fun a => (hY a a).2 rfl))), hX, hY⟩

theorem fC_range : Set.range (fC M a πa hker g) =
    {c | ∃ pr : Formalism.L2.SG.Pf.Coef.CellPair a, Quotient.mk _ pr = c ∧
      pr.1.1 * a.mat * pr.1.2 ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) ((g : GG p) • a.mat)} := by
  ext c
  constructor
  · rintro ⟨X, rfl⟩
    induction X using Quotient.inductionOn with
    | h x =>
      obtain ⟨hxN, k, hk, hxk⟩ := x.2
      refine ⟨pairOfU a πa hker x.1 (MonoidHom.mem_ker.1 hxN), rfl, ?_⟩
      refine ⟨(((k : GG p).1 : GLp p)).val, (((k : GG p).2.unop : GLp p)).val, hk.1, hk.2, ?_⟩
      exact hxk
  · rintro ⟨pr, rfl, l, ρ, hl, hρ, he⟩
    have hv : IsLoUni pr.1.1 := fun i j => ⟨pr.2.1.2.1 i j, fun h => h ▸ pr.2.1.1 i⟩
    have hu : IsUpUni pr.1.2 := fun i j => ⟨pr.2.2.2 i j, fun h => h ▸ pr.2.2.1 i⟩
    set x := mkUP pr.1.1 pr.1.2 hv hu with hxdef
    have hxN : πa x = 1 := (hker x).2 ⟨hv, fun i j hij hb => pr.2.1.2.2 i j hij hb⟩
    set k := mkUP l ρ (Formalism.L2.SG.Pf.ProdEP2Cut.loUni_of_int M hl) (Formalism.L2.SG.Pf.ProdEP2Cut.upUni_of_int M hρ)
    have hk : k ∈ KU M p := ⟨hl, hρ⟩
    refine ⟨Quotient.mk _ ⟨x, MonoidHom.mem_ker.2 hxN, k, hk, he⟩, ?_⟩
    show Quotient.mk _ (pairOfU a πa hker x hxN) = _
    congr 1

include hker in
theorem card_cellRel : Nat.card (Quotient (CountAb.cellRel (a.mat) πa.ker (KU M p) g)) =
    {c : Quotient (Formalism.L2.SG.Pf.Coef.cellSetoid (M p) a) | ∃ pr : Formalism.L2.SG.Pf.Coef.CellPair a,
      Quotient.mk (Formalism.L2.SG.Pf.Coef.cellSetoid (M p) a) pr = c ∧
      pr.1.1 * a.mat * pr.1.2 ∈ Formalism.L2.SG.Pf.LocOrbSumPf.orbR (M p) ((g : GG p) • a.mat)}.ncard := by
  rw [← fC_range M a πa hker g, Set.ncard_range_of_injective (fC_inj M a πa hker g)]

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.BlockCounting

open Formalism.MainNotions.S Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P.Phase

variable {R : Type} [CommRing R] {n : ℕ} (a : Loc.Pt R n)

abbrev sz : List ℕ := a.blocks.map (fun b => (b.2 : ℕ))

theorem sz_sum : (sz a).sum = n := a.size

def bk (i : Fin n) : ℕ := blk (sz a) i

def rv (i : Fin n) : Fin n :=
  ⟨revIn (sz a) i, by have := revIn_lt (sz a) i (by rw [sz_sum]; exact i.2); rwa [sz_sum] at this⟩

def cc (i : Fin n) : R := (((a.blocks.map Prod.fst).getD (bk a i) 1 : Rˣ) : R)

theorem rv_rv (i : Fin n) : rv a (rv a i) = i :=
  Fin.ext (revIn_revIn (sz a) i (by rw [sz_sum]; exact i.2))

theorem bk_rv (i : Fin n) : bk a (rv a i) = bk a i := blk_revIn (sz a) i (by rw [sz_sum]; exact i.2)

theorem bk_mono {i j : Fin n} (h : i ≤ j) : bk a i ≤ bk a j := blk_mono (sz a) i j h

theorem rv_anti {i j : Fin n} (h : i < j) (hb : bk a i = bk a j) : rv a j < rv a i :=
  revIn_anti (sz a) i j (by rw [sz_sum]; exact j.2) h hb

theorem rv_lt_of_bk_lt {i j : Fin n} (h : bk a i < bk a j) : rv a i < rv a j := by
  by_contra hc
  have := bk_mono a (not_lt.1 hc)
  rw [bk_rv, bk_rv] at this
  omega


theorem cc_rv (i : Fin n) : cc a (rv a i) = cc a i := by unfold cc; rw [bk_rv]

theorem cc_unit (i : Fin n) : IsUnit (cc a i) := Units.isUnit _

theorem mat_apply (i j : Fin n) : a.mat i j = if j = rv a i then cc a i else 0 := by
  have h := Formalism.MainNotions.LocalModelPeriodLattices.ptEntryL_eq a.blocks i j (by rw [a.size]; exact i.2)
  show Loc.ptEntryL a.blocks i j = _
  rw [h]
  simp only [Fin.ext_iff, rv, cc, bk]

theorem sameBlock_iff (i j : Fin n) : Loc.sameBlock a.blocks i j = true ↔ bk a i = bk a j :=
  Formalism.MainNotions.LocalOrbitGerms.Cls.sameBlock_iff a.blocks i j (by rw [a.size]; exact i.2) (by rw [a.size]; exact j.2)

end Formalism.L2.SG.Pf.BlockCounting

namespace Formalism.L2.SG.Pf.BlockCounting

open Formalism.MainNotions.S Matrix

variable {R : Type} [CommRing R] {n : ℕ} (a : Loc.Pt R n)

def bd (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := fun i j => if bk a i = bk a j then x i j else 0

def rvM (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := fun i j => M (rv a i) (rv a j)

variable {a}

theorem bd_lo {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : IsLoUni (bd a x) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold bd; split_ifs
    · exact (hx i j).1 h
    · rfl
  · subst h; unfold bd; rw [if_pos rfl]; exact (hx i i).2 rfl

theorem bd_one : bd a (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  unfold bd
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, if_neg]
    rintro rfl; exact h rfl

theorem bd_mul {x y : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) (hy : IsLoUni y) :
    bd a (x * y) = bd a x * bd a y := by
  ext i j
  simp only [bd, Matrix.mul_apply]
  by_cases hij : bk a i = bk a j
  · rw [if_pos hij]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : bk a i = bk a k
    · rw [if_pos hk, if_pos (hk.symm.trans hij)]
    · rw [if_neg hk, zero_mul]
      by_cases h1 : i < k
      · rw [(hx i k).1 h1, zero_mul]
      · by_cases h2 : k < j
        · rw [(hy k j).1 h2, mul_zero]
        · exfalso
          have e1 := bk_mono a (not_lt.1 h1)
          have e2 := bk_mono a (not_lt.1 h2)
          omega
  · rw [if_neg hij]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : bk a i = bk a k
    · rw [if_pos hk, if_neg (fun e => hij (hk.trans e)), mul_zero]
    · rw [if_neg hk, zero_mul]

theorem bd_inv {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : bd a x⁻¹ = (bd a x)⁻¹ := by
  obtain ⟨hi, -, h2⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx
  have : bd a x * bd a x⁻¹ = 1 := by rw [← bd_mul hx hi, h2, bd_one]
  exact (Matrix.inv_eq_right_inv this).symm

theorem bd_eq_one_iff {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) :
    bd a x = 1 ↔ ∀ i j : Fin n, i ≠ j → bk a i = bk a j → x i j = 0 := by
  constructor
  · intro h i j hij hb
    have := congrFun (congrFun h i) j
    simp only [bd, if_pos hb, Matrix.one_apply, if_neg hij] at this
    exact this
  · intro h
    ext i j
    unfold bd
    rw [Matrix.one_apply]
    split_ifs with h1 h2 h2
    · subst h2; exact (hx i i).2 rfl
    · exact h i j h2 h1
    · subst h2; exact absurd rfl h1
    · rfl

theorem rvM_mul (M N : Matrix (Fin n) (Fin n) R) : rvM a (M * N) = rvM a M * rvM a N := by
  ext i j
  simp only [rvM, Matrix.mul_apply]
  exact (Fintype.sum_equiv ⟨rv a, rv a, rv_rv a, rv_rv a⟩ _ _ (fun k => by simp [rv_rv])).symm

theorem rvM_one : rvM a (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  ext i j
  simp only [rvM, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun e => h (by rw [← rv_rv a i, e, rv_rv])), if_neg h]

theorem rvM_up {x : Matrix (Fin n) (Fin n) R} (hx : IsLoUni x) : IsUpUni (rvM a (bd a x)) := by
  intro i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold rvM bd
    split_ifs with hb
    · rw [bk_rv, bk_rv] at hb
      exact (hx _ _).1 (rv_anti a h hb.symm)
    · rfl
  · subst h; unfold rvM bd; rw [if_pos rfl]; exact (hx _ _).2 rfl

theorem bd_mat (x : Matrix (Fin n) (Fin n) R) : bd a x * a.mat = a.mat * rvM a (bd a x) := by
  ext i j
  have h1 : (bd a x * a.mat) i j = bd a x i (rv a j) * cc a (rv a j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (rv a j)]
    · rw [mat_apply, if_pos (rv_rv a j).symm]
    · intro k _ hk
      rw [mat_apply, if_neg (fun e => hk (by rw [e, rv_rv])), mul_zero]
    · simp
  have h2 : (a.mat * rvM a (bd a x)) i j = cc a i * bd a x i (rv a j) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
    · rw [mat_apply, if_pos rfl, rvM, rv_rv]
    · intro k _ hk
      rw [mat_apply, if_neg hk, zero_mul]
    · simp
  rw [h1, h2, cc_rv]
  unfold bd
  split_ifs with hb
  · have : cc a i = cc a j := by unfold cc; rw [hb, bk_rv]
    rw [this, mul_comm]
  · simp

def ccU (a : Loc.Pt R n) (i : Fin n) : Rˣ := (a.blocks.map Prod.fst).getD (bk a i) 1

theorem cc_eq (i : Fin n) : cc a i = (ccU a i : R) := rfl

theorem ccU_rv (i : Fin n) : ccU a (rv a i) = ccU a i := by unfold ccU; rw [bk_rv]

def matI (a : Loc.Pt R n) : Matrix (Fin n) (Fin n) R := fun i j => if j = rv a i then (((ccU a i)⁻¹ : Rˣ) : R) else 0

theorem matI_mul : matI a * a.mat = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
  · rw [matI, if_pos rfl, mat_apply, rv_rv, Matrix.one_apply]
    by_cases h : j = i
    · subst h; rw [if_pos rfl, if_pos rfl, cc_eq, ccU_rv]; exact Units.inv_mul _
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro k _ hk
    rw [matI, if_neg hk, zero_mul]
  · simp


theorem bd_of_stab {l ρ : Matrix (Fin n) (Fin n) R} (hl : IsLoUni l) (hρ : IsUpUni ρ)
    (h : l * a.mat * ρ = a.mat) : bd a l = l := by
  obtain ⟨hρi, -, hρ2⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv hρ
  have e : l * a.mat = a.mat * ρ⁻¹ := by
    calc l * a.mat = l * a.mat * (ρ * ρ⁻¹) := by rw [hρ2, Matrix.mul_one]
      _ = l * a.mat * ρ * ρ⁻¹ := by rw [Matrix.mul_assoc (l * a.mat)]
      _ = a.mat * ρ⁻¹ := by rw [h]
  ext i j
  unfold bd
  split_ifs with hb
  · rfl
  · symm
    rcases lt_or_gt_of_ne (show i ≠ j from fun h' => hb (by rw [h'])) with hij | hij
    · exact (hl i j).1 hij
    ·
      have e1 := congrFun (congrFun e i) (rv a j)
      have lhs : (l * a.mat) i (rv a j) = l i j * cc a j := by
        rw [Matrix.mul_apply, Finset.sum_eq_single j]
        · rw [mat_apply, if_pos rfl]
        · intro k _ hk
          rw [mat_apply, if_neg (fun e' => hk (by rw [← rv_rv a k, ← e', rv_rv])), mul_zero]
        · simp
      have rhs : (a.mat * ρ⁻¹) i (rv a j) = cc a i * ρ⁻¹ (rv a i) (rv a j) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (rv a i)]
        · rw [mat_apply, if_pos rfl]
        · intro k _ hk
          rw [mat_apply, if_neg hk, zero_mul]
        · simp
      have hlt : bk a j < bk a i := lt_of_le_of_ne (bk_mono a hij.le) (fun e' => hb e'.symm)
      have hz : ρ⁻¹ (rv a i) (rv a j) = 0 := (hρi _ _).1 (rv_lt_of_bk_lt a hlt)
      rw [lhs, rhs, hz, mul_zero] at e1
      exact ((cc_unit a j).mul_left_eq_zero).1 e1

theorem rho_of_stab {l ρ : Matrix (Fin n) (Fin n) R} (hl : IsLoUni l) (hρ : IsUpUni ρ)
    (h : l * a.mat * ρ = a.mat) : ρ = rvM a (bd a l⁻¹) := by
  have hb := bd_of_stab hl hρ h
  obtain ⟨hli, h1, -⟩ := Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hl
  have e : a.mat * ρ = l⁻¹ * a.mat := by
    calc a.mat * ρ = (l⁻¹ * l) * a.mat * ρ := by rw [h1, Matrix.one_mul]
      _ = l⁻¹ * (l * a.mat * ρ) := by simp only [Matrix.mul_assoc]
      _ = l⁻¹ * a.mat := by rw [h]
  have hbi : bd a l⁻¹ = l⁻¹ := by rw [bd_inv hl, hb]
  have e2 : a.mat * ρ = a.mat * rvM a (bd a l⁻¹) := by rw [e, ← bd_mat, hbi]
  calc ρ = matI a * (a.mat * ρ) := by rw [← Matrix.mul_assoc, matI_mul, Matrix.one_mul]
    _ = matI a * (a.mat * rvM a (bd a l⁻¹)) := by rw [e2]
    _ = rvM a (bd a l⁻¹) := by rw [← Matrix.mul_assoc, matI_mul, Matrix.one_mul]

end Formalism.L2.SG.Pf.BlockCounting

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut Formalism.L2.SG.Pf.BlockCounting

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D)

section Retr

variable {p}

def loU {l : MP p} (h : IsLoUni l) : GLp p :=
  ⟨l, l⁻¹, (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv h).2.2, (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv h).2.1⟩

def upU {l : MP p} (h : IsUpUni l) : GLp p :=
  ⟨l, l⁻¹, (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv h).2.2, (Formalism.L2.SG.Pf.ZsVolGrp.isUpUni_inv h).2.1⟩

variable (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))

theorem UP_lo (x : UP p) : IsLoUni (((x : GG p).1 : GLp p) : MP p) := x.2.1

theorem UP_up (x : UP p) : IsUpUni (((x : GG p).2.unop : GLp p) : MP p) := x.2.2

def retrFun (x : UP p) : UP p :=
  ⟨(loU (bd_lo (a := a) (UP_lo x)),
      MulOpposite.op (upU (rvM_up (a := a) (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (UP_lo x)).1))),
    bd_lo (UP_lo x), rvM_up (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv (UP_lo x)).1⟩

theorem retrFun_fst (x : UP p) : ((((retrFun a x : UP p) : GG p).1 : GLp p) : MP p) =
    bd a (((x : GG p).1 : GLp p) : MP p) := rfl

theorem retrFun_snd (x : UP p) : ((((retrFun a x : UP p) : GG p).2.unop : GLp p) : MP p) =
    rvM a (bd a (((x : GG p).1 : GLp p) : MP p)⁻¹) := rfl

theorem UP_ext {x y : UP p} (h1 : (((x : GG p).1 : GLp p) : MP p) = (((y : GG p).1 : GLp p) : MP p))
    (h2 : (((x : GG p).2.unop : GLp p) : MP p) = (((y : GG p).2.unop : GLp p) : MP p)) : x = y := by
  apply Subtype.ext
  apply Prod.ext
  · exact Units.ext h1
  · exact MulOpposite.unop_injective (Units.ext h2)

def retr : UP p →* UP p where
  toFun := retrFun a
  map_one' := by
    apply UP_ext
    · rw [retrFun_fst]; exact bd_one
    · rw [retrFun_snd]
      show rvM a (bd a (1 : MP p)⁻¹) = 1
      rw [inv_one, bd_one, rvM_one]
  map_mul' x y := by
    have hx := UP_lo x
    have hy := UP_lo y
    apply UP_ext
    · show bd a ((((x * y : UP p) : GG p).1 : GLp p) : MP p) = bd a _ * bd a _
      exact bd_mul hx hy
    · show rvM a (bd a ((((x * y : UP p) : GG p).1 : GLp p) : MP p)⁻¹) =
        rvM a (bd a (((y : GG p).1 : GLp p) : MP p)⁻¹) * rvM a (bd a (((x : GG p).1 : GLp p) : MP p)⁻¹)
      have e : ((((x * y : UP p) : GG p).1 : GLp p) : MP p) =
          (((x : GG p).1 : GLp p) : MP p) * (((y : GG p).1 : GLp p) : MP p) := rfl
      rw [e, Matrix.mul_inv_rev, bd_mul (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hy).1
        (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).1, rvM_mul]

theorem smul_UP (x : UP p) (X : MP p) :
    x • X = (((x : GG p).1 : GLp p) : MP p) * X * (((x : GG p).2.unop : GLp p) : MP p) := rfl

theorem retr_stab (x : UP p) : retr a x • a.mat = a.mat := by
  rw [smul_UP]
  show bd a _ * a.mat * rvM a (bd a _) = a.mat
  have hx := UP_lo x
  rw [bd_mat, Matrix.mul_assoc, ← rvM_mul, ← bd_mul hx (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).1,
    (Formalism.L2.SG.Pf.ZsVolGrp.isLoUni_inv hx).2.2, bd_one, rvM_one, Matrix.mul_one]

theorem retr_id (s : UP p) (hs : s • a.mat = a.mat) : retr a s = s := by
  rw [smul_UP] at hs
  apply UP_ext
  · exact bd_of_stab (UP_lo s) (UP_up s) hs
  · exact (rho_of_stab (UP_lo s) (UP_up s) hs).symm

theorem intLow_bd {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) : Formalism.MainNotions.S.TieN.IntLow (M p) (bd a l) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · unfold bd; rw [if_pos rfl]; exact h1 i
  · unfold bd; split_ifs
    · exact h2 i j hij
    · rfl
  · unfold bd; split_ifs
    · exact h3 i j
    · exact (M p).R.zero_mem

theorem intUp_rvM {l : MP p} (h : Formalism.MainNotions.S.TieN.IntLow (M p) l) :
    Formalism.MainNotions.S.TieN.IntUp (M p) (rvM a (bd a l)) := by
  have hl2 := h.2.1
  have hb := intLow_bd M a h
  obtain ⟨h1, h2, h3⟩ := hb
  refine ⟨fun i => h1 _, fun i j hij => ?_, fun i j => h3 _ _⟩
  show bd a l (rv a i) (rv a j) = 0
  unfold bd
  split_ifs with hb'
  · rw [bk_rv, bk_rv] at hb'
    exact hl2 _ _ (rv_anti a hij hb'.symm)
  · rfl

theorem retr_K (k : UP p) (hk : k ∈ KU M p) : retr a k ∈ KU M p := by
  obtain ⟨h1, -⟩ := hk
  have hi := (Formalism.L2.SG.Pf.ZsVolGrp.intLow_inv (M p) h1).1
  exact ⟨intLow_bd M a h1, intUp_rvM M a hi⟩

theorem blockRetr_holds : BlockRetr M p a := by
  refine ⟨retr a, ⟨fun x => (MulAction.mem_stabilizer_iff).symm, fun x => retr_stab a x,
    fun s hs => retr_id a s hs, fun x => MonoidHom.mem_ker, fun k hk => retr_K M a k hk⟩, fun x => ?_⟩
  have hx := UP_lo x
  constructor
  · intro h
    have h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1 := by
      rw [← retrFun_fst a x]
      show ((((retr a x : UP p) : GG p).1 : GLp p) : MP p) = 1
      rw [h]; rfl
    refine ⟨hx, fun i j hij hs => ?_⟩
    exact (bd_eq_one_iff hx).1 h1 i j hij ((sameBlock_iff a i j).1 hs)
  · rintro ⟨-, hV⟩
    have h1 : bd a (((x : GG p).1 : GLp p) : MP p) = 1 :=
      (bd_eq_one_iff hx).2 fun i j hij hb => hV i j hij ((sameBlock_iff a i j).2 hb)
    apply UP_ext
    · show bd a _ = _
      rw [h1]; rfl
    · show rvM a (bd a _) = _
      rw [bd_inv hx, h1, inv_one, rvM_one]; rfl

end Retr

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.CountBase

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.AtPt
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem zhatOM_sg (X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) :
    ZhatOM X * Sg D.host.E D.R.rS = X := by
  ext a b
  simp only [ZhatOM, Sg, Matrix.mul_diagonal]
  rw [mul_comm, ← mul_assoc, ← mul_pow]
  simp

theorem modMat_ord (hA : ∀ p, Agree δ M p) (T T' : ℕ) (p : PlF D) (hM : (M p).split = none)
    (w : Point D.host.E (D.R.rS + 1)) :
    Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) *
        (ptMat w).map (D.s.atP p).ιE *
        Matrix.diagonal (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf (⟨δ, M, hA⟩ : LocDat D) p a)) =
      modMat δ T T' p w := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hR : (D.s.atP p).split = none := by
    have h := (hA p).2.2.2.2.2
    rw [hM] at h
    cases h' : (D.s.atP p).split with
    | none => rfl
    | some sg => rw [h'] at h; exact h.elim
  ext a b
  rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
  by_cases hb : b = sgF w a
  · rw [if_pos hb, if_pos hb, modMat_blk Zd]
    simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul]
    subst hb
    ring
  · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]

theorem baseConj_L (hA : ∀ p, Agree δ M p) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)
    (hM : (M p).split = none) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    Formalism.L2.SG.Pf.ProdE.Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p +
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w = a.mat := by
  set Zd : LocDat D := ⟨δ, M, hA⟩
  have hY := Formalism.L2.SG.Pf.PCount.zzp_sgn_ord Zd u u' p hM (ZhatOM (ptMat w))
  rw [zhatOM_sg] at hY
  have hmat := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  rw [hmat]
  unfold Formalism.L2.SG.Pf.ProdE.Y0
  congr 1
  rw [show Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p =
    Formalism.L2.SG.CntLocal.ZZP (M := Zd.M) Zd.δ u u' p (ZhatOM (ptMat w)) * Formalism.L2.SG.LsDatumB.sgnP p from rfl, hY]
  exact modMat_ord hA _ _ p hM w

end Formalism.L2.SG.Pf.CountBase
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Corner

variable {R : Type*} [CommRing R] {n : ℕ}

theorem isLo_of_uni {L : Matrix (Fin n) (Fin n) R} (h : IsLoUni L) : IsLo L :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h a b).1 hab⟩

theorem isUp_of_uni {U : Matrix (Fin n) (Fin n) R} (h : IsUpUni U) : IsUp U :=
  ⟨fun a => (h a a).2 rfl, fun a b hab => (h b a).1 hab⟩

theorem uni_of_isLo {L : Matrix (Fin n) (Fin n) R} (h : IsLo L) : IsLoUni L :=
  fun a b => ⟨fun hab => h.2 a b hab, fun e => by subst e; exact h.1 a⟩

theorem uni_of_isUp {U : Matrix (Fin n) (Fin n) R} (h : IsUp U) : IsUpUni U :=
  fun a b => ⟨fun hab => h.2 b a hab, fun e => by subst e; exact h.1 a⟩

end Corner

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (p : PlF D)

def glOfLo {L : MP p} (h : IsLo L) : GLp p :=
  ⟨L, L⁻¹, Matrix.mul_nonsing_inv L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul L (by
      rw [Matrix.det_of_lowerTriangular L (fun a b hab => h.2 a b hab)]
      simp [h.1])⟩

def glOfUp {U : MP p} (h : IsUp U) : GLp p :=
  ⟨U, U⁻¹, Matrix.mul_nonsing_inv U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1]),
    Matrix.nonsing_inv_mul U (by
      rw [Matrix.det_of_upperTriangular (fun a b hab => h.2 b a hab)]
      simp [h.1])⟩

theorem glue_one_one {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ} :
    glue e (1 : Matrix (Fin n) (Fin n) Fp) 1 = 1 :=
  mat_eq e (by rw [glue_map_fst, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [glue_map_snd, Matrix.map_one _ (map_zero _) (map_one _)])

theorem corner_fix {Fp K : Type} [Field Fp] [CommRing K] [Algebra Fp K] (e : K ≃ₐ[Fp] Fp × Fp) {n : ℕ}
    {l ρ Δ : Matrix (Fin (n + 1)) (Fin (n + 1)) K} (hl : IsLoUni l) (hρ : IsUpUni ρ) (k1 k2 : Fp)
    (h1 : Δ.map (p1 e) = k1 • Ecorner n) (h2 : Δ.map (p2 e) = k2 • Ecorner n) : l * Δ * ρ = Δ := by
  apply mat_eq e
  · rw [Matrix.map_mul, Matrix.map_mul, h1, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]
  · rw [Matrix.map_mul, Matrix.map_mul, h2, Matrix.mul_smul, Matrix.smul_mul,
      lo_corner_up (isLo_map _ (isLo_of_uni hl)) (isUp_map _ (isUp_of_uni hρ))]

set_option maxHeartbeats 4000000 in

theorem baseAt_typed (hA : ∀ p, Agree δ M p) (g : Loc.SplitG (M p).L) (hM : (M p).split = some g)
    (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)) (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) :
    BaseAt M δ u u' w p a := by
  have hAg := (hA p).2.2.2.2.2
  rw [hM] at hAg
  obtain ⟨sg, hR, hge, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.e = sg.e ∧ g.q = sg.q := by
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hs] at hAg; exact hAg.elim
    · rw [hs] at hAg; exact ⟨sg, rfl, hAg.1, hAg.2⟩
  let Zd : LocDat D := ⟨δ, M, hA⟩
  have hzz := Formalism.L2.SG.Pf.PCountEx.zz_fact Zd p sg hR g hM hge hgq u u' w (L := 1) (B := 1)
    Formalism.L2.SG.Pf.PCountEx.isLo_one' Formalism.L2.SG.Pf.PCountEx.isUp_one'
  have e1 : Matrix.diagonal (cf Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e2 : Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cfi Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cf Zd p a * cfi Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cf_cfi Zd p),
      Matrix.diagonal_one]
  have e3 : Matrix.diagonal (cfi Zd p) * (1 : PairVal.MatR D).map ((p1 sg.e).comp (D.s.atP p).ιE) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  have e4 : Matrix.diagonal (cfi Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
      ((1 : PairVal.MatR D).map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
      Matrix.diagonal (cf Zd p) = 1 := by
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.mul_one, sg_sq, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal,
      show (fun a => cfi Zd p a * cf Zd p a) = fun _ => (1 : (D.s.atP p).Fp) from funext (cfi_cf Zd p),
      Matrix.diagonal_one]
  rw [e1, e2, e3, e4, glue_one_one, Matrix.one_mul, Matrix.mul_one] at hzz
  have hz : ZhatOM (ptMat w) = ptMat w * Sg D.host.E D.R.rS := by
    have h := Formalism.L2.SG.Pf.CountBase.zhatOM_sg (ptMat w)
    calc ZhatOM (ptMat w) = ZhatOM (ptMat w) * Sg D.host.E D.R.rS * Sg D.host.E D.R.rS := by
          rw [Matrix.mul_assoc, sg_sq, Matrix.mul_one]
      _ = ptMat w * Sg D.host.E D.R.rS := by rw [h]
  rw [Matrix.one_mul, Matrix.mul_one, ← hz] at hzz
  have hYg : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = _ := hzz
  obtain ⟨Gl, Gu, hGl, hGu, hT⟩ := Formalism.L2.SG.Pf.PCountEx.target_fact Zd p sg hR g hM hge hgq u u' w
  have hY0 : Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p = Gl * modMat δ (D.mem u).A.T (D.mem u').A.T p w * Gu :=
    hzz.trans hT
  have hshE : Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Formalism.MainNotions.S.LocalSplitGroups.cornerSh δ (D.mem u).A.T (D.mem u').A.T p w • Ecorner D.R.rS := by
    ext i j
    simp only [Formalism.L2.SG.Pf.LocOrbSumPf.shM, Ecorner, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  have hsh : Gl * Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w * Gu =
      Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [hshE, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hGl hGu]
  have hmod := Formalism.L2.SG.Pf.LocOrbSumPf.modShift_holds δ (D.mem u).A.T (D.mem u').A.T p w a ha
  refine ⟨⟨(glOfLo p hGl, MulOpposite.op (glOfUp p hGu)), uni_of_isLo hGl, uni_of_isUp hGu⟩, ?_, ?_⟩
  · show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
      Gl * a.mat * Gu
    rw [hmod, Matrix.mul_add, Matrix.add_mul, hsh, ← hY0]
  · intro x

    have hd1 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p1 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -((D.mem u).A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_fst, Formalism.L2.SG.Pf.PCount.mm1' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hd2 : (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w).map
        (p2 sg.e) = ((if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then ((D.mem u').A.T : (D.s.atP p).Fp) /
          (sg.q : (D.s.atP p).Fp) else 0) - ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))) •
          Ecorner D.R.rS := by
      rw [Matrix.map_sub _ (map_sub _), hYg, glue_map_snd, Formalism.L2.SG.Pf.PCount.mm2' Zd p sg hR g hM hge hgq, sub_sub_sub_cancel_left,
        ← sub_smul]
    have hfix := corner_fix sg.e x.2.1 x.2.2 _ _ hd1 hd2
    have hphi : phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat +
        (Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p - modMat δ (D.mem u).A.T (D.mem u').A.T p w) := by
      show Y0 M δ u u' w p * Formalism.L2.SG.LsDatumB.sgnP p + Formalism.L2.SG.Pf.LocOrbSumPf.shM δ (D.mem u).A.T (D.mem u').A.T p w =
        _
      rw [hmod]; abel
    rw [hphi, smul_def, smul_def, Matrix.mul_add, Matrix.add_mul, hfix]
    constructor
    · intro h; exact add_right_cancel h
    · intro h; rw [h]

theorem baseAt_holds (hA : ∀ p, Agree δ M p) (a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1))
    (ha : modPt δ (D.mem u).A.T (D.mem u').A.T p w = some a) : BaseAt M δ u u' w p a := by
  rcases hM : (M p).split with _ | g
  · have h := Formalism.L2.SG.Pf.CountBase.baseConj_L hA u u' w p hM a ha
    refine ⟨1, ?_, fun x => ?_⟩
    · rw [OneMemClass.coe_one, one_smul]; exact h
    · show _ ↔ _
      rw [show phi p δ (D.mem u).A.T (D.mem u').A.T w (Y0 M δ u u' w p) = a.mat from h]
  · exact baseAt_typed M δ u u' w p hA g hM a ha

end Formalism.L2.SG.Pf.CountAt
end
end

section
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.LocOrbSumPf MeasureTheory
open Classical

variable {D : Formalism.BasicNotions.D7}

theorem wtL_eq_wtZ (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (ha : modPt δ T T' p w = some a) (Y : MatP D p) :
    wtL M δ T T' p w Y = wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) := by
  have hmat : a.mat = modMat δ T T' p w + shM δ T T' p w := modShift_holds δ T T' p w a ha
  have hset : {xy : (Loc.IL (D.R.rS + 1) → (D.s.atP p).Ep) × (Loc.IN a → (D.s.atP p).Ep) |
      Loc.uLow xy.1 * modMat δ T T' p w * Loc.uUp a xy.2 ∈ kkOrb M p Y} =
      {xy | zAt a xy ∈ orbR (M p) (Y + shM δ T T' p w)} := by
    ext xy
    simp only [Set.mem_ofPred_eq]
    rw [mem_orbR_iff M δ T T' p w Y (zAt a xy), zAt_eq hmat xy, add_sub_cancel_right]
  unfold wtL wtZ muA
  simp only [ha]
  rw [hset]

theorem wtL_count (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {a : Loc.Pt (D.s.atP p).Ep (D.R.rS + 1)}
    (hOK : (M p).OK) (ha : modPt δ T T' p w = some a) {Y : MatP D p} (hY : ∀ i j, Y i j ∈ (M p).R) :
    {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.Finite ∧
    wtL M δ T T' p w Y = ({q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)}.ncard : ℝ) := by
  have := Formalism.MainNotions.LocalModelPeriodLattices.top_of_OK (M p) hOK
  have hZ0 : ∀ i j, (Y + shM δ T T' p w) i j ∈ (M p).R := fun i j =>
    add_mem (hY i j) (shM_mem M δ T T' p w i j)
  obtain ⟨hfin, hsum⟩ := LocOrbCut.wt_gen (M p) hOK a (Y + shM δ T T' p w) hZ0
  set S := {q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) |
      LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w)} with hSdef
  have hsupp : (Function.support (fun q : Formalism.FourierDecayAlt.A5.Cos (M p).R (Formalism.MainNotions.LocalModelPeriodLattices.tr a) =>
      if LocOrbCut.zQ (M p).R a q ∈ orbR (M p) (Y + shM δ T T' p w) then (1 : ℂ) else 0)) = S := by
    ext q
    simp [hSdef]
  rw [hsupp] at hfin
  refine ⟨hfin, ?_⟩
  rw [wtL_eq_wtZ M δ ha Y]
  have hc : (wtZ (M p) a (orbR (M p) (Y + shM δ T T' p w)) : ℂ) = (S.ncard : ℂ) := by
    rw [hsum, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [hsupp]; simp)]
    rw [Finset.sum_boole, Set.ncard_eq_toFinset_card S hfin]
    congr 2
    exact Finset.filter_true_of_mem (fun q hq => hfin.mem_toFinset.1 hq)
  exact_mod_cast hc

end Formalism.L2.SG.Pf.Coef
end
end

section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.ProdE Formalism.L2.SG.Pf.ProdEP2Cut
  Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.CountAt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem XP_eq_ZZP {p : PlF D} (hA : Agree δ M p) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L)
    (hU : IsUpUni U) (heq : ZhatOM (ZhatL (lf D F0) F') = L * ptMat w * U) :
    XP M δ u u' (p := p) w L U = Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') := by
  unfold XP Y0
  rw [← move δ M u u' hA L U hL hU, Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM, ← heq,
    Formalism.L2.SG.Pf.ZsVolGrp.zhatOM_zhatOM]

theorem int_zzp (γ : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1))
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D)
    (hE : Formalism.L2.SG.Pf.ZsVolCut.HypE M δ u u' F0 what₂ γ w F' L U) (p : PlF D) :
    ∀ i j, (Formalism.L2.SG.CntLocal.ZZP (M := M) δ u u' p (ZhatL (lf D F0) F') * Formalism.L2.SG.LsDatumB.sgnP p) i j ∈
      (M p).R := by
  obtain ⟨hAg, hT, hrows, -, hel, ⟨hPD, hmk⟩, hadm, -⟩ := hE
  have hTF := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam (hrows.1 γ.lam γ.mem)
  have hGt := Formalism.L2.SG.TermDef.Gt_mk hTF.1 ⟨F', hPD⟩
  have hGen := Formalism.L2.SG.TermDef.isGen_mk (gS D) hTF.2.2.2.1 ⟨F', hPD⟩
  rw [hmk] at hGt hGen
  have hEZ : F' ∈ Formalism.L2.SG.CntLocal.EZ (Formalism.L2.SG.CntLocal.Tn u') F0 γ.lam (ZhatL (lf D F0) F') :=
    ⟨⟨hPD.1, hPD.2.1, fun h => hel.1.2 (hGt.trans h)⟩, hadm, hGen.1 hel.1.1, hPD.2.2, rfl⟩
  have hI := PI.CntNotIntW.integral_on_pairs_holds D δ M hAg u u' hT F0 what₂ hrows γ.lam γ.mem (ZhatL (lf D F0) F') F' hEZ p
  intro i j
  simp only [Formalism.L2.SG.LsDatumB.sgnP, Matrix.mul_diagonal]
  exact Subring.mul_mem _ (hI i j) (Subring.pow_mem _ (Subring.neg_mem _ (Subring.one_mem _)) _)

end Formalism.L2.SG.Pf.CountAt
end
end
