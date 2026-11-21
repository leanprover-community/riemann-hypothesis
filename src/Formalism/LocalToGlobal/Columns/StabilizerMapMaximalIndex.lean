import Formalism.LocalToGlobal.Columns.LevelZeroComparisonBijective
import Formalism.LocalToGlobal.Columns.WithTopLevGTop
import Formalism.LocalToGlobal.Columns.StabMapRLInjective

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

def frameOfY {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet X.E n (Pr.vT u) Pr.vGs) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  Classical.choose (exists_frameD P d.2.lat)

theorem frameOfY_spec {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet X.E n (Pr.vT u) Pr.vGs) :
    ∀ x, frameOfY u P d x ∈ localization₂ P.asIdeal d.1.N ↔ x ∈ stdAt X.E n P :=
  Classical.choose_spec (exists_frameD P d.2.lat)

variable (hm : R.m = m2 + 2)

def topIdx : (L₀.withTop m2 Λt Θt).β R.m := ChIdx.top L₀ m2 Λt Θt (by omega)

def tilPtY (d : DecoSet X.E (R.N R.m - 1) ∅ SG') : PtY W cst (L₀.withTop m2 Λt Θt) u m2 R.m (topIdx L₀ m2 Λt Θt hm) :=
  ⟨(⟨(tilR hSG u d, fun P => frameOfY u P.1 (tilR hSG u d)), fun P x => frameOfY_spec u P.1 (tilR hSG u d) x⟩, Set.univ), by
    classical
    show Set.univ ∈ (if R.m = m2 + 1 then ybSet sel mu cst (tilR hSG u d).1.N else {Set.univ})
    rw [if_neg (by omega)]
    rfl⟩


def tilY (c : (ptGSD W ΛM).Cl) : (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).Cl :=
  clsY (topIdx L₀ m2 Λt Θt hm) (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))

def TopLevQ : Prop :=
  ∀ (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G), s • d = d →
    ∀ (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (h : (frameOfY u P.1 (tilR hSG u d))⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d) ∈ GLint X.E (R.N R.m) P.1),
      (⟨_, h⟩ : ↥(GLint X.E (R.N R.m) P.1)) ∈ (Θt R.m P).H

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm}

theorem localization_tilR_fixed (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) {d : DecoSet X.E (R.N R.m - 1) ∅ SG'} {s : (ptGSD W ΛM).G}
    (hs : s • d = d) (P : HeightOneSpectrum (𝓞 X.E)) :
    localization₂ P.asIdeal (tilR hSG u d).1.N = localization₂ P.asIdeal (gmap (extR R hSG (s.1, s.2.1)).1.1 (tilR hSG u d).1.N) := by
  have hsd : Deco.act s.1.1 s.2.1 d.1 = d.1 := by
    have h0 := congrArg Subtype.val hs
    exact h0
  have key : ∀ {N : ℕ} (hN : N = R.N R.m - 1 + 1),
      Deco.act (extUH hN s.1).1 (extGH hN s.2.1) (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 =
        (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 := by
    intro N hN
    subst hN
    have hok : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok := d.2.til (conj_piT_notMem hPr u) hpi
    have e : (DecoSet.tilH (ST := Pr.vT u) (rfl : R.N R.m - 1 + 1 = R.N R.m - 1 + 1) (Pr.piT u) d).1 =
        d.1.til (ST := Pr.vT u) (Pr.piT u) := by
      show (DecoSet.til (ST := Pr.vT u) (Pr.piT u) d).1 = _
      unfold DecoSet.til
      rw [dif_pos hok]
    rw [e]
    show Deco.act (extE s.1.1) (extG s.2.1) _ = _
    rw [← Deco.til_act, hsd]
  have hN : gmap (extR R hSG (s.1, s.2.1)).1.1 (tilR hSG u d).1.N = (tilR hSG u d).1.N :=
    congrArg Deco.N (key (N_m_succ R))
  rw [hN]

def extYg (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).G :=
  ((extR R hSG (s.1, s.2.1)).1, ⟨(extR R hSG (s.1, s.2.1)).2, hL s.2⟩,
    ⟨fun P => ⟨(frameOfY u P.1 (tilR hSG u d))⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d),
      frame_move (frameOfY_spec u P.1 _) (frameOfY_spec u P.1 _) (localization_tilR_fixed hPr hpi hs P.1)⟩,
      fun P _ => hQ d s hs P _⟩)


theorem extYg_smul (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G) (hs : s • d = d) :
    extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs • tilPtY W cst L₀ u m2 Λt Θt hSG hm d =
      tilPtY W cst L₀ u m2 Λt Θt hSG hm d := by
  have hsd : Deco.act s.1.1 s.2.1 d.1 = d.1 := by
    have h0 := congrArg Subtype.val hs
    exact h0
  have key : ∀ {N : ℕ} (hN : N = R.N R.m - 1 + 1),
      Deco.act (extUH hN s.1).1 (extGH hN s.2.1) (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 =
        (DecoSet.tilH (ST := Pr.vT u) hN (Pr.piT u) d).1 := by
    intro N hN
    subst hN
    have hok : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok := d.2.til (conj_piT_notMem hPr u) hpi
    have e : (DecoSet.tilH (ST := Pr.vT u) (rfl : R.N R.m - 1 + 1 = R.N R.m - 1 + 1) (Pr.piT u) d).1 =
        d.1.til (ST := Pr.vT u) (Pr.piT u) := by
      show (DecoSet.til (ST := Pr.vT u) (Pr.piT u) d).1 = _
      unfold DecoSet.til
      rw [dif_pos hok]
    rw [e]
    show Deco.act (extE s.1.1) (extG s.2.1) _ = _
    rw [← Deco.til_act, hsd]
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      show (Deco.act (extUH (N_m_succ R) s.1).1 (extGH (N_m_succ R) s.2.1)
          (DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG =
        ((DecoSet.tilH (ST := Pr.vT u) (N_m_succ R) (Pr.piT u) d).1).res hSG
      rw [key]
    · funext P
      show (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d) *
          ((frameOfY u P.1 (tilR hSG u d))⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * frameOfY u P.1 (tilR hSG u d))⁻¹ = frameOfY u P.1 (tilR hSG u d)
      group
  · have hmem := (extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ d s hs •
      tilPtY W cst L₀ u m2 Λt Θt hSG hm d).2
    classical
    change _ ∈ (if R.m = m2 + 1 then ybSet sel mu cst _ else {Set.univ}) at hmem
    rw [if_neg (by omega)] at hmem
    exact hmem

def stabilizerMapMaximalIndex (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      MulAction.stabilizer ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).G
        (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.rep
          (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
            (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))) where
  toFun s := ⟨(((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)))⁻¹ *
      extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
      ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.mv
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c)), by
    have h1 := ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.mv_smul
      (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))
    refine MulAction.mem_stabilizer_iff.2 ?_
    show (_ * _ * _) • ((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).outSec.rep
      (((chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m).mem (topIdx L₀ m2 Λt Θt hm)).cls
        (tilPtY W cst L₀ u m2 Λt Θt hSG hm ((ptGSD W ΛM).outSec.rep c))) = _
    rw [mul_smul, mul_smul, h1, extYg_smul, inv_smul_eq_iff, h1]⟩
  map_one' := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ 1 _ * _ = 1
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) 1 (one_smul _ _) = 1 := by
      have e1 : (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)) = 1 := map_one (extR R hSG)
      apply Prod.ext
      · show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1 = 1
        rw [e1]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).2 = 1
          rw [e1]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * ((extR R hSG ((1 : (ptGSD W ΛM).G).1, (1 : (ptGSD W ΛM).G).2.1)).1.1) * frameOfY u P.1 _ = 1
          rw [e1]
          have e2 : ((1 : UF X.E (R.N R.m) × GLG X.E (R.N R.m) Pr.vGs).1 : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) = 1 := rfl
          rw [e2]
          group
    rw [e, mul_one, inv_mul_cancel]
  map_mul' s t := by
    apply Subtype.ext
    show _ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ (s.1 * t.1) _ * _ =
      (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) * _) *
        (_ * extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) * _)
    have e : extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ ((ptGSD W ΛM).outSec.rep c) (s.1 * t.1) (MulAction.mem_stabilizer_iff.1 (s * t).2) =
        extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ s.1 (MulAction.mem_stabilizer_iff.1 s.2) *
          extYg (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ _ t.1 (MulAction.mem_stabilizer_iff.1 t.2) := by
      have em : extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1) = extR R hSG (s.1.1, s.1.2.1) * extR R hSG (t.1.1, t.1.2.1) :=
        map_mul (extR R hSG) (s.1.1, s.1.2.1) (t.1.1, t.1.2.1)
      apply Prod.ext
      · show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1 = (extR R hSG (s.1.1, s.1.2.1)).1 * (extR R hSG (t.1.1, t.1.2.1)).1
        rw [em]
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          show (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).2 = (extR R hSG (s.1.1, s.1.2.1)).2 * (extR R hSG (t.1.1, t.1.2.1)).2
          rw [em]
          rfl
        · apply Subtype.ext
          funext P
          apply Subtype.ext
          show (frameOfY u P.1 _)⁻¹ * (extR R hSG ((s.1 * t.1).1, (s.1 * t.1).2.1)).1.1 * frameOfY u P.1 _ =
            ((frameOfY u P.1 _)⁻¹ * (extR R hSG (s.1.1, s.1.2.1)).1.1 * frameOfY u P.1 _) *
              ((frameOfY u P.1 _)⁻¹ * (extR R hSG (t.1.1, t.1.2.1)).1.1 * frameOfY u P.1 _)
          rw [em]
          show _ * ((extR R hSG (s.1.1, s.1.2.1)).1.1 * (extR R hSG (t.1.1, t.1.2.1)).1.1) * _ = _
          group
    rw [e]
    group

def stabMapY (hPr : Pr.Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL (Λt R.m) hSG ΛM) (hQ : TopLevQ W u Θt hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →*
      FamStab (chFY W sel mu cst (L₀.withTop m2 Λt Θt) u m2 R.m) (tilY W cst L₀ u m2 Λt Θt hSG ΛM hm c) :=
  stabilizerMapMaximalIndex (W := W) (cst := cst) (L₀ := L₀) (m2 := m2) (hm := hm) hPr hpi hL hQ c


end Top

end Formalism.L2.Col
