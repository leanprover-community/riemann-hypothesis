import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCIface
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ToMatrixLin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemidirectExistsOfParts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ConjDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.OrthogonalInvarianceOfStableRankOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.NCDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemiAlg

section
noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type} [AddCommGroup Q] [TopologicalSpace Q] [ContinuousAdd Q]

structure CoordHyp (N A N1 Z : Subgroup G) (Lev : G → G) (sH : Q → G) (yQ : N1 → Q) : Prop where
  hAN : A ≤ N
  coordinate_level_le : N1 ≤ N
  hZN1 : Z ≤ N1
  cLev : Continuous Lev
  csH : Continuous sH
  cyQ : Continuous yQ
  lev_mem : ∀ n ∈ N, Lev n ∈ A
  lev_rest : ∀ n ∈ N, (Lev n)⁻¹ * n ∈ N1
  triv : ∀ u ∈ A, u ∈ N1 → u = 1
  norm1 : ∀ n ∈ N, ∀ m ∈ N1, n * m * n⁻¹ ∈ N1
  sH_mem : ∀ y, sH y ∈ N1
  dec : ∀ m : N1, (sH (yQ m))⁻¹ * (m : G) ∈ Z
  yQ_sH : ∀ y z (hz : z ∈ Z), yQ ⟨sH y * z, N1.mul_mem (sH_mem y) (hZN1 hz)⟩ = y
  cent : ∀ z ∈ Z, ∀ m ∈ N1, z * m = m * z
  mul : ∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Z

variable {N A N1 Z : Subgroup G} {Lev : G → G} {sH : Q → G} {yQ : N1 → Q}

theorem lev_eq (H : CoordHyp N A N1 Z Lev sH yQ) (u : A) (w : G) (hw : w ∈ N1) :
    Lev ((u : G) * w) = u := by
  have hg : (u : G) * w ∈ N := N.mul_mem (H.hAN u.2) (H.coordinate_level_le hw)
  set v := Lev ((u : G) * w) with hv
  have h1 : v⁻¹ * (u : G) ∈ N1 := by
    have : v⁻¹ * (u : G) = (v⁻¹ * ((u : G) * w)) * w⁻¹ := by group
    rw [this]
    exact N1.mul_mem (H.lev_rest _ hg) (N1.inv_mem hw)
  have h2 : v⁻¹ * (u : G) ∈ A := A.mul_mem (A.inv_mem (H.lev_mem _ hg)) u.2
  have h3 := H.triv _ h2 h1
  have : (u : G) = v := by
    calc (u : G) = v * (v⁻¹ * u) := by group
      _ = v := by rw [h3, mul_one]
  exact this.symm

def cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) : N :=
  ⟨(p.1 : G) * sH p.2.1 * (p.2.2 : G),
    N.mul_mem (N.mul_mem (H.hAN p.1.2) (H.coordinate_level_le (H.sH_mem _))) (H.coordinate_level_le (H.hZN1 p.2.2.2))⟩

def cm (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : N1 :=
  ⟨(Lev n)⁻¹ * (n : G), H.lev_rest n n.2⟩

def cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : A × (Q × Z) :=
  (⟨Lev n, H.lev_mem n n.2⟩, yQ (cm H n), ⟨(sH (yQ (cm H n)))⁻¹ * (cm H n : G), H.dec _⟩)

theorem cinv_cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    cinv H (cfun H p) = p := by
  obtain ⟨u, y, z⟩ := p
  have hw : sH y * (z : G) ∈ N1 := N1.mul_mem (H.sH_mem y) (H.hZN1 z.2)
  have hL : Lev ((u : G) * sH y * (z : G)) = u := by
    rw [mul_assoc]; exact lev_eq H u _ hw
  have hm : cm H (cfun H (u, y, z)) = ⟨sH y * (z : G), hw⟩ := by
    apply Subtype.ext
    simp only [cm, cfun]
    rw [hL]; group
  have hy : yQ (cm H (cfun H (u, y, z))) = y := by
    rw [hm]; exact H.yQ_sH y z z.2
  refine Prod.ext (Subtype.ext ?_) (Prod.ext hy (Subtype.ext ?_))
  · simp only [cinv, cfun]; exact hL
  · simp only [cinv]
    rw [hy, hm]
    group

theorem cfun_cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : cfun H (cinv H n) = n := by
  apply Subtype.ext
  simp only [cfun, cinv, cm]
  group

theorem continuous_cm (H : CoordHyp N A N1 Z Lev sH yQ) : Continuous (cm H) :=
  Continuous.subtype_mk ((H.cLev.comp continuous_subtype_val).inv.mul continuous_subtype_val) _

def cHomeo (H : CoordHyp N A N1 Z Lev sH yQ) : (A × (Q × Z)) ≃ₜ N where
  toFun := cfun H
  invFun := cinv H
  left_inv := cinv_cfun H
  right_inv := cfun_cinv H
  continuous_toFun := Continuous.subtype_mk
    (((continuous_subtype_val.comp continuous_fst).mul
      (H.csH.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))) _
  continuous_invFun := by
    have h1 := continuous_cm H
    refine Continuous.prodMk (Continuous.subtype_mk (H.cLev.comp continuous_subtype_val) _)
      (Continuous.prodMk (H.cyQ.comp h1) (Continuous.subtype_mk ?_ _))
    exact (H.csH.comp (H.cyQ.comp h1)).inv.mul (continuous_subtype_val.comp h1)

theorem cHomeo_apply (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    ((cHomeo H p : N) : G) = (p.1 : G) * sH p.2.1 * (p.2.2 : G) := rfl

theorem coord_skew (H : CoordHyp N A N1 Z Lev sH yQ) (n0 : N) :
    ∃ (a0 : A) (t : A → Q) (c : A × Q → Z), Continuous t ∧ Continuous c ∧
      ∀ u y z, n0 * cHomeo H (u, y, z) = cHomeo H (a0 * u, y + t u, c (u, y) * z) := by
  set a0 : A := ⟨Lev n0, H.lev_mem n0 n0.2⟩
  set n1 : G := (Lev n0)⁻¹ * (n0 : G) with hn1
  have hn1m : n1 ∈ N1 := H.lev_rest n0 n0.2
  have hmf : ∀ u : A, (u : G)⁻¹ * n1 * u ∈ N1 := fun u => by
    have := H.norm1 ((u : G)⁻¹) (N.inv_mem (H.hAN u.2)) n1 hn1m
    simpa using this
  let mf : A → N1 := fun u => ⟨(u : G)⁻¹ * n1 * u, hmf u⟩
  have cmf : Continuous mf := Continuous.subtype_mk
    ((continuous_subtype_val.inv.mul continuous_const).mul continuous_subtype_val) _
  let t : A → Q := fun u => yQ (mf u)
  have ct : Continuous t := H.cyQ.comp cmf
  let zm : A → G := fun u => (sH (t u))⁻¹ * (mf u : G)
  have hzm : ∀ u, zm u ∈ Z := fun u => H.dec (mf u)
  let k : A × Q → G := fun p => sH (t p.1) * sH p.2 * (sH (t p.1 + p.2))⁻¹
  have hk : ∀ p, k p ∈ Z := fun p => H.mul _ _
  let c : A × Q → Z := fun p => ⟨k p * zm p.1, Z.mul_mem (hk p) (hzm p.1)⟩
  have cc : Continuous c := by
    refine Continuous.subtype_mk ?_ _
    have ct1 : Continuous (fun p : A × Q => t p.1) := ct.comp continuous_fst
    refine (((H.csH.comp ct1).mul (H.csH.comp continuous_snd)).mul
      (H.csH.comp (ct1.add continuous_snd)).inv).mul ?_
    exact (H.csH.comp ct1).inv.mul (continuous_subtype_val.comp (cmf.comp continuous_fst))
  refine ⟨a0, t, c, ct, cc, fun u y z => ?_⟩
  apply Subtype.ext
  show (n0 : G) * ((u : G) * sH y * (z : G)) = (Lev n0 * u) * sH (y + t u) * (k (u, y) * zm u * z)
  have e2 : (mf u : G) = sH (t u) * zm u := by
    show (mf u : G) = sH (t u) * ((sH (t u))⁻¹ * (mf u : G)); group
  have e3 : zm u * sH y = sH y * zm u := H.cent _ (hzm u) _ (H.sH_mem y)
  have e4 : sH (t u) * sH y = sH (t u + y) * k (u, y) := by
    have h := H.cent _ (hk (u, y)) _ (H.sH_mem (t u + y))
    calc sH (t u) * sH y = k (u, y) * sH (t u + y) := by show _ = sH (t u) * sH y * (sH (t u + y))⁻¹ * sH (t u + y); group
      _ = sH (t u + y) * k (u, y) := h
  have e1 : (n0 : G) * ((u : G) * sH y * (z : G)) = Lev n0 * u * (mf u : G) * sH y * z := by
    show _ = Lev n0 * u * ((u : G)⁻¹ * ((Lev n0)⁻¹ * (n0 : G)) * u) * sH y * z
    group
  rw [e1, e2, add_comm y (t u)]
  calc Lev n0 * (u : G) * (sH (t u) * zm u) * sH y * (z : G)
      = Lev n0 * u * sH (t u) * (zm u * sH y) * z := by group
    _ = Lev n0 * u * sH (t u) * (sH y * zm u) * z := by rw [e3]
    _ = Lev n0 * u * (sH (t u) * sH y) * zm u * z := by group
    _ = Lev n0 * u * (sH (t u + y) * k (u, y)) * zm u * z := by rw [e4]
    _ = (Lev n0 * u) * sH (t u + y) * (k (u, y) * zm u * z) := by group

end Gen

end PI.LevelKSplit.W.NC
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} [FiniteDimensional F E]

theorem isClosed_FixXp {r : ℕ} (P : Frame E M r) :
    IsClosed (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) := by
  have h : (FixXp (Af F) σ J P : Set (HA (Af F) σ J)) =
      ⋂ v, ⋂ (_ : InXperp (Af F) σ J P v), {g | lin (Af F) σ J g v = v} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [h]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    isClosed_eq (ExC.continuous_lin _) continuous_const

theorem ncoord_of_parts (hH : HeisP F E σ M J) (hL : LevP F E σ M J) : NCoord F E σ M J := by
  intro hJ hinv r P T hP
  obtain ⟨sH, csH, cyH, hs1, hdec, hyH, hZN1, hcent, hmul, hZnorm, hconj, hZconj⟩ :=
    hH hJ hinv r P T hP
  obtain ⟨A, Lev, hAN, hAcl, cLev, hLev, hAN1, hN1norm, hAcomm⟩ := hL hJ hinv r P T hP
  have hmemW : ∀ m : LevelUnipotentSubgroup (Af F) σ J P, ∀ a, yH (Af F) σ J P m a ∈ Wp (Af F) σ J P := by
    intro m a
    obtain ⟨y, hy, -⟩ := hdec m m.2
    rw [← hy a]; exact (y a).2
  let yQ : LevelUnipotentSubgroup (Af F) σ J P → (Fin r → Wp (Af F) σ J P) := fun m a =>
    ⟨yH (Af F) σ J P m a, hmemW m a⟩
  have H : CoordHyp (Nsub (Af F) σ J P) A (LevelUnipotentSubgroup (Af F) σ J P) (Zsub (Af F) σ J P) Lev sH yQ :=
    { hAN := hAN
      coordinate_level_le := inf_le_left
      hZN1 := hZN1
      cLev := cLev
      csH := csH
      cyQ := continuous_pi fun a => Continuous.subtype_mk
        ((continuous_apply a).comp (cyH.comp continuous_subtype_val)) _
      lev_mem := fun n hn => (hLev n hn).1
      lev_rest := fun n hn => (hLev n hn).2
      triv := hAN1
      norm1 := hN1norm
      sH_mem := hs1
      dec := fun m => by
        obtain ⟨y, hy, hz⟩ := hdec m m.2
        have : yQ m = y := funext fun a => Subtype.ext (hy a).symm
        rw [this]; exact hz
      yQ_sH := fun y z hz => funext fun a => Subtype.ext (hyH y z hz a)
      cent := hcent
      mul := hmul }
  refine ⟨A, Zsub (Af F) σ J P, cHomeo H, hAcl, ?_, fun n0 => coord_skew H n0, ?_⟩
  · show IsClosed ((Nsub (Af F) σ J P ⊓ FixXp (Af F) σ J P : Subgroup (HA (Af F) σ J)) :
      Set (HA (Af F) σ J))
    rw [Subgroup.coe_inf]
    exact (ExC.isClosed_Nsub hJ hinv P T hP).inter (isClosed_FixXp P)
  · intro h hh u y z
    obtain ⟨y', hy', hc⟩ := hconj h hh y
    refine ⟨y', hy', ?_⟩
    rw [cHomeo_apply, cHomeo_apply]
    have hu : h * (u : HA (Af F) σ J) * h⁻¹ = u := by rw [hAcomm h hh u u.2]; group
    have hz : h * (z : HA (Af F) σ J) * h⁻¹ = z := hZconj h hh z z.2
    calc h * ((u : HA (Af F) σ J) * sH y * (z : HA (Af F) σ J)) * h⁻¹
        = (h * u * h⁻¹) * (h * sH y * h⁻¹) * (h * z * h⁻¹) := by group
      _ = u * sH y' * z := by rw [hu, hc, hz]

end Ext

theorem ncoordAll_of (hH : HeisPAll) (hL : LevPAll) : NCoordAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact ncoord_of_parts (hH F E σ hσ M J hJ) (hL F E σ hσ M J hJ)

theorem levelSAll_of_semiNHS_heis_lev (hS : PI.LevelKSplit.W.ExS.SemiNHSAll) (hH : HeisPAll) (hL : LevPAll)
    (hV : PI.LevelKSplit.W.CD.ModVAll) (hA : NCAsmAll) : PI.LevelKSplit.LevelSAll :=
  levelSAll_of_parts hS (ncoordAll_of hH hL) hV hA

end PI.LevelKSplit.W.NC
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.SemiA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
  (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem piG_mem_H (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : piG hσσ hJ hP g hg ∈ Hsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub
  rw [mem_stabT]
  intro b
  rw [lin_piG]
  refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · rw [tupH, Fin.append_left]
    refine Fin.lastCases ?_ (fun a => ?_) b
    · rw [F0, Fin.snoc_last]
      exact SemiG.Dat.unipotent_proj_fixes_normal H _
    · rw [F0, Fin.snoc_castSucc]
      exact SemiG.Dat.Pi_e H _ a
  · rw [tupH, Fin.append_right]
    exact SemiG.Dat.Pi_f H _ b

theorem piG_of_H {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (hg : h ∈ Ssub R σ J P) :
    piG hσσ hJ hP h hg = h := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  unfold Hsub at hh
  rw [mem_stabT] at hh
  have he : ∀ a, lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := fun a => by
    have h1 := hh (Fin.castAdd r (Fin.castSucc a))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_castSucc] at h1
  have hz : lin R σ J h (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
    have h1 := hh (Fin.castAdd r (Fin.last r))
    rwa [tupH, Fin.append_left, F0, Fin.snoc_last] at h1
  have hf : ∀ a, lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := fun a => by
    have h1 := hh (Fin.natAdd (r + 1) a)
    rwa [tupH, Fin.append_right] at h1
  refine hext fun x => ?_
  rw [lin_piG]
  exact SemiG.Dat.Pi_of_fix H ⟨he, hz⟩ hf (uni_lin h) x

theorem piG_of_N {n : HA R σ J} (hn : n ∈ Nsub R σ J P) (hg : n ∈ Ssub R σ J P) :
    piG hσσ hJ hP n hg = 1 := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  have H := datR_hyp (R := R) hσσ hJ hP
  obtain ⟨-, hn2⟩ := hn
  refine hext fun x => ?_
  rw [lin_piG, lin_one]
  refine SemiG.Dat.Pi_of_N H (fun v hv => spanR_le Set.univ (hn2 v fun a => ?_)) x
  have h1 := hv a
  rwa [datR_h] at h1

theorem piG_mul {g g' : HA R σ J} (hg : g ∈ Ssub R σ J P) (hg' : g' ∈ Ssub R σ J P) :
    piG hσσ hJ hP (g * g') ((Ssub R σ J P).mul_mem hg hg') =
      piG hσσ hJ hP g hg * piG hσσ hJ hP g' hg' := by
  have hext : ∀ {g₁ g₂ : HA R σ J}, (∀ x, lin R σ J g₁ x = lin R σ J g₂ x) → g₁ = g₂ := by
    intro g₁ g₂ hgg
    have hm : ((HA.mat R σ J g₁ : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
        (HA.mat R σ J g₂ : GL (Fin M) (R ⊗[F] E)) := by
      ext i j
      have h1 := hgg (Pi.single j 1)
      simp only [lin, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
      exact congrFun h1 i
    exact Subtype.ext (Units.ext hm)
  refine hext fun x => ?_
  rw [lin_piG, lin_mul, lin_piG, lin_piG, Pi_lin_mul hσσ hJ hP hg hg']
  rfl

theorem mul_inv_piG_mem_N {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    s * (piG hσσ hJ hP s hs)⁻¹ ∈ Nsub R σ J P := by
  have H := datR_hyp (R := R) hσσ hJ hP
  set π := piG hσσ hJ hP s hs with hπ
  have hpe : ∀ b, lin R σ J π (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    rw [hπ, lin_piG]
    exact SemiG.Dat.Pi_e H _ b
  have hpie : ∀ b, lin R σ J π⁻¹ (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := fun b => by
    conv_lhs => rw [← hpe b]
    rw [lin_inv_lin]
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [lin_mul, hpie]
    exact S_e hs b
  · set u := lin R σ J π⁻¹ v with hu
    have hu' : ∀ a, (datR R σ J P T).h ((datR R σ J P T).e a) u = 0 := fun a => by
      rw [datR_h]
      show hR R σ J (ratV (F := F) R (P.e a)) u = 0
      rw [← hR_lin π, hpe, hu, lin_lin_inv]
      exact hv a
    have hZ : lin R σ J s (datR R σ J P T).z - (datR R σ J P T).z ∈
        Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
      spanR_le Set.univ (stabilizer_fixes_tail_coords hs)
    have h1 := SemiG.Dat.N_part H (mapX_S hs) (mapW_S hs) hZ u hu'
    have h2 : (datR R σ J P T).Pi (lin R σ J s) u = v := by
      rw [← lin_piG hσσ hJ hP s hs, ← hπ, hu, lin_lin_inv]
    rw [h2] at h1
    rw [lin_mul, ← hu]
    exact span_le_spanR h1

end R

end PI.LevelKSplit.W.SemiA
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.SemiT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {R : Type}
  [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  rw [piMat, PI.LevelKSplit.W.SemiG.Dat.Pi, map_add, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_comp, lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', Matrix.mul_assoc]

theorem mat_inv (g : HA R σ J) : HA.mat R σ J g⁻¹ = (HA.mat R σ J g)⁻¹ := rfl

theorem continuous_piMat : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : (fun g : HA R σ J => piMat (P := P) (T := T) g) = fun g =>
      LinearMap.toMatrix' (datR R σ J P T).pU + LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := funext piMat_eq
  rw [he]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)

theorem continuous_piMat_inv : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  exact (continuous_piMat (P := P) (T := T)).comp continuous_inv

variable (R) in

def fwdM (hP : P.IsStd σ J T) (p : Nsub R σ J P × Hsub R σ J P) : Ssub R σ J P :=
  ⟨(p.1 : HA R σ J) * (p.2 : HA R σ J), (Ssub R σ J P).mul_mem (N_le_S' (R := R) hP p.1.2) (H_le_S p.2.2)⟩

theorem continuous_fwdM (hP : P.IsStd σ J T) : Continuous (fwdM R hP) := by
  apply continuous_induced_rng.2
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

theorem continuous_piG : Continuous fun s : Ssub R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_piMat (P := P) (T := T)).comp continuous_subtype_val
  · exact (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val

variable (R) in

def bwdM (s : Ssub R σ J P) : Nsub R σ J P × Hsub R σ J P :=
  (⟨(s : HA R σ J) * (piG (R := R) hσσ hJ hP (s : HA R σ J) s.2)⁻¹, mul_inv_piG_mem_N hσσ hJ hP s.2⟩,
    ⟨piG (R := R) hσσ hJ hP (s : HA R σ J) s.2, piG_mem_H hσσ hJ hP (s : HA R σ J) s.2⟩)

theorem continuous_bwdM : Continuous (bwdM R hσσ hJ hP) := by
  have hpi := continuous_piG (R := R) hσσ hJ hP
  refine Continuous.prodMk ?_ ?_
  · apply continuous_induced_rng.2
    exact continuous_subtype_val.mul hpi.inv
  · apply continuous_induced_rng.2
    exact hpi

theorem bwd_fwd : Function.LeftInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  rintro ⟨n, h⟩
  have hnS := N_le_S' (R := R) hP n.2
  have hhS := H_le_S (R := R) h.2
  have key : piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J))
      ((Ssub R σ J P).mul_mem hnS hhS) = h := by
    rw [piG_mul hσσ hJ hP hnS hhS, piG_of_N hσσ hJ hP n.2 hnS, piG_of_H hσσ hJ hP h.2 hhS, one_mul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (n : HA R σ J) * (h : HA R σ J) *
      (piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J)) _)⁻¹ = n
    rw [key, mul_inv_cancel_right]
  · exact key

theorem fwd_bwd : Function.RightInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  intro s
  apply Subtype.ext
  exact inv_mul_cancel_right _ _

variable (R) in

def homeoNH : (Nsub R σ J P × Hsub R σ J P) ≃ₜ Ssub R σ J P where
  toFun := fwdM R hP
  invFun := bwdM R hσσ hJ hP
  left_inv := bwd_fwd hσσ hJ hP
  right_inv := fwd_bwd hσσ hJ hP
  continuous_toFun := continuous_fwdM hP
  continuous_invFun := continuous_bwdM (R := R) hσσ hJ hP

theorem semi_gen : Semi (Ssub R σ J P) (Nsub R σ J P) (Hsub R σ J P) :=
  ⟨fun _ hh _ hn => norm_N hh hn, homeoNH R hσσ hJ hP, fun _ => rfl⟩

end Cont

theorem semidirect_topological_all : PI.LevelKSplit.W.ExS.SemiNHSAll := by
  unfold PI.LevelKSplit.W.ExS.SemiNHSAll PI.LevelKSplit.ForAllCM PI.LevelKSplit.W.ExS.SemiNHS
  intro F E _ _ _ _ _ σ _ M J _ hJ hσσ r P T hP
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact semi_gen hσσ hJ hP

end PI.LevelKSplit.W.SemiT
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]

def p1 : (R1 × R2) ⊗[F] E →+* R1 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.fst F R1 R2) (AlgHom.id F E)).toRingHom

def p2 : (R1 × R2) ⊗[F] E →+* R2 ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.snd F R1 R2) (AlgHom.id F E)).toRingHom



variable {R1 R2} in

def crd (R : Type) [CommRing R] [Algebra F R] :
    R ⊗[F] E ≃ₗ[R] (Fin (Module.finrank F E) → R) :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun

theorem crd_symm (R : Type) [CommRing R] [Algebra F R] (c : Fin (Module.finrank F E) → R) :
    (crd (E := E) R).symm c = ∑ k, c k ⊗ₜ (Module.finBasis F E k) := by
  simp [crd, Module.Basis.equivFun_symm_apply, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']

theorem fst_coordinates (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 x = (crd R1).symm (fun k => (crd (R1 × R2) x k).1) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  rw [crd_symm, crd_symm, map_sum]
  rfl

theorem snd_coordinates (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 x = (crd R2).symm (fun k => (crd (R1 × R2) x k).2) := by
  conv_lhs => rw [← (crd (E := E) (R1 × R2)).symm_apply_apply x]
  rw [crd_symm, crd_symm, map_sum]
  rfl

def qq (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : (R1 × R2) ⊗[F] E :=
  (crd (R1 × R2)).symm (fun k => (crd R1 a k, crd R2 b k))

theorem fst_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p1 R1 R2 (qq R1 R2 a b) = a := by
  unfold qq
  rw [fst_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R1).symm_apply_apply a

theorem snd_pair (a : R1 ⊗[F] E) (b : R2 ⊗[F] E) : p2 R1 R2 (qq R1 R2 a b) = b := by
  unfold qq
  rw [snd_coordinates, LinearEquiv.apply_symm_apply]
  exact (crd R2).symm_apply_apply b

theorem qq_p (x : (R1 × R2) ⊗[F] E) : qq R1 R2 (p1 R1 R2 x) (p2 R1 R2 x) = x := by
  apply (crd (E := E) (R1 × R2)).injective
  unfold qq
  rw [LinearEquiv.apply_symm_apply, fst_coordinates, snd_coordinates, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem ext_p {x y : (R1 × R2) ⊗[F] E} (h1 : p1 R1 R2 x = p1 R1 R2 y)
    (h2 : p2 R1 R2 x = p2 R1 R2 y) : x = y := by
  rw [← qq_p R1 R2 x, ← qq_p R1 R2 y, h1, h2]

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem fst_conj_bis (x : (R1 × R2) ⊗[F] E) :
    p1 R1 R2 (sigR (R1 × R2) σ x) = sigR R1 σ (p1 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem snd_conj_alt (x : (R1 × R2) ⊗[F] E) :
    p2 R1 R2 (sigR (R1 × R2) σ x) = sigR R2 σ (p2 R1 R2 x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem fst_inclusion (e : E) : p1 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R1 e := rfl

theorem snd_inclusion (e : E) : p2 R1 R2 (inclR (F := F) (R1 × R2) e) = inclR (F := F) R2 e := rfl

theorem map_fst_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (sigR (R1 × R2) σ) P).map (p1 R1 R2) =
      Formalism.UG.cT (sigR R1 σ) (P.map (p1 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, fst_conj_bis]

theorem map_snd_conj_transpose (P : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)) :
    (Formalism.UG.cT (sigR (R1 × R2) σ) P).map (p2 R1 R2) =
      Formalism.UG.cT (sigR R2 σ) (P.map (p2 R1 R2)) := by
  ext i j
  simp [Formalism.UG.cT, snd_conj_alt]

theorem map_fst_form : (JR (F := F) (R1 × R2) J).map (p1 R1 R2) = JR (F := F) R1 J := by
  ext i j
  exact fst_inclusion R1 R2 (J i j)

theorem map_snd_form : (JR (F := F) (R1 × R2) J).map (p2 R1 R2) = JR (F := F) R2 J := by
  ext i j
  exact snd_inclusion R1 R2 (J i j)

def mlift (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E) :=
  Matrix.of fun i j => qq R1 R2 ((1 : Matrix (Fin M) (Fin M) (R1 ⊗[F] E)) i j) (m i j)

theorem matrix_lift_fst (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p1 R1 R2) = 1 := by
  ext i j
  exact fst_pair R1 R2 _ _

theorem matrix_lift_snd (m : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) : (mlift R1 R2 m).map (p2 R1 R2) = m := by
  ext i j
  exact snd_pair R1 R2 _ _

theorem mext {P Q : Matrix (Fin M) (Fin M) ((R1 × R2) ⊗[F] E)} (h1 : P.map (p1 R1 R2) = Q.map (p1 R1 R2))
    (h2 : P.map (p2 R1 R2) = Q.map (p2 R1 R2)) : P = Q := by
  ext i j
  exact ext_p R1 R2 (congrArg (· i j) h1) (congrArg (· i j) h2)

theorem mlift_mul (m m' : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) :
    mlift R1 R2 m * mlift R1 R2 m' = mlift R1 R2 (m * m') := by
  apply mext
  · rw [Matrix.map_mul, matrix_lift_fst, matrix_lift_fst, matrix_lift_fst, one_mul]
  · rw [Matrix.map_mul, matrix_lift_snd, matrix_lift_snd, matrix_lift_snd]

theorem mlift_one : mlift R1 R2 (1 : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = 1 := by
  apply mext
  · rw [matrix_lift_fst, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [matrix_lift_snd, Matrix.map_one _ (map_zero _) (map_one _)]

def glift (u : GL (Fin M) (R2 ⊗[F] E)) : GL (Fin M) ((R1 × R2) ⊗[F] E) :=
  ⟨mlift R1 R2 (u : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)), mlift R1 R2 (↑u⁻¹ : Matrix (Fin M) (Fin M) _),
    by rw [mlift_mul, u.mul_inv, mlift_one], by rw [mlift_mul, u.inv_mul, mlift_one]⟩

theorem glift_mem (g : HA R2 σ J) : glift R1 R2 (HA.mat R2 σ J g) ∈ HR (R1 × R2) σ J := by
  have hg : HA.mat R2 σ J g ∈ HR R2 σ J := g.2
  change Formalism.UG.cT (sigR R2 σ) ((HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) * JR (F := F) R2 J *
    (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) R2 J at hg
  change Formalism.UG.cT (sigR (R1 × R2) σ) (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) *
    JR (F := F) (R1 × R2) J * mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) = JR (F := F) (R1 × R2) J
  apply mext
  · rw [Matrix.map_mul, Matrix.map_mul, map_fst_conj_transpose, map_fst_form, matrix_lift_fst]
    ext i j
    simp [Formalism.UG.cT, Matrix.one_apply]
  · rw [Matrix.map_mul, Matrix.map_mul, map_snd_conj_transpose, map_snd_form, matrix_lift_snd]
    exact hg

def lift (g : HA R2 σ J) : HA (R1 × R2) σ J :=
  (⟨glift R1 R2 (HA.mat R2 σ J g), glift_mem R1 R2 σ J g⟩ : ↥(HR (R1 × R2) σ J))

def psiE : (Fin M → (R1 × R2) ⊗[F] E) ≃+ (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) where
  toFun x := (fun i => p1 R1 R2 (x i), fun i => p2 R1 R2 (x i))
  invFun y := fun i => qq R1 R2 (y.1 i) (y.2 i)
  left_inv x := funext fun i => qq_p R1 R2 (x i)
  right_inv y := Prod.ext (funext fun i => fst_pair R1 R2 _ _) (funext fun i => snd_pair R1 R2 _ _)
  map_add' x y := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> simp


theorem psi_lin (g : HA R2 σ J) (x : Fin M → (R1 × R2) ⊗[F] E) :
    psiE R1 R2 (lin (R1 × R2) σ J (lift R1 R2 σ J g) x) =
      ((psiE R1 R2 x).1, lin R2 σ J g (psiE R1 R2 x).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show p1 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) = p1 R1 R2 (x i)
    rw [RingHom.map_mulVec, matrix_lift_fst, Matrix.one_mulVec]
    rfl
  · show p2 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) =
      Matrix.mulVec (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) (fun k => p2 R1 R2 (x k)) i
    rw [RingHom.map_mulVec, matrix_lift_snd]
    rfl

end Ring

end PI.LevelKSplit.W.MVA
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem cancel_prod {X Y : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (ν : Measure X) [ν.IsAddHaarMeasure] [SFinite ν] (a b : Measure Y) [SFinite a] [SFinite b]
    (h : ν.prod a = ν.prod b) : a = b := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (0 : X)
  have h0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hinf : ν K ≠ ⊤ := hK.measure_lt_top.ne
  ext s hs
  have h1 := congrArg (fun m => m (K ×ˢ s)) h
  simp only [Measure.prod_prod] at h1
  exact (ENNReal.mul_right_inj h0 hinf).1 h1

section Top

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R) := by
  first
  | exact continuous_induced_dom
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).toLinearMap
  | fun_prop
  | (delta crd; exact LinearMap.continuous_of_finiteDimensional _)

theorem continuous_crd_symm (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] : Continuous (crd (F := F) (E := E) R).symm := by
  first
  | exact continuous_induced_rng.2 (by simpa [Function.comp_def] using continuous_id)
  | exact IsModuleTopology.continuous_of_linearMap (crd (F := F) (E := E) R).symm.toLinearMap
  | fun_prop

variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [TopologicalSpace R2] [IsTopologicalRing R2]

theorem continuous_first_orbit_map : Continuous (p1 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p1 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) := by
    intro x
    apply (crd (F := F) (E := E) R1).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p1, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, Prod.fst_add, hx, hy]
  rw [show p1 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R1).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).1) from funext key]
  exact (continuous_crd_symm R1).comp
    (continuous_pi fun i => continuous_fst.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_p2 : Continuous (p2 (F := F) (E := E) R1 R2) := by
  have key : ∀ x, p2 (F := F) (E := E) R1 R2 x =
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) := by
    intro x
    apply (crd (F := F) (E := E) R2).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      simp [crd, p2, Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Pi.add_apply, Prod.snd_add, hx, hy]
  rw [show p2 (F := F) (E := E) R1 R2 = fun x =>
      (crd (F := F) (E := E) R2).symm (fun i => (crd (F := F) (E := E) (R1 × R2) x i).2) from funext key]
  exact (continuous_crd_symm R2).comp
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_crd (R1 × R2))))

theorem continuous_qq :
    Continuous (fun y : (R1 ⊗[F] E) × (R2 ⊗[F] E) => qq R1 R2 y.1 y.2) := by
  delta qq
  exact (continuous_crd_symm (R1 × R2)).comp (continuous_pi fun k =>
    (((continuous_apply k).comp (continuous_crd R1)).comp continuous_fst).prodMk
      (((continuous_apply k).comp (continuous_crd R2)).comp continuous_snd))

variable {M : ℕ}

theorem continuous_psiE : Continuous (psiE (F := F) (E := E) (M := M) R1 R2) := by
  show Continuous (fun x : Fin M → (R1 × R2) ⊗[F] E =>
    (fun i => p1 (F := F) (E := E) R1 R2 (x i), fun i => p2 (F := F) (E := E) R1 R2 (x i)))
  exact (continuous_pi fun i => (continuous_first_orbit_map R1 R2).comp (continuous_apply i)).prodMk
    (continuous_pi fun i => (continuous_p2 R1 R2).comp (continuous_apply i))

set_option maxHeartbeats 800000 in

theorem continuous_qqv :
    Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => fun i => qq R1 R2 (y.1 i) (y.2 i)) := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) => (y.1 i, y.2 i)) :=
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)
  have h2 := (continuous_qq R1 R2).comp h1
  simpa only [Function.comp_def] using h2

set_option maxHeartbeats 1000000 in
theorem continuous_psiE_symm : Continuous (psiE (F := F) (E := E) (M := M) R1 R2).symm := by
  show Continuous (fun y : (Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E) =>
    fun i => qq R1 R2 (y.1 i) (y.2 i))
  exact continuous_qqv R1 R2

theorem continuous_lin (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    Continuous (lin R σ J g) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap ((lin R σ J g).restrictScalars R)
  | exact Continuous.matrix_mulVec continuous_const continuous_id
  | (delta lin; fun_prop)

end Top

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
  [TopologicalSpace R1] [IsTopologicalRing R1] [LocallyCompactSpace R1] [T2Space R1]
  [SecondCountableTopology R1]
  [TopologicalSpace R2] [IsTopologicalRing R2] [LocallyCompactSpace R2] [T2Space R2]
  [SecondCountableTopology R2]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem pres_snd
    (hV : ∀ (g : HA (R1 × R2) σ J) (ν : Measure (Fin M → (R1 × R2) ⊗[F] E)),
      ν.IsAddHaarMeasure → ν.map (lin (R1 × R2) σ J g) = ν)
    (g : HA R2 σ J) (μ : Measure (Fin M → R2 ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) :
    μ.map (lin R2 σ J g) = μ := by
  let ν1 : Measure (Fin M → R1 ⊗[F] E) := Measure.addHaar
  let e := psiE (F := F) (E := E) (M := M) R1 R2
  have hc : Continuous e := continuous_psiE R1 R2
  have hcs : Continuous e.symm := continuous_psiE_symm R1 R2
  let P0 : Measure ((Fin M → R1 ⊗[F] E) × (Fin M → R2 ⊗[F] E)) := ν1.prod μ
  have : P0.IsAddHaarMeasure := inferInstance
  let P : Measure (Fin M → (R1 × R2) ⊗[F] E) := P0.map e.symm
  have : P.IsAddHaarMeasure := e.symm.isAddHaarMeasure_map P0 hcs hc
  have hP := hV (lift R1 R2 σ J g) P inferInstance
  have hl1 := continuous_lin (R1 × R2) σ J (lift R1 R2 σ J g)
  have hl2 := continuous_lin R2 σ J g
  have hPe : P.map e = P0 := by
    rw [Measure.map_map hc.measurable hcs.measurable]
    have : (e ∘ e.symm) = id := funext e.apply_symm_apply
    rw [this, Measure.map_id]
  have key : P0.map (Prod.map id (lin R2 σ J g)) = P0 := by
    have h1 : (Prod.map id (lin R2 σ J g)) ∘ e = e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g)) := by
      funext x
      exact (psi_lin R1 R2 σ J g x).symm
    calc P0.map (Prod.map id (lin R2 σ J g))
        = (P.map e).map (Prod.map id (lin R2 σ J g)) := by rw [hPe]
      _ = P.map ((Prod.map id (lin R2 σ J g)) ∘ e) :=
          Measure.map_map (measurable_id.prodMap hl2.measurable) hc.measurable
      _ = P.map (e ∘ (lin (R1 × R2) σ J (lift R1 R2 σ J g))) := by rw [h1]
      _ = (P.map (lin (R1 × R2) σ J (lift R1 R2 σ J g))).map e :=
          (Measure.map_map hc.measurable hl1.measurable).symm
      _ = P0 := by rw [hP, hPe]
  rw [← Measure.map_prod_map ν1 μ measurable_id hl2.measurable, Measure.map_id] at key
  exact (cancel_prod ν1 _ _ key).symm ▸ rfl

end Meas

end PI.LevelKSplit.W.MVA
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.MVA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

theorem modVAll_of_vmod (h : PI.VolSemiDirect.W.Cj.VMod) : PI.LevelKSplit.W.CD.ModVAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  intro _ _ g μ hμ
  exact pres_snd (InfiniteAdeleRing F) (Af F) σ J
    (fun g' ν hν => h F E σ hσ M J hJ g' ν hν) g μ hμ

theorem modulus_all_extensions : PI.LevelKSplit.W.CD.ModVAll :=
  modVAll_of_vmod PI.VolSemiDirect.W.Cj.unipotent_modulus_holds

end PI.LevelKSplit.W.MVA
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA
open scoped TensorProduct

section Gen

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]

theorem map_eq_of_split (p : V →+ V) (hp : Continuous p) (hpp : ∀ v, p (p v) = p v)
    (W : AddSubgroup V) (hW : ∀ v, v ∈ W ↔ p v = v)
    (g : V →+ V) (hg : Continuous g) (hgU : ∀ u, p u = 0 → g u = u)
    (hV : ∀ μ : Measure V, μ.IsAddHaarMeasure → μ.map g = μ)
    (f : W → W) (hf : ∀ w, (f w : V) = g w) (μ : Measure W) (hμ : μ.IsAddHaarMeasure) :
    μ.map f = μ := by
  classical
  haveI := hμ
  set U : AddSubgroup V := p.ker with hUdef
  have hWc : IsClosed (W : Set V) := by
    have e : (W : Set V) = {v | p v = v} := Set.ext fun v => hW v
    rw [e]
    exact isClosed_eq hp continuous_id
  have hUc : IsClosed (U : Set V) := by
    have e : (U : Set V) = {v | p v = 0} := Set.ext fun v => by simp [hUdef, AddMonoidHom.mem_ker]
    rw [e]
    exact isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace W := hWc.locallyCompactSpace
  haveI : LocallyCompactSpace U := hUc.locallyCompactSpace
  haveI : BorelSpace W := Subtype.borelSpace (W : Set V)
  haveI : BorelSpace U := Subtype.borelSpace (U : Set V)
  haveI : SecondCountableTopology W := TopologicalSpace.Subtype.secondCountableTopology (W : Set V)
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set V)
  haveI : BorelSpace (W × U) := Prod.borelSpace
  have hpW : ∀ w : W, p w = w := fun w => (hW w).1 w.2
  have hfc : Continuous f := by
    apply continuous_induced_rng.2
    have e : (Subtype.val ∘ f : W → V) = fun w : W => g (w : V) := funext hf
    rw [e]
    exact hg.comp continuous_subtype_val
  let Φ : W × U →+ V := W.subtype.comp (AddMonoidHom.fst W U) + U.subtype.comp (AddMonoidHom.snd W U)
  have hΦ : ∀ x : W × U, Φ x = (x.1 : V) + (x.2 : V) := fun x => rfl
  have hΦc : Continuous Φ := by
    have e : (Φ : W × U → V) = fun x => (x.1 : V) + (x.2 : V) := funext hΦ
    rw [e]
    exact (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
  let Ψ : V → W × U := fun v => (⟨p v, (hW _).2 (hpp v)⟩,
    ⟨v - p v, by simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp]⟩)
  have hΨc : Continuous Ψ :=
    (hp.subtype_mk fun v => (hW _).2 (hpp v)).prodMk ((continuous_id.sub hp).subtype_mk fun v => by
      simp [hUdef, AddMonoidHom.mem_ker, map_sub, hpp])
  have hΦΨ : ∀ v, Φ (Ψ v) = v := fun v => by
    rw [hΦ]
    simp [Ψ]
  have hΨΦ : ∀ x, Ψ (Φ x) = x := by
    rintro ⟨w, u⟩
    have hu : p u = 0 := u.2
    have hpx : p (Φ (w, u)) = w := by rw [hΦ, map_add, hpW, hu, add_zero]
    apply Prod.ext
    · apply Subtype.ext
      show p (Φ (w, u)) = w
      exact hpx
    · apply Subtype.ext
      show Φ (w, u) - p (Φ (w, u)) = u
      rw [hpx, hΦ]
      simp
  have hΦs : Function.Surjective Φ := fun v => ⟨Ψ v, hΦΨ v⟩
  let e : (W × U) ≃ₜ V :=
    { toFun := Φ, invFun := Ψ, left_inv := hΨΦ, right_inv := hΦΨ,
      continuous_toFun := hΦc, continuous_invFun := hΨc }
  let ν : Measure U := Measure.addHaar
  set P : Measure (W × U) := μ.prod ν with hP
  haveI hPH : P.IsAddHaarMeasure := by rw [hP]; infer_instance
  have hHaar : (P.map Φ).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map P Φ hΦc hΦs e.isClosedEmbedding.tendsto_cocompact
  have hmap := hV _ hHaar
  have hgΦ : (g : V → V) ∘ Φ = Φ ∘ Prod.map f id := by
    funext x
    obtain ⟨w, u⟩ := x
    simp only [Function.comp, Prod.map, id, hΦ, map_add, hgU u u.2, hf]
  have hfm : Measurable f := hfc.measurable
  have hPm : Measurable (Prod.map f (id : U → U)) := hfm.prodMap measurable_id
  rw [Measure.map_map hg.measurable hΦc.measurable, hgΦ,
    ← Measure.map_map hΦc.measurable hPm] at hmap
  have hinv : ∀ Q : Measure (W × U), (Q.map Φ).map Ψ = Q := by
    intro Q
    rw [Measure.map_map hΨc.measurable hΦc.measurable]
    have e2 : Ψ ∘ Φ = id := funext hΨΦ
    rw [e2, Measure.map_id]
  have hP' : P.map (Prod.map f id) = P := by
    have h2 := congrArg (fun Q => Q.map Ψ) hmap
    simpa only [hinv] using h2
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds (0 : U)
  have hK0 : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hKn).ne'
  have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
  ext A hA
  rw [Measure.map_apply hfm hA]
  have h1 : (P.map (Prod.map f id)) (A ×ˢ K) = P (A ×ˢ K) := by rw [hP']
  rw [Measure.map_apply hPm (hA.prod hKc.measurableSet)] at h1
  have hpre : Prod.map f id ⁻¹' (A ×ˢ K) = (f ⁻¹' A) ×ˢ K := by
    ext x
    simp
  rw [hpre, hP, Measure.prod_prod, Measure.prod_prod] at h1
  have h2 := congrArg (fun t => t / ν K) h1
  simp only [ENNReal.mul_div_cancel_right hK0 hKt] at h2
  exact h2

end Gen

namespace DatL

open PI.LevelKSplit.W.SemiG PI.LevelKSplit.W.SemiG.Dat

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
  {D : PI.LevelKSplit.W.SemiG.Dat A n r}

theorem h_e_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (D.pXv v) = D.h (D.e b) v := by
  rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ef, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem h_f_pX (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pX v) = D.h (D.f b) v := by
  have hfe : ∀ a, D.h (D.f b) (D.e a) = if b = a then 1 else 0 := by
    intro a
    rw [Dat.h_symm H (D.e a) (D.f b), H.ef]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (Ne.symm hab), map_zero]
  rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, hfe, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem h_f_pXv (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (D.pXv v) = 0 := by
  rw [← Dat.hL_apply, Dat.pXv, LinearMap.sum_apply, map_sum]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ff, mul_zero,
    Finset.sum_const_zero]

variable (D) in

def pL : (n → A) →ₗ[A] (n → A) := LinearMap.id - D.pX - D.pXv

theorem pL_apply (v : n → A) : pL D v = v - D.pX v - D.pXv v := rfl

theorem h_e_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.e b) (pL D v) = 0 := by
  have h0 : D.h (D.e b) (D.pX v) = 0 := by
    rw [← Dat.hL_apply, Dat.pX, LinearMap.sum_apply, map_sum]
    simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul, Dat.hL_apply, H.ee, mul_zero,
      Finset.sum_const_zero]
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h0, h_e_pXv H]
  ring

theorem h_f_pL (H : D.Hyp) (b : Fin r) (v : n → A) : D.h (D.f b) (pL D v) = 0 := by
  rw [pL_apply, ← Dat.hL_apply, map_sub, map_sub]
  simp only [Dat.hL_apply]
  rw [h_f_pX H, h_f_pXv H]
  ring

theorem pL_of {v : n → A} (he : ∀ a, D.h (D.e a) v = 0) (hf : ∀ a, D.h (D.f a) v = 0) :
    pL D v = v := by
  have h1 : D.pX v = 0 := by
    simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, hf, zero_smul,
      Finset.sum_const_zero]
  have h2 : D.pXv v = 0 := by
    simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, Dat.hL_apply, he, zero_smul,
      Finset.sum_const_zero]
  rw [pL_apply, h1, h2, sub_zero, sub_zero]

theorem pL_pL (H : D.Hyp) (v : n → A) : pL D (pL D v) = pL D v :=
  pL_of (fun a => h_e_pL H a v) (fun a => h_f_pL H a v)

theorem fix_of_pL_zero {S : (n → A) →ₗ[A] (n → A)} (hSe : ∀ a, S (D.e a) = D.e a)
    (hSf : ∀ a, S (D.f a) = D.f a) {u : n → A} (hu : pL D u = 0) : S u = u := by
  have hu' : u = D.pX u + D.pXv u := by
    rw [pL_apply, sub_sub, sub_eq_zero] at hu
    exact hu
  rw [hu', map_add]
  congr 1
  · simp only [Dat.pX, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSe]
  · simp only [Dat.pXv, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul, hSf]

end DatL

section Wp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem mem_Wp_iff (H : (datR R σ J P T).Hyp) (v : Fin M → R ⊗[F] E) :
    v ∈ Wp R σ J P ↔ DatL.pL (datR R σ J P T) v = v := by
  constructor
  · rintro ⟨he, hf⟩
    exact DatL.pL_of (fun a => he a) (fun a => hf a)
  · intro h
    change (∀ a, _) ∧ (∀ a, _)
    refine ⟨fun a => ?_, fun a => ?_⟩
    · have h1 := DatL.h_e_pL H a v
      rw [h] at h1
      exact h1
    · have h1 := DatL.h_f_pL H a v
      rw [h] at h1
      exact h1

theorem lin_mem_Wp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin M → R ⊗[F] E}
    (hw : w ∈ Wp R σ J P) : lin R σ J h w ∈ Wp R σ J P := by
  obtain ⟨he, hf⟩ := hw
  have hfix : ∀ i, lin R σ J h (ratV (F := F) R (tupH P i)) = ratV (F := F) R (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  change (∀ a, _) ∧ (∀ a, _)
  refine ⟨fun a => ?_, fun a => ?_⟩
  · have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    rw [← h1, hR_lin]
    exact he a
  · have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    rw [← h1, hR_lin]
    exact hf a

def linWp {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (w : Wp R σ J P) : Wp R σ J P :=
  ⟨lin R σ J h w, lin_mem_Wp hh w.2⟩

end Wp

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

theorem sc_tens : SecondCountableTopology (Af F ⊗[F] E) := by
  haveI := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  infer_instance

theorem wp_map (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
    (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) {h : HA (Af F) σ J} (hh : h ∈ Hsub (Af F) σ J P)
    (μ : Measure (Wp (Af F) σ J P)) (hμ : μ.IsAddHaarMeasure) : μ.map (linWp hh) = μ := by
  haveI := sc_tens (F := F) (E := E)
  have H := datR_hyp (R := Af F) hσσ hJ hP
  have hfix : ∀ i, lin (Af F) σ J h (ratV (F := F) (Af F) (tupH P i)) = ratV (F := F) (Af F) (tupH P i) :=
    fun i => congrFun (MulAction.mem_stabilizer_iff.mp hh) i
  have hSe : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).e a) = (datR (Af F) σ J P T).e a := by
    intro a
    have h1 := hfix (Fin.castAdd r (Fin.castSucc a))
    simp only [tupH, F0, Fin.append_left, Fin.snoc_castSucc] at h1
    exact h1
  have hSf : ∀ a, lin (Af F) σ J h ((datR (Af F) σ J P T).f a) = (datR (Af F) σ J P T).f a := by
    intro a
    have h1 := hfix (Fin.natAdd (r + 1) a)
    simp only [tupH, Fin.append_right] at h1
    exact h1
  refine map_eq_of_split (DatL.pL (datR (Af F) σ J P T)).toAddMonoidHom ?_
    (fun v => DatL.pL_pL H v) (Wp (Af F) σ J P) (fun v => mem_Wp_iff H v)
    (lin (Af F) σ J h).toAddMonoidHom ?_ (fun u hu => DatL.fix_of_pL_zero hSe hSf hu)
    (fun ν hν => hV hJ hσσ h ν hν) (linWp hh) (fun w => rfl) μ hμ
  · exact LinearMap.continuous_on_pi _
  · exact LinearMap.continuous_on_pi _

end Af

end PI.LevelKSplit.W.NCA
end
end

section
noncomputable section

namespace PI.LevelKSplit.W.NCA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open PI.LevelKSplit PI.LevelKSplit.W.NC PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct

theorem conjInv_of_one {X : Type} [Group X] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (N H : Subgroup X) (hN : LCSC N)
    (hex : ∀ h ∈ H, ∃ μ0 : Measure N, μ0.IsHaarMeasure ∧ ∀ f : X → ENNReal, Measurable f →
      ∫⁻ n, f (h * (n : X) * h⁻¹) ∂μ0 = ∫⁻ n, f (n : X) ∂μ0) : ConjInv N H := by
  obtain ⟨hlc, hsc, ht2, htg⟩ := hN
  intro μN hμN h hh f hf
  obtain ⟨μ0, hμ0, hinv⟩ := hex h hh
  rw [Measure.isMulLeftInvariant_eq_smul μN μ0, lintegral_smul_measure, lintegral_smul_measure,
    hinv f hf]

section Af

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [FiniteDimensional F E] {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem conjNH_of (hC : NCoord F E σ M J) (hV : PI.LevelKSplit.W.CD.ModV F E σ M J) :
    PI.LevelKSplit.W.ExS.ConjNH F E σ M J := by
  intro hJ hσσ r P T hP
  have hsc : SecondCountableTopology (Af F) := PI.LevelKSplit.W.SC.finite_adeles_secondCountable F
  have hL : LCSC (HA (Af F) σ J) := PI.LevelKSplit.W.ExS.lcsc_HAf hsc
  have : BorelSpace (HA (Af F) σ J) := ⟨rfl⟩
  have : SecondCountableTopology (HA (Af F) σ J) := hL.2.1
  obtain ⟨-, cN, -⟩ := PI.LevelKSplit.W.ExC.closed_SNH hJ hσσ P T hP
  obtain ⟨lN, -⟩ := subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ _ hL cN inferInstance inferInstance
  refine conjInv_of_one _ _ lN ?_
  intro h hh
  obtain ⟨A, Z, Ψ, cA, cZ, hleft, hconj⟩ := hC hJ hσσ r P T hP
  obtain ⟨⟨lcA, scA, t2A, tgA⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ A hL cA inferInstance inferInstance
  obtain ⟨⟨lcZ, scZ, t2Z, tgZ⟩, -⟩ :=
    subgroup_locally_compact_holds (HA (Af F) σ J) ⊥ Z hL cZ inferInstance inferInstance
  obtain ⟨lcN, scN, t2N, tgN⟩ := lN
  have : BorelSpace A := Subtype.borelSpace _
  have : BorelSpace Z := Subtype.borelSpace _
  have : BorelSpace (Nsub (Af F) σ J P) := Subtype.borelSpace _
  have : SecondCountableTopology (Af F ⊗[F] E) := sc_tens
  have : BorelSpace (Af F ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (Fin M → Af F ⊗[F] E) := Pi.borelSpace
  have H := SemiA.datR_hyp (R := Af F) hσσ hJ hP
  have cW : IsClosed ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) :
      Set (Fin M → Af F ⊗[F] E)) := by
    have e1 : ((Wp (Af F) σ J P : AddSubgroup (Fin M → Af F ⊗[F] E)) : Set (Fin M → Af F ⊗[F] E)) =
        {v | DatL.pL (SemiA.datR (Af F) σ J P T) v = v} := by
      ext v
      exact mem_Wp_iff H v
    rw [e1]
    exact isClosed_eq (LinearMap.continuous_on_pi _) continuous_id
  have : LocallyCompactSpace (Wp (Af F) σ J P) := cW.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (Wp (Af F) σ J P) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  have : BorelSpace (Wp (Af F) σ J P) := Subtype.borelSpace _
  have : BorelSpace (Fin r → Wp (Af F) σ J P) := Pi.borelSpace
  have : BorelSpace ((Fin r → Wp (Af F) σ J P) × Z) := Prod.borelSpace
  have : BorelSpace (A × ((Fin r → Wp (Af F) σ J P) × Z)) := Prod.borelSpace
  let μA : Measure A := Measure.haar
  let μZ : Measure Z := Measure.haar
  let μW : Measure (Wp (Af F) σ J P) := Measure.addHaar
  let μQ : Measure (Fin r → Wp (Af F) σ J P) := Measure.pi fun _ => μW
  let ρ : Measure (A × ((Fin r → Wp (Af F) σ J P) × Z)) := μA.prod (μQ.prod μZ)
  have hΨm : Measurable Ψ := Ψ.continuous.measurable
  refine ⟨ρ.map Ψ, ?_, ?_⟩
  · have hli : (ρ.map Ψ).IsMulLeftInvariant := by
      refine ⟨fun n0 => ?_⟩
      obtain ⟨a0, t, c, ht, hc, hform⟩ := hleft n0
      have hcomm : (fun n => n0 * n) ∘ Ψ = Ψ ∘ (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) := by
        funext ⟨u, y, z⟩
        exact hform u y z
      have hinner : ∀ u : A, MeasurePreserving
          (fun q : (Fin r → Wp (Af F) σ J P) × Z => (q.1 + t u, c (u, q.1) * q.2))
          (μQ.prod μZ) (μQ.prod μZ) := by
        intro u
        refine (measurePreserving_add_right μQ (t u)).skew_product (g := fun y z => c (u, y) * z)
          ?_ (Filter.Eventually.of_forall fun y => map_mul_left_eq_self μZ (c (u, y)))
        exact (show Continuous fun q : (Fin r → Wp (Af F) σ J P) × Z => c (u, q.1) * q.2 from
          (hc.comp (continuous_const.prodMk continuous_fst)).mul continuous_snd).measurable
      have hgm : Continuous fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2) :=
        (continuous_snd.fst.add (ht.comp continuous_fst)).prodMk
          ((hc.comp (continuous_fst.prodMk continuous_snd.fst)).mul continuous_snd.snd)
      have hT : MeasurePreserving (fun p : A × ((Fin r → Wp (Af F) σ J P) × Z) =>
          (a0 * p.1, (p.2.1 + t p.1, c (p.1, p.2.1) * p.2.2))) ρ ρ :=
        (measurePreserving_mul_left μA a0).skew_product
          (g := fun (u : A) (q : (Fin r → Wp (Af F) σ J P) × Z) => (q.1 + t u, c (u, q.1) * q.2)) hgm.measurable
          (Filter.Eventually.of_forall fun u => (hinner u).map_eq)
      rw [Measure.map_map (measurable_const_mul n0) hΨm, hcomm, ← Measure.map_map hΨm hT.measurable,
        hT.map_eq]
    have hfc : IsFiniteMeasureOnCompacts (ρ.map Ψ) := Measure.IsFiniteMeasureOnCompacts.map ρ Ψ
    have hop : (ρ.map Ψ).IsOpenPosMeasure := Ψ.continuous.isOpenPosMeasure_map Ψ.surjective
    have := hfc
    have := hli
    have := hop
    exact Measure.IsHaarMeasure.mk
  · intro f hf
    have hF : Measurable fun n : Nsub (Af F) σ J P => f (h * (n : HA (Af F) σ J) * h⁻¹) :=
      hf.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hF0 : Measurable fun n : Nsub (Af F) σ J P => f (n : HA (Af F) σ J) :=
      hf.comp continuous_subtype_val.measurable
    have hlinm : Measurable (linWp hh) :=
      (((LinearMap.continuous_on_pi (lin (Af F) σ J h)).comp continuous_subtype_val).subtype_mk
        _).measurable
    let Lq : (Fin r → Wp (Af F) σ J P) → (Fin r → Wp (Af F) σ J P) := fun y a => linWp hh (y a)
    have hLq : MeasurePreserving Lq μQ μQ :=
      measurePreserving_pi (fun _ => μW) (fun _ => μW)
        (fun _ => ⟨hlinm, wp_map hσσ hJ hP hV hh μW inferInstance⟩)
    have hT : MeasurePreserving (Prod.map id (Prod.map Lq id)) ρ ρ :=
      (MeasurePreserving.id μA).prod (hLq.prod (MeasurePreserving.id μZ))
    rw [lintegral_map hF hΨm, lintegral_map hF0 hΨm]
    calc ∫⁻ p, f (h * (Ψ p : HA (Af F) σ J) * h⁻¹) ∂ρ
        = ∫⁻ p, f (Ψ (Prod.map id (Prod.map Lq id) p) : HA (Af F) σ J) ∂ρ := by
          congr 1
          funext ⟨u, y, z⟩
          obtain ⟨y', hy', he⟩ := hconj h hh u y z
          have e2 : y' = Lq y := funext fun a => Subtype.ext (hy' a)
          show f (h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹) = f (Ψ (u, Lq y, z) : HA (Af F) σ J)
          rw [he, e2]
      _ = ∫⁻ p, f (Ψ p : HA (Af F) σ J) ∂ρ :=
          hT.lintegral_comp (show Measurable fun p => f (Ψ p : HA (Af F) σ J) from
            hf.comp (continuous_subtype_val.comp Ψ.continuous).measurable)

theorem normal_conjugation_hypothesis : NCAsm F E σ M J := fun hC hV => conjNH_of hC hV

end Af

theorem normal_conjugation_all : NCAsmAll := by
  intro F E _ _ _ _ _ σ hσ M J hJ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  exact normal_conjugation_hypothesis

end PI.LevelKSplit.W.NCA
end
end

section
namespace PI.LevelKSplit.W.Top6

theorem levelSplitting_of_heisenberg_levi (hH : PI.LevelKSplit.W.NC.HeisPAll) (hL : PI.LevelKSplit.W.NC.LevPAll) :
    PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.NC.levelSAll_of_semiNHS_heis_lev PI.LevelKSplit.W.SemiT.semidirect_topological_all hH hL
    PI.LevelKSplit.W.MVA.modulus_all_extensions PI.LevelKSplit.W.NCA.normal_conjugation_all

end PI.LevelKSplit.W.Top6
end
