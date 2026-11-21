import Formalism.LocalToGlobal.Columns.CharactersLevelZeroAgree
import Formalism.LocalToGlobal.Columns.TiedGlRec

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ColLevelXRest {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V} (L : ColLevel R F E sp gp C A clsLat)
    (piU : 𝓞 E)
    (e : A.vT ≃ {v : HeightOneSpectrum (𝓞 F) // ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal})
    (fz : ∀ (v : A.vT) (c : C.cls 0), Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c) → A.Fv v) where

  frG_lat : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal)
    (t : Fin R.k → v.adicCompletion F),
    (∃ x ∈ Formalism.L2.Herm.locL v L.Lb, ∀ a, (L.splitG i v h (x a)).1 = t a) ↔
      ∀ a, (((L.frG i v h)⁻¹ : GL (Fin R.k) (v.adicCompletion F)) :
        Matrix (Fin R.k) (Fin R.k) (v.adicCompletion F)).mulVec t a ∈ v.adicCompletionIntegers F

  fM_pi : ∀ (v : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ v.asIdeal) (a : intV E v),
    (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (piU : E) →
    ∀ m : L.fM v h, a • m = 0

  fMe : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal), L.fM w h ≃+ A.Fv (e.symm ⟨w, h⟩)

  fv0 : ∀ (w : HeightOneSpectrum (𝓞 F)) (h : ((A.T : ℕ) : 𝓞 F) ∈ w.asIdeal) (c : C.cls 0)
    (z : Formalism.HermitianLatticesTheory.dual (sp.X 0).hT (clsLat 0 c))
    (t : latS (F := F) (w.adicCompletion F) (intV E w)
      (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) sp.gram0 L.Lb))),
    ((bc (prV (E := E) w) (L.y c : GL (Fin R.k) (E ⊗[F] Formalism.L2.Herm.Af F)) : GL (Fin R.k) (E ⊗[F] w.adicCompletion F)) :
      Matrix (Fin R.k) (Fin R.k) (E ⊗[F] w.adicCompletion F)).mulVec t.1 =
      (fun a => inclE (F := F) (w.adicCompletion F) (sp.crd0 z.1 a)) →
    fz (e.symm ⟨w, h⟩) c z = fMe w h (L.fT w h t)

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S) (O : AtTOwed a hS hH)

abbrev LevelZeroConditions : Type :=
  ∀ u : d.what₂.Word, ColLevelXRest ((hermCols a hS hP hK S hI).lev0 u) (d.piT u) ((hermCols a hS hP hK S hI).vT u)
    (fun v c z => ((d.colRec a).fm u).fv 0 v c ((hermAtT a hS hH O u).pr 0 v c z))

def levelZeroCompatibility (L0 : LevelZeroConditions a hS hH hP hK S hI O) :
    CH.Lev0Tied (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) := fun u =>
  { piG := d.piG
    piG_K := hH.piG_K
    piG_norm := fun i => by
      have h := congrArg (algebraMap (𝓞 d.host.E) d.host.E) (d.hPr.piG_norm i)
      rw [map_mul, map_natCast] at h
      exact h
    splitG_pi := S.sp_pi
    splitG_alg := S.sp_alg
    frG_lat := (L0 u).frG_lat
    fM_pi := (L0 u).fM_pi
    fMe := (L0 u).fMe
    fv0 := (L0 u).fv0 }

theorem piGConst (L0 : LevelZeroConditions a hS hH hP hK S hI O) :
    CH.PiGConst (d.colRec a) (hermCols a hS hP hK S hI) (hermAtT a hS hH O) (levelZeroCompatibility a hS hH hP hK S hI O L0) :=
  fun _ _ => rfl

theorem th_joint_sp (hCh : d.Ch.Ok) (u : d.what₂.Word) : (recGLoc a S hCh).sp = ((hermCols a hS hP hK S hI).lev0 u).splitG := rfl

theorem th_joint_piG (hCh : d.Ch.Ok) (L0 : LevelZeroConditions a hS hH hP hK S hI O) (u : d.what₂.Word) :
    (recGLoc a S hCh).piG = (levelZeroCompatibility a hS hH hP hK S hI O L0 u).piG := rfl

theorem jointLevel_frame_zero (hCh : d.Ch.Ok) (hl : d.lev = colLevS d.Ch) (u : d.what₂.Word) (i : Fin 2) (v : HeightOneSpectrum (𝓞 d.host.F))
    (h : (d.host.g i : 𝓞 d.host.F) ∈ v.asIdeal) :
    (recGLev a S hCh hl hS hH hP u 0 (Nat.zero_le _)).fr i v h =
      Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level d.R) _ (((hermCols a hS hP hK S hI).lev0 u).frG i v h) := by
  rw [recGLev_fr]
  have h0 : recUnit S u 0 i v h = 1 := by
    unfold recUnit
    rw [if_neg]
    have := d.R.two_le_m
    omega
  show glvD (d.R.N 0) v (recUnit S u 0 i v h) = _
  rw [h0, glvD_one]
  exact (map_one (Formalism.L2.Forms.reGL (Formalism.L2.Forms.rank_eq_first_level d.R) (v.adicCompletion d.host.F))).symm

end Formalism.L2.Col
end
end

section
open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E} (v : HeightOneSpectrum (𝓞 F))

theorem th_fLoc_pi (h : BasePi ST π) (a : Formalism.BasicNotions.intV E v)
    (ha : (a : E ⊗[F] v.adicCompletion F) = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π)) (m : fMod hc n ST v) :
    a • m = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
  show a • fLoc hc n ST v x = 0
  rw [← map_smul, rll_fLoc_eq_zero, rll_baseKer_eq n h, rll_mem_loc_dLat n v _ (div_ne_zero h.star_ne_zero h.coe_ne_zero)]
  have hx : x.1 ∈ Formalism.L2.Herm.locL v (rll_dLat n (star (algebraMap (𝓞 E) E π))) := by
    rw [← rll_dualV_eq hc n v h]; exact x.2
  rw [rll_mem_loc_dLat n v _ h.star_ne_zero] at hx
  refine ⟨fun i hi => mul_mem a.2 (hx.1 i hi), ?_⟩
  show inclE (F := F) (v.adicCompletion F) (star (algebraMap (𝓞 E) E π) / algebraMap (𝓞 E) E π) *
    ((a : E ⊗[F] v.adicCompletion F) * x.1 (lastIdx n)) ∈ Formalism.BasicNotions.intV E v
  rw [ha, rll_cp_mul v h]
  exact hx.2

end Loc

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)
  (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c) (hK : LocalLevelIsKOneAtT hc u Λ)

theorem levPack_fM_pi (H : HCrd Pr n fun c => (s c).1.L) (v : HeightOneSpectrum (𝓞 X.F)) (hv : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal)
    (a : intV X.E v) (ha : (a : X.E ⊗[X.F] v.adicCompletion X.F) = inclE (F := X.F) (v.adicCompletion X.F) (Pr.piT u : X.E))
    (m : (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.fM v hv) : a • m = 0 := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact th_fLoc_pi hc _ v (basePi_of_ok hX hPr u) a ha m

theorem levPack_frLat (S : GSplit (Pr := Pr) hc) (H : HCrd Pr n fun c => (s c).1.L) (i : Fin 2) (v : HeightOneSpectrum (𝓞 X.F))
    (h : (Pr.g i : 𝓞 X.F) ∈ v.asIdeal) (t : Fin H.n' → v.adicCompletion X.F) :
    (∃ x ∈ Formalism.L2.Herm.locL v (levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).lev.Lb, ∀ b, (S.sp i v h (x b)).1 = t b) ↔
      ∀ b, (((1 : GL (Fin H.n') (v.adicCompletion X.F))⁻¹ : GL (Fin H.n') (v.adicCompletion X.F)) :
        Matrix (Fin H.n') (Fin H.n') (v.adicCompletion X.F)).mulVec t b ∈ v.adicCompletionIntegers X.F := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  refine gco_fr_lat _ (Pr.vT u) v (S.sp i v h) (S.sp_alg i v h) ?_ t
  intro hT
  have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
    (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
  exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl h; exact Or.inr h))

end Gen

end Formalism.L2.Col
end
end
