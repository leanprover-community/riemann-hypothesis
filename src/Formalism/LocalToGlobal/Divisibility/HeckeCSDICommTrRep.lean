import Mathlib
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.Divisibility.LiftLatInst
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsRat
import Formalism.LocalToGlobal.Columns.AnisotropicOfPositiveDefinite
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.Columns.HeckeInertTr

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Conj

variable {K : Type} [Field K] {M M₂ : Type} [AddCommGroup M] [Module K M] [AddCommGroup M₂] [Module K M₂]
  (e : M ≃ₗ[K] M₂)

theorem conjE_one : e.conj (1 : Module.End K M) = 1 := by
  ext x
  simp [LinearEquiv.conj_apply]

theorem conjE_commute {f g : Module.End K M} (hfg : Commute f g) : Commute (e.conj f) (e.conj g) := by
  rw [commute_iff_eq]
  ext x
  simpa [LinearEquiv.conj_apply] using congrArg e (LinearMap.congr_fun hfg.eq (e.symm x))

theorem conjE_sub_pow (f : Module.End K M) (μ : K) (k : ℕ) :
    (e.conj f - μ • (1 : Module.End K M₂)) ^ k = e.conj ((f - μ • (1 : Module.End K M)) ^ k) := by
  have hsub : e.conj f - μ • (1 : Module.End K M₂) = e.conj (f - μ • (1 : Module.End K M)) := by
    ext x
    simp [LinearEquiv.conj_apply]
  rw [hsub]
  induction k with
  | zero => rw [pow_zero, pow_zero, conjE_one]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    ext x
    simp [LinearEquiv.conj_apply]

theorem conjE_maxGen (f : Module.End K M) (μ : K) :
    (e.conj f).maxGenEigenspace μ = (f.maxGenEigenspace μ).map (e : M →ₗ[K] M₂) := by
  ext y
  simp only [Module.End.mem_maxGenEigenspace, Submodule.mem_map, conjE_sub_pow]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨e.symm y, ⟨k, ?_⟩, by simp⟩
    simpa [LinearEquiv.conj_apply] using hk
  · rintro ⟨x, ⟨k, hk⟩, rfl⟩
    exact ⟨k, by simp [LinearEquiv.conj_apply, hk]⟩

theorem conjE_iSup_maxGen (f : Module.End K M) (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) :
    ⨆ μ, (e.conj f).maxGenEigenspace μ = ⊤ := by
  simp only [conjE_maxGen]
  rw [← Submodule.map_iSup, hf, Submodule.map_top]
  exact LinearEquiv.range e

end Conj

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
  {ST SG' : Finset (HeightOneSpectrum (𝓞 E))}
  (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG') (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (S0 : Set (HeightOneSpectrum (𝓞 E)))

theorem heckeCSD_zero (P : offSub ST SG SG' S0) : heckeCSD S h c SG S0 (P, 0) = 1 := by
  unfold heckeCSD
  dsimp only
  first
    | (simp only [Col.heckeFam_zero]; ext x; simp [LinearEquiv.conj_apply])
    | (erw [Col.heckeFam_zero]; ext x; simp [LinearEquiv.conj_apply])
    | (ext x; simp [LinearEquiv.conj_apply, Col.heckeFam_zero])

theorem heckeCSD_comm (hc : Col.HeckeComm c S0) : Col.PairComm (heckeCSD S h c SG S0) := by
  intro x y
  exact conjE_commute _ (hc _ _)

theorem heckeCSD_split (hs : Col.HeckeFieldsIn c S0) : Col.SplitOver (heckeCSD S h c SG S0) := by
  intro x
  exact conjE_iSup_maxGen (S.res h) _ (hs _)



end Gen

section Tr

variable {X : Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : Col.CoefPk X n (Col.DecoSet X.E n ST SG)) (Λ : Col.LevFam X.E X.K n SG)

theorem heckeFam_formPts_apply (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Col.LevOff ST SG S0 × ℕ)
    (φ : (Col.formGSD C Λ).EqFun) :
    ((Col.heckeFam (formPts C Λ) S0 y φ : (Col.formGSD C Λ).EqFun) : Col.DecoSet X.E n ST SG → C.V) =
      Col.nbFun X.K C.V y.1.1.asIdeal y.2 (φ : Col.DecoSet X.E n ST SG → C.V) := by
  funext d
  simp only [Col.heckeFam, Col.heckeD]
  erw [Col.LocOp.ofNbr_op_apply]
  simp only [Col.DecoPts.nb, Finset.sum_map, LinearMap.id_apply]
  rfl

theorem heckeFam_comm_trRep {A : Type} [Group A] (ι : A →* Col.GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (y : Col.LevOff ST SG S0 × ℕ) (a : A) :
    Commute (Col.trRep C Λ ι hι a) (Col.heckeFam (formPts C Λ) S0 y) := by
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  have key : ∀ ψ : (Col.formGSD C Λ).EqFun,
      ((Col.trRep C Λ ι hι a ψ : (Col.formGSD C Λ).EqFun) : Col.DecoSet X.E n ST SG → C.V) =
        Col.trF X n ST SG C.V (ι a) (ψ : Col.DecoSet X.E n ST SG → C.V) := fun ψ => rfl
  rw [Module.End.mul_apply, Module.End.mul_apply, key, heckeFam_formPts_apply, heckeFam_formPts_apply, key,
    Col.trF_nbFun]

theorem heckeCSD_comm_trRep (h : (Col.formGSD C Λ).Ok) {A : Type} [Group A] (ι : A →* Col.GLG X.E n SG)
    (hι : ∀ a w, (Λ w).NormBy (ι a w)) (SG0 : Finset (HeightOneSpectrum (𝓞 X.E)))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (x : offSub ST SG0 SG S0 × ℕ) (a : A) :
    Commute (heckeCSD (Col.formGSD C Λ) h (formPts C Λ) SG0 S0 x)
      ((Col.formGSD C Λ).repCSD h (Col.trRep C Λ ι hι) a) := by
  have hc := heckeFam_comm_trRep C Λ ι hι S0 (⟨x.1.1.1, x.1.2⟩, x.2) a
  have hr : (Col.formGSD C Λ).repCSD h (Col.trRep C Λ ι hι) a =
      ((Col.formGSD C Λ).res h).conj (Col.trRep C Λ ι hι a) := by
    apply LinearMap.ext
    intro f
    simp [Col.GSD.repCSD, LinearEquiv.conj_apply]
  rw [hr]
  exact conjE_commute ((Col.formGSD C Λ).res h) hc.symm

end Tr

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

abbrev rowPts (mu : Tup X.F X.E X.K S) :
    Col.DecoPts (Col.mtildeKGSD W Ch sel mu) X.E (R.N R.m - 1) ∅ (Col.rowSG Pr sel mu) := formPts _ _

abbrev liftPts (mu : Tup X.F X.E X.K S) (j : ℕ) :
    Col.DecoPts (Col.mtKGSD W Ch sel mu j) X.E R.nV ∅ (Col.rowSG Pr sel mu) := formPts _ _

structure ColHyp (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E))) : Prop where

  conj : IsConjAt v0

  irr : ∀ χ ∈ Xg, IsAbsIrrChar χ

  commR : ∀ τ : TupF TU, Col.HeckeComm (rowPts W Ch sel τ.1) S0

  splitR : ∀ τ : TupF TU, Col.HeckeFieldsIn (rowPts W Ch sel τ.1) S0

  commL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeComm (liftPts W Ch sel τ.1 (j.1 + 1)) S0

  splitL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeFieldsIn (liftPts W Ch sel τ.1 (j.1 + 1)) S0


variable (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)

theorem colFam_rows_ok (commR : ∀ τ : TupF TU, Col.HeckeComm (rowPts W Ch sel τ.1) S0)
    (splitR : ∀ τ : TupF TU, Col.HeckeFieldsIn (rowPts W Ch sel τ.1) S0) (τ : TupF TU) :
    ((colFam W Ch sel hX v0 TU Xg S0 xiVal).R τ).Ok 1 where
  good := Col.MtildeKCSD_good W Ch sel τ.1 hX _
  hrat := Col.CSDRat.H_mem _ (Col.MtildeKCSD_rat W Ch sel τ.1 hX _)
    (Col.csd_hasRatBasis _ (Col.MtildeKCSD_rat W Ch sel τ.1 hX _))
  hpos := fun v => (Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v
  act := Col.unipotentActionForms_good W Ch sel τ.1 hX _
  actRat := Col.unipotentActionForms_rational W Ch sel τ.1 hX _
  comm := heckeCSD_comm _ _ _ _ _ (commR τ)
  split := heckeCSD_split _ _ _ _ _ (splitR τ)
  opG := fun i g => heckeCSD_comm_trRep _ _ _ _ _ _ _ i g
  blocks := Col.blockOk_firstValB (fun j (P : ↥(offSub ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0)) =>
      Ch.muVal j P.1.1 * xiVal τ.1 P.1.1) (q := fun P => Col.SplitOff.q P.1) R.r R.t_odd.pos
    (by have := R.two_le_m; omega) (fun P => Col.SplitOff.q_ne_zero P.1)
  q_pos := fun P => Nat.pos_of_ne_zero (Col.SplitOff.q_ne_zero P.1)
  pl_inj := Subtype.val_injective

theorem colFam_lifts_ok (commL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeComm (liftPts W Ch sel τ.1 (j.1 + 1)) S0)
    (splitL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeFieldsIn (liftPts W Ch sel τ.1 (j.1 + 1)) S0)
    (j : Fin R.m) (τ : TupF TU) :
    ((colFam W Ch sel hX v0 TU Xg S0 xiVal).L j τ).Ok 1 where
  good := Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _
  hrat := Col.CSDRat.H_mem _ (Col.MtKCSD_rat W Ch sel τ.1 hX (j.1 + 1) _)
    (Col.csd_hasRatBasis _ (Col.MtKCSD_rat W Ch sel τ.1 hX (j.1 + 1) _))
  hpos := fun v => (Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v
  act := Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _
  actRat := Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _
  comm := heckeCSD_comm _ _ _ _ _ (commL j τ)
  split := heckeCSD_split _ _ _ _ _ (splitL j τ)
  opG := fun i g => heckeCSD_comm_trRep _ _ _ _ _ _ _ i g
  blocks := Col.blockOk_firstValA (fun (P : ↥(offSub ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0)) =>
      Ch.muVal j P.1.1 * xiVal τ.1 P.1.1) (fun P => Ch.etaVal P.1.1) (q := fun P => Col.SplitOff.q P.1) R.r
    R.t_odd.pos (fun P => Col.SplitOff.q_ne_zero P.1)
  q_pos := fun P => Nat.pos_of_ne_zero (Col.SplitOff.q_ne_zero P.1)
  pl_inj := Subtype.val_injective

theorem colFam_ok (hH : ColHyp W Ch sel v0 TU Xg S0) : (colFam W Ch sel hX v0 TU Xg S0 xiVal).Ok 1 where
  conj := hH.conj
  tup_fin := tupF_finite TU
  irr := hH.irr
  what₂ := colFam_rows_ok W Ch sel hX v0 TU Xg S0 xiVal hH.commR hH.splitR
  lifts := colFam_lifts_ok W Ch sel hX v0 TU Xg S0 xiVal hH.commL hH.splitL




theorem colFam_typesSep : (colFam W Ch sel hX v0 TU Xg S0 xiVal).TypesSep := by
  unfold colFam
  refine FamIn.typesSep_of' (A := colIn W Ch sel hX v0 TU Xg S0 xiVal) (fun P => ?_) (fun P => ?_)
  · first
      | exact Col.SplitOff.q_ne_zero _
      | exact_mod_cast Col.SplitOff.q_ne_zero _
  · exact heckeCSD_zero _ _ _ _ _ P

end Inst

section Xi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

def IsUnifIdele (P : HeightOneSpectrum (𝓞 E)) (u : (AfE F E)ˣ) : Prop :=
  ∃ (v : HeightOneSpectrum (𝓞 F)) (hu : (u : AfE F E) ∈ RInt F E) (b : 𝓞 E),
    P.asIdeal.under (𝓞 F) = v.asIdeal ∧ u ∈ suppAt E v ∧ b ∈ P.asIdeal ∧ b ∉ P.asIdeal ^ 2 ∧
    (⟨(u : AfE F E), hu⟩ : RInt F E) - toRInt F E b ∈ (P.asIdeal ^ 2).map (toRInt F E) ∧
    ∀ P' : HeightOneSpectrum (𝓞 E), P' ≠ P → (⟨(u : AfE F E), hu⟩ : RInt F E) - 1 ∈ P'.asIdeal.map (toRInt F E)

open Classical in

def unifVal (ξ : Chr F E L) (P : HeightOneSpectrum (𝓞 E)) : Lˣ :=
  if h : ∃ u, IsUnifIdele (F := F) P u then ξ h.choose else 1




end Xi

section XiCol

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

def xiVal (τ : Tup X.F X.E X.K S) (P : HeightOneSpectrum (𝓞 X.E)) : X.Kˣ := unifVal (τ : Chr X.F X.E X.K) P

variable (hX : X.Ok) (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))

def colInX : FamIn X.K (Col.G0 X.E Pr.vGs R.r) (Col.LevOff ∅ Pr.vGs S0) (TupF TU) R.m :=
  colIn W Ch sel hX v0 TU Xg S0 xiVal

theorem colInX_ok (hH : ColHyp W Ch sel v0 TU Xg S0) : (colInX W Ch sel hX v0 TU Xg S0).fam.Ok 1 :=
  colFam_ok W Ch sel hX v0 TU Xg S0 xiVal hH

theorem colInX_typesSep : (colInX W Ch sel hX v0 TU Xg S0).fam.TypesSep :=
  colFam_typesSep W Ch sel hX v0 TU Xg S0 xiVal

end XiCol

section LinkCol

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))

open Formalism.L2.Col in

theorem division_height_bound_columns (hH : ColHyp W Ch sel v0 TU Xg S0)
    (P0 : Subgroup (Col.G0 X.E Pr.vGs R.r)) (ψ0 : P0 →* X.Kˣ) (P1 : Subgroup (Col.G0 X.E Pr.vGs R.r)) (ψ1 : P1 →* X.Kˣ)
    {P : LevFam X.E X.K R.r Pr.vGs} {m2 : ℕ} {Gc : ChGlob X R.m}
    {Sg : Set ℕ} (mu : (colInX W Ch sel hX v0 TU Xg S0).fam.base.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx X Pr R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := R) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    (Ak : ∀ t x, ChKer W Ch sel (mu t) (cst t) (L t) P (wd x) m2 (b t x) (hY t x))
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) P (wd x)).Ok)
    (ev : ∀ (Zs : DefSub (colInX W Ch sel hX v0 TU Xg S0).fam.amb) t, (Fin (((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg P)
    (Sp : ∀ Zs : DefSub (colInX W Ch sel hX v0 TU Xg S0).fam.amb, SPer (colFace hX ((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY Ak hF (ev Zs)))
    (Zsc : DefSub (colInX W Ch sel hX v0 TU Xg S0).fam.amb → IndefScale (colInX W Ch sel hX v0 TU Xg S0).fam.base) (C CH : ℝ)
    (Pk : IndefPkg (colInX W Ch sel hX v0 TU Xg S0).fam.amb
      (faceOf (colInX W Ch sel hX v0 TU Xg S0) P0 ψ0 P1 ψ1 (fun Zs => colFace hX ((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY Ak hF (ev Zs)) Sp Zsc) C CH)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (Rn : RecNums (colInX W Ch sel hX v0 TU Xg S0).fam.base.J Pl) (x : Mem)
    (Nu : Submodule (𝓞 X.K) (Fin (ramDim W Ch hX (wd x)) → X.K)) (sg : HeightOneSpectrum (𝓞 X.K) → ℝ)
    (I : DivInputs Pk.core Rn x Nu sg)
    (hQ : ChainTie I.ch (memQ (A := Ak) (hF := hF) hE (x := x))) (h0 : FirstCols hE hQ) (hPL : LastPer hE hQ) :
    DivClauses Pk.core Rn x Nu sg ∧
      (∀ y : Fin (I.ch.c 0) → X.K,
        hQ.coL ((chainMat I.ch.Kj ⟨(memQ (A := Ak) (hF := hF) hE (x := x)).n + 1, by have := hQ.hmm; omega⟩).mulVec y) =
          colC (Ak (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hF (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hL (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0)
            (colOfCoord W Ch hX (wd x) fun i => y (Fin.cast I.ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim W Ch hX (wd x)) → X.K) (F : Fin (((colInX W Ch sel hX v0 TU Xg S0).side P1 ψ1 Pk.Zs).nV (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) → X.K),
        I.ch.PtL ((chainMat I.ch.Kj (Fin.last I.ch.mm)).mulVec fun i => φ (Fin.cast I.ch.c0 i)) F =
          colPerL (hP (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) Xg (wd x) (ev Pk.Zs (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0)
            (colC (Ak (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hF (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0 x) (hL (colInX W Ch sel hX v0 TU Xg S0).fam.base.μ0) (colOfCoord W Ch hX (wd x) φ)) F := by
  haveI := hX.cplxK
  exact division_height_bound (colInX W Ch sel hX v0 TU Xg S0) (colInX_ok W Ch sel hX v0 TU Xg S0 hH)
    (colInX_typesSep W Ch sel hX v0 TU Xg S0) P0 ψ0 P1 ψ1 hX Xg mu cst L hL hP Mem wd b hY Ak hF hE ev Sp Zsc C CH Pk
    Rn x Nu sg I hQ h0 hPL

end LinkCol

end Formalism.L2.DIV
end
end

section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section OffI

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def offSubI (ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    Set (Col.LevOffI ST SG S0) :=
  {P | P.1 ∉ S0 ∪ (↑ST : Set (HeightOneSpectrum (𝓞 E))) ∪ (↑SG' : Set (HeightOneSpectrum (𝓞 E)))}

def offSubI.lev {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))} {S0 : Set (HeightOneSpectrum (𝓞 E))}
    (P : offSubI ST SG SG' S0) : Col.LevOffI ST SG' S0 :=
  ⟨P.1.1, P.1.2.1, P.1.2.2.1, P.2⟩

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} {ST SG' : Finset (HeightOneSpectrum (𝓞 E))}

def heckeCSDI (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG') (SG : Finset (HeightOneSpectrum (𝓞 E)))
    (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    offSubI ST SG SG' S0 × List ℕ → Module.End K (S.toCSD h).Forms :=
  fun x => (S.res h).conj (Col.heckeFamI c S0 (offSubI.lev x.1, x.2))

variable (S : Col.GSD K) (h : S.Ok) (c : Col.DecoPts S E n ST SG') (SG : Finset (HeightOneSpectrum (𝓞 E)))
  (S0 : Set (HeightOneSpectrum (𝓞 E)))

private theorem commute_conj_of_commute {R0 V0 W0 : Type} [CommRing R0] [AddCommGroup V0] [Module R0 V0]
    [AddCommGroup W0] [Module R0 W0] (e : V0 ≃ₗ[R0] W0) {a b : Module.End R0 V0} (hab : Commute a b) :
    Commute (e.conj a) (e.conj b) := by
  have h1 : a * b = b * a := hab.eq
  show e.conj a * e.conj b = e.conj b * e.conj a
  apply LinearMap.ext
  intro x
  have h2 := LinearMap.congr_fun h1 (e.symm x)
  change e (a (e.symm (e (b (e.symm x))))) = e (b (e.symm (e (a (e.symm x)))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact congrArg e h2

theorem heckeCSDAll_comm (hc : Col.HeckeCommAll c S0) :
    Col.PairComm (Sum.elim (heckeCSD S h c SG S0) (heckeCSDI S h c SG S0)) := by
  intro i j
  rcases i with ⟨P, k⟩ | ⟨P, k⟩ <;> rcases j with ⟨Q, l⟩ | ⟨Q, l⟩
  · exact commute_conj_of_commute _ (hc (Sum.inl _) (Sum.inl _))
  · exact commute_conj_of_commute _ (hc (Sum.inl _) (Sum.inr _))
  · exact commute_conj_of_commute _ (hc (Sum.inr _) (Sum.inl _))
  · exact commute_conj_of_commute _ (hc (Sum.inr _) (Sum.inr _))

private theorem iSup_maxGenEigenspace_conj_eq_whole {K0 V0 W0 : Type} [Field K0] [AddCommGroup V0] [Module K0 V0]
    [AddCommGroup W0] [Module K0 W0] (e : V0 ≃ₗ[K0] W0) (f : Module.End K0 V0)
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤) : ⨆ μ, (e.conj f).maxGenEigenspace μ = ⊤ := by
  have key : ∀ (μ : K0) (k : ℕ) (x : V0),
      ((e.conj f - μ • (1 : Module.End K0 W0)) ^ k) (e x) = e (((f - μ • (1 : Module.End K0 V0)) ^ k) x) := by
    intro μ k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', pow_succ']
      change (e.conj f - μ • (1 : Module.End K0 W0)) (((e.conj f - μ • (1 : Module.End K0 W0)) ^ k) (e x)) =
        e ((f - μ • (1 : Module.End K0 V0)) (((f - μ • (1 : Module.End K0 V0)) ^ k) x))
      rw [ih]
      simp [LinearEquiv.conj_apply]
  rw [eq_top_iff]
  intro y _
  have hy : e.symm y ∈ ⨆ μ, f.maxGenEigenspace μ := by
    rw [hf]
    exact Submodule.mem_top
  have hmap : Submodule.map (e : V0 →ₗ[K0] W0) (⨆ μ, f.maxGenEigenspace μ) ≤
      ⨆ μ, (e.conj f).maxGenEigenspace μ := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun μ => ?_
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ f.maxGenEigenspace μ := hx
    rw [Module.End.mem_maxGenEigenspace] at hx'
    obtain ⟨k, hk⟩ := hx'
    show e x ∈ (e.conj f).maxGenEigenspace μ
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨k, by rw [key, hk, map_zero]⟩
  exact hmap ⟨e.symm y, hy, by simp⟩

theorem heckeCSDI_split (hs : Col.HeckeFieldsInI c S0) : Col.SplitOver (heckeCSDI S h c SG S0) := by
  intro i
  exact iSup_maxGenEigenspace_conj_eq_whole _ _ (hs (offSubI.lev i.1, i.2))

end OffI

section TrI

variable {X : Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : Col.CoefPk X n (Col.DecoSet X.E n ST SG)) (Λ : Col.LevFam X.E X.K n SG)

theorem heckeCSDI_comm_trRep (h : (Col.formGSD C Λ).Ok) {A : Type} [Group A] (ι : A →* Col.GLG X.E n SG)
    (hι : ∀ a w, (Λ w).NormBy (ι a w)) (SG0 : Finset (HeightOneSpectrum (𝓞 X.E)))
    (S0 : Set (HeightOneSpectrum (𝓞 X.E))) (x : offSubI ST SG0 SG S0 × List ℕ) (a : A) :
    Commute (heckeCSDI (Col.formGSD C Λ) h (formPts C Λ) SG0 S0 x)
      ((Col.formGSD C Λ).repCSD h (Col.trRep C Λ ι hι) a) := by
  have h1 := (Col.heckeFamI_comm_trRep (C := C) (Λ := Λ) (ι := ι) (hι := hι) (S0 := S0)
    (y := (offSubI.lev x.1, x.2)) (a := a)).eq
  show _ * _ = _ * _
  apply LinearMap.ext
  intro f
  change (Col.formGSD C Λ).res h (Col.heckeFamI (formPts C Λ) S0 (offSubI.lev x.1, x.2)
      (((Col.formGSD C Λ).res h).symm ((Col.formGSD C Λ).res h
        (Col.trRep C Λ ι hι a (((Col.formGSD C Λ).res h).symm f))))) =
    (Col.formGSD C Λ).res h (Col.trRep C Λ ι hι a
      (((Col.formGSD C Λ).res h).symm ((Col.formGSD C Λ).res h
        (Col.heckeFamI (formPts C Λ) S0 (offSubI.lev x.1, x.2) (((Col.formGSD C Λ).res h).symm f)))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact congrArg _ (LinearMap.congr_fun h1 _).symm

end TrI

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

def colIn3 (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
    (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
    (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
    (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) :
    FamIn3 X.K (Col.G0 X.E Pr.vGs R.r) (Col.LevOff ∅ Pr.vGs S0) (Col.LevOffI ∅ Pr.vGs S0) (List ℕ) (TupF TU) R.m where
  A := colIn W Ch sel hX v0 TU Xg S0 xiVal
  okI := fun τ => offSubI ∅ Pr.vGs (Col.rowSG Pr sel τ.1) S0
  heckeRI := fun τ => heckeCSDI (Col.mtildeKGSD W Ch sel τ.1) (Col.mtildeKOk W Ch sel τ.1 hX) (formPts _ _) Pr.vGs S0
  heckeLI := fun j τ =>
    heckeCSDI (Col.mtKGSD W Ch sel τ.1 (j.1 + 1)) (Col.mtKOk W Ch sel τ.1 hX (j.1 + 1)) (formPts _ _) Pr.vGs S0
  trI := trIv

variable (v0 : InfinitePlace X.K) (TU : Finset (Tup X.F X.E X.K S))
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)

def colFam3 : DefFam3 X.K (Col.G0 X.E Pr.vGs R.r) (Col.LevOff ∅ Pr.vGs S0) (Col.LevOffI ∅ Pr.vGs S0) (List ℕ) (TupF TU)
    (Fin R.m) :=
  (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).fam3

def colSide3 (P : Col.LevFam X.E X.K R.r Pr.vGs) (Zs : DefSub (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3) :
    DefSide (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).base3 :=
  (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).side3 P.grp P.chr Zs

structure ColHyp3 : Prop where

  base : ColHyp W Ch sel v0 TU Xg S0

  commAllR : ∀ τ : TupF TU, Col.HeckeCommAll (rowPts W Ch sel τ.1) S0

  splitIR : ∀ τ : TupF TU, Col.HeckeFieldsInI (rowPts W Ch sel τ.1) S0

  commAllL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeCommAll (liftPts W Ch sel τ.1 (j.1 + 1)) S0

  splitIL : ∀ (j : Fin R.m) (τ : TupF TU), Col.HeckeFieldsInI (liftPts W Ch sel τ.1 (j.1 + 1)) S0

theorem colFam3_ok (hH : ColHyp3 W Ch sel v0 TU Xg S0) : (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).Ok3 1 where
  ok2 := colFam_ok W Ch sel hX v0 TU Xg S0 xiVal hH.base
  what₂ τ :=
    { comm := heckeCSDAll_comm _ _ _ _ _ (hH.commAllR τ)
      split := heckeCSDI_split _ _ _ _ _ (hH.splitIR τ)
      opG := fun k g => heckeCSDI_comm_trRep _ _ _ _ _ _ _ k g
      plI_inj := Subtype.val_injective }
  lifts j τ :=
    { comm := heckeCSDAll_comm _ _ _ _ _ (hH.commAllL j τ)
      split := heckeCSDI_split _ _ _ _ _ (hH.splitIL j τ)
      opG := fun k g => heckeCSDI_comm_trRep _ _ _ _ _ _ _ k g
      plI_inj := Subtype.val_injective }

theorem colFam3_typesSep (hc : Col.HeckeComm (rowPts W Ch sel (mu0 X.F X.E X.K S)) S0)
    (hI : (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TrISep) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TypesSep3 :=
  (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).typesSep3_of' (fun P => Col.SplitOff.q_ne_zero P)
    (fun P => heckeCSD_zero _ _ _ _ _ P) (heckeCSD_comm _ _ _ _ _ hc) hI

theorem colFam3_typesSep' (hH : ColHyp3 W Ch sel v0 TU Xg S0)
    (hI : (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TrISep) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TypesSep3 :=
  colFam3_typesSep W Ch sel hX v0 TU Xg S0 xiVal trIv (hH.base.commR (mu0F TU)) hI


end Inst

end Formalism.L2.DIV
end
end
