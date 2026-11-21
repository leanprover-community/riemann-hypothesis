import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonCoefficientMapLiftPresentation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdSideUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLiftReadingOfDecoratedLatticePresentatio
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthogonalSumCoefficientLatticeIsLatticeAndDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeedAtReadingKeeping
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParabolicCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueIsStdChar
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleLiftFormsPassToCoeffEnlargement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicCoreTransportEnlargedCoefficientBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValuesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RecAtOfTwoPasses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIndexBoundCoreOverExactSmallField

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Mem.R3.BrgAt

open GlobalTheory.Mem.R3.LiftPresStd GlobalTheory.Mem.R3.BrgRead

theorem vv_cast_heq : ∀ {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] {ι : Type} [Fintype ι]
    (emb : ι → E →+* K) {n n' : ℕ} (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n'),
    (∀ τ a, (lam τ).w a = (lam' τ).w (Fin.cast h a)) →
    ∃ e : VV K lam ≃ₗ[K] VV K lam', (∀ v, HEq (e v) v) ∧
      (∀ (g : GL (Fin n') E) v, e (rhoVr emb lam (LiftBrg.castGL h.symm g) v) = rhoVr emb lam' g (e v)) ∧
      (∀ (J : Matrix (Fin n) (Fin n) E) x y,
        pairVr emb lam' (J.reindex (finCongr h) (finCongr h)) (e x) (e y) = pairVr emb lam J x y) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (nabAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        nabAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ N : Submodule (𝓞 E) (Fin n → E), (delAtr emb lam N).map (e.toLinearMap.restrictScalars (𝓞 K)) =
        delAtr emb lam' (N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr h).symm).toLinearMap)) ∧
      (∀ i j, (bVV K lam').repr (e (bVV K lam i)) j ∈ Formalism.DivisionValues.cmMax K) ∧
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (c0 : VV K lam' →ₛₗ[σ] W),
        LinearIndependent ℂ (fun i => c0 (bVV K lam' i)) → Submodule.span ℂ (Set.range fun i => c0 (bVV K lam' i)) = ⊤ →
        LinearIndependent ℂ (fun i => c0 (e (bVV K lam i))) ∧ Submodule.span ℂ (Set.range fun i => c0 (e (bVV K lam i))) = ⊤) := by
  intro E K _ _ _ _ _ ι _ emb n n' h lam lam' hl
  subst h
  have hlam : lam = lam' := by
    funext τ
    have h1 := hl τ
    rcases hw : lam τ with ⟨w, hw1⟩
    rcases hw' : lam' τ with ⟨w', hw1'⟩
    rw [hw, hw'] at h1
    have : w = w' := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hlam
  have hN : ∀ N : Submodule (𝓞 E) (Fin n → E),
      N.map (LinearEquiv.funCongrLeft (𝓞 E) E (finCongr (rfl : n = n)).symm).toLinearMap = N := by
    intro N
    ext x
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      convert hy using 1
      funext a
      rfl
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨LinearEquiv.refl K _, fun _ => HEq.rfl, fun g v => ?_, fun J x y => ?_, fun N => ?_, fun N => ?_, fun i j => ?_, fun W _ _ σ c0 h1 h2 => ⟨h1, h2⟩⟩
  · have : LiftBrg.castGL (rfl : n = n).symm g = g := by ext a b; simp [LiftBrg.castGL]
    rw [this]; rfl
  · have : J.reindex (finCongr (rfl : n = n)) (finCongr (rfl : n = n)) = J := by ext a b; simp
    rw [this]; rfl
  · rw [hN]; exact Submodule.map_id _
  · rw [hN]; exact Submodule.map_id _
  · show (bVV K lam).repr (bVV K lam i) j ∈ Formalism.DivisionValues.cmMax K
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem exists_pres_heq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 →
    ∃ c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W, (∀ v v', HEq v' v → c v = c0L v') ∧ (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v)) ∧
      ∀ t : TupU I U, ∃ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t 1 1 P ∧
        (∀ v, P.coef v = c v) ∧ Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef P (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) := by
  intro X px I hX U Xg tr L eG0 hI hV hL hG cV i c0L hcV hmap hin hβ hgram
  obtain ⟨e0, he0, he_rho, he_pair, he_nab, he_del, he_rat, he_li⟩ :=
    vv_cast_heq X.B.fields.emb (LiftBrg.rkEq X i) (X.B.wts.lamV ((i : ℕ) + 1))
      (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) (GlobalTheory.T.baseWeight_eq_forcedLiftWeight X i)
  let c : VV X.B.fields.K (X.B.wts.lamV ((i : ℕ) + 1)) →ₛₗ[X.B.embLL] (cV i).W :=
    { toFun := fun v => c0L (e0 v)
      map_add' := fun v w => by show c0L (e0 (v + w)) = c0L (e0 v) + c0L (e0 w); rw [map_add]; exact c0L.map_add _ _
      map_smul' := fun a v => by show c0L (e0 (a • v)) = _; rw [LinearEquiv.map_smul]; exact c0L.map_smulₛₗ a (e0 v) }
  have hc : ∀ v, c v = c0L (e0 v) := fun v => rfl
  have hint : ∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE →
      ∀ v, c (rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) (LiftBrg.castGL (LiftBrg.rkEq X i).symm γE) v) = (cV i).coef.ρ γ (c v) := by
    intro γ γE h v
    exact (congrArg c0L (he_rho γE v)).trans (hmap.1 γ γE h (e0 v))
  refine ⟨c, fun v v' h => congrArg c0L (eq_of_heq ((he0 v).trans h.symm)), hint, fun t => ?_⟩
  obtain ⟨eG, eΓ, hchar, hι, hrat⟩ := GlobalTheory.T.exists_unitaryGroups_equiv_unitForm_gram_one X i hgram
  obtain ⟨hJ, hχ⟩ := GlobalTheory.T.liftAdelicForm_level_type_eq_columnLevel X px I U L hI hV hL i t eG hchar
  letI : Algebra X.toD7.host.F X.B.fields.E := inferInstanceAs (Algebra X.toD7.host.F X.toD7.host.E)
  have hneg : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  have hgr : (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) =
      (1 : Matrix (Fin X.B.R.nV) (Fin X.B.R.nV) X.toD7.host.E).reindex (finCongr (LiftBrg.rkEq X i)) (finCongr (LiftBrg.rkEq X i)) := by
    rw [hneg, if_neg (by simp), hgram]
    ext a b
    simp [Matrix.one_apply]
  have hSG : Formalism.L2.Col.DecoPtSurj X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) :=
    Formalism.L2.Col.decoPtSurj_of _ _ _ _ (Formalism.L2.Col.unimodGenus_holds _ _) Formalism.L2.DIV.reduction_surjective_bis
      (by classical convert GlobalTheory.T.rowFormLevelPrimes_isSplitSet X px I U L hI hL t using 1; exact Finset.empty_union _) (Finset.disjoint_empty_left _)
  let o := Formalism.L2.Col.rf_onDeco (X := X.B.fields) (n := X.B.R.nV) (ST := ∅) (SG := LiftBrg.sgL X I U t)
    (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) _) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv
  have hmem : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (eG.toMonoidHom.comp (Subgroup.subtype _)) k ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J := fun k => by
    rw [hJ]; exact Subgroup.mem_map_of_mem _ k.2
  let χc := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ.comp ((eG.toMonoidHom.comp (Subgroup.subtype _)).codRestrict _ hmem)
  have hχc : ∀ k, ((χc k)⁻¹ : ℂˣ) = Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
      (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
        ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) := fun k => (hχ k (hmem k)).1
  have hK1 : ∀ k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp,
      (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) → χc k = 1 :=
    fun k hk => (hχ k (hmem k)).2 hk
  have hli := he_li (cV i).W X.toD7.what₂.embLL c0L hmap.2.1 hmap.2.2
  have hpair : ∀ x x', inner ℂ (c x) (c x') = X.toD7.what₂.embLL ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).pair x x') := by
    intro x x'
    refine (hin (e0 x) (e0 x')).trans ?_
    congr 1
    rw [hgr]
    exact he_pair 1 x x'
  have hgl : ∀ (γ : Formalism.L2.Col.URat X.toD7.sp.cm X.B.R.nV) k (v : (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).V),
      c ((Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v) =
        ((χc k)⁻¹ : ℂˣ) • ((cV i).coef.ρ.comp eΓ.toMonoidHom) γ (c v) := by
    intro γ k v
    rw [show (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).ρ (Bridge.colGl o (γ, k)) v = _ from
      formRho_colGl (X := X.B.fields) X.toD7.sp.cm _ _ γ k v]
    refine (c.map_smulₛₗ _ _).trans ?_
    have e3 : (Formalism.L2.Col.mtVal (Pr := X.B.primes px) X.B.wts ((i : ℕ) + 1) (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)).rho
        (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ) v =
        rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
          (LiftBrg.castGL (LiftBrg.rkEq X i).symm (LiftBrg.castGL (LiftBrg.rkEq X i) (γ : GL (Fin X.B.R.nV) X.toD7.host.E))) v := by
      show rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1))
        (Formalism.L2.Col.ufGL X.toD7.host.E X.B.R.nV (Formalism.L2.Col.ratHom X.toD7.sp.cm X.B.R.nV γ)) v = _
      rw [ufGL_ratHom]
      exact congrArg (fun g => rhoVr X.B.fields.emb (X.B.wts.lamV ((i : ℕ) + 1)) g v) (castGL_symm_castGL (LiftBrg.rkEq X i) _).symm
    have e2 := hint (eΓ γ) _ (hrat γ) v
    have e4 := (congrArg c e3).trans e2
    rw [hχc k, Units.smul_def]
    erw [e4]
    rfl
  let A := Bridge.colAdPts o hSG
  let P0 := Bridge.colClassPres (hc := X.toD7.sp.cm) o hSG (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
    ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl
  let P : LiftBrg.PresL X I hX U Xg tr L cV i t :=
    P0.transport eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl)
  refine ⟨P, ?_, fun v => rfl, e0, he_rat, fun x => rfl, ?_, ?_, ?_⟩
  · intro f g
    have h5 := GlobalTheory.T.transportedClassSetPresentation_reads_equivariant (ι' := Bridge.ratF (Vc X.toD7 i)) (ρ' := (cV i).coef.ρ) (J' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J)
      (χ' := (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ) A (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) X.toD7.what₂.embLL
      ((cV i).coef.ρ.comp eΓ.toMonoidHom) χc c hli.1 hli.2 hpair hK1 hgl eG eΓ hι (fun _ => rfl) hJ (fun k hk => rfl) f g
    refine h5.trans ?_
    have hq : A.q (eG.symm g) = LiftBrg.ptL X I U i t 1 1 g := by
      show Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (eG.symm g)) = _
      rw [Formalism.L2.Col.decoPt_mk]
      unfold LiftBrg.ptL
      congr 1
      have := hchar (eG.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [this]
      simp
    erw [hq]
    rfl
  · intro x x'
    rw [hgr]
    exact he_pair 1 x x'
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (nabAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_nab _
  · intro cl
    have h6 := GlobalTheory.T.translatedStdLattice_eq_decoratedLattice_reindexed X i (L.ΛV i) (by rw [← hβ]; exact hL.is.βV i) (LiftBrg.sgL X I U t) eG hchar (A.y cl)
    have hy := A.q_y cl
    have hy' : Formalism.L2.Col.decoPt X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (QuotientGroup.mk (A.y cl)) =
        (Formalism.L2.Col.mtKGSD X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).outSec.rep cl := hy
    refine Eq.trans ?_ (congrArg (delAtr (labLL X.toD7) (fun τ => Bridge.lamLdef (D := X.toD7) (Vc X.toD7 i).rank ((i : ℕ) + 1) τ)) h6).symm
    rw [hy']
    exact he_del _

theorem exists_liftSide_at : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m)
    (c0L : VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W),
    (cV i).Is → Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef c0L (rhoVr (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0L x) (c0L y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _
      (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) →
    L.βV i = 1 → (Vc X.toD7 i).gram = 1 → Seed.FrmC.StdLat (Vc X.toD7 i) → ∃ s : ∀ t, Seed.LiftSideT (famR X I hX U Xg tr) L cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) i t, (∀ t,       (∀ q : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q,
        eG ((s t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf (Vc X.toD7 i)) : GL _ _))) ∧
      Bridge.CoefTie (X.toD7.sp.V ((i : ℕ) + 1)) (cV i).coef (s t).pres (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) c0L
        (pairVr (labLL X.toD7) _
          (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(X.toD7.sp.V ((i : ℕ) + 1)).gram else (X.toD7.sp.V ((i : ℕ) + 1)).gram))
        (nabAtr (labLL X.toD7) _) (delAtr (labLL X.toD7) _) ∧
      Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) (s t).pres ((famR X I hX U Xg tr).heckeLI i t)
        (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
        (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
        fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1)) ∧ BrgStdV X I hX U Xg tr L i (cV i) (fun t φ => (s t).pres.extL φ) ∧
    ∀ (t : TupU I U) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)) v', HEq v' (φ.1 (LiftBrg.ptL X I U i t 1 1 h)) → (s t).pres.extL ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) φ :))) h = c0L v' := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i c0L hcV hmap hin hβ hg _
  obtain ⟨c, hce, hc, hP⟩ := exists_pres_heq X px I hX U Xg tr L eG hI hV hL hG cV i c0L hcV hmap hin hβ hg
  choose P hR hco hC using hP
  have hF : ∀ t, LiftBrg.FrameOK X I U i t 1 1 := fun t => GlobalTheory.T.identity_integralUnitaryFrameCoordinates_of_unitGram X px I U i t hg
  choose a ha using fun t => GlobalTheory.T.exists_finiteGroupAction_liftForms_rightTranslation X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  have hk := fun t => GlobalTheory.T.splitHecke_operators_lifts_doubleCoset X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  have hki := fun t => GlobalTheory.T.exists_inertHecke_doubleCosetOperators_lifts X px I hX U Xg tr L eG hI hV hL hG cV i t 1 1 (hF t) (P t) (hR t)
  refine ⟨fun t => Bridge.SideRealG.mk (P t) (a t) (Classical.choice (hk t)), fun t => ⟨ha t, hC t, hki t⟩,
    GlobalTheory.T.standardLiftReading_of_decoratedLatticePresentations X px I hX U Xg tr L eG hI hV hL hG cV i hβ hg c hc P hR hco, fun t φ h v' hv => ?_⟩
  refine ((hR t _ h).trans (hco t _)).trans (hce _ _ ?_)
  rw [LinearEquiv.symm_apply_apply]
  exact hv

theorem exists_brgL_at : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (c0L : ∀ i : Fin X.toD7.R.m, VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W), (∀ i, (cV i).Is) → (∀ i, Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef (c0L i) (rhoVr (labLL X.toD7) _)) → (∀ i x y, inner ℂ (c0L i x) (c0L i y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _ (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) → ∃ (cX : CoefA X.toD7.sp.X') (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ (∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ) ∧ ∀ i : Fin X.toD7.R.m, ∀ (t : TupU I U) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)) v', HEq v' (φ.1 (LiftBrg.ptL X I U i t 1 1 h)) → Bd.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) φ :))) h = c0L i v' := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβX hβV hsX hsV θ hθ MX cV c0L hcV hmapL hinL
  have hVP : Seed.VPos X.toD7 := fun i => X.B.V_posDef _ (by omega) i.2
  obtain ⟨cX, -, prX, gramR, c0R, -, hcX, -, hdual, hiso, hgram, hmapR, -, hinR, -⟩ :=
    exists_coefData X.toD7 hVP θ hθ MX
  have hR := GlobalTheory.T.exists_rowForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hmapR hinR hβX hsX
  have hLf := fun i => exists_liftSide_at X px I hX U Xg tr L eG hI hV hL hG cV i (c0L i) (hcV i) (hmapL i) (hinL i) (hβV i)
    (gram_V X hI.spaces i) (hsV i)
  obtain ⟨sR, hsR, hstR⟩ := hR
  choose sL hsL hstL hrd using hLf
  obtain ⟨hok, hon, hit, hion⟩ := GlobalTheory.Mem.R3.famR_places X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hmu, heta, hroots⟩ := GlobalTheory.Mem.R3.Brg.values X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hdR, hdL⟩ := hecke_degrees X px I hX U Xg tr
  have hrk : X.toD7.sp.X'.rank = (famR X I hX U Xg tr).A.r + X.toD7.R.m * (famR X I hX U Xg tr).A.t := X.toD7.sp.X'_rank
  have hrkL : ∀ i : Fin X.toD7.R.m, (Vc X.toD7 i).rank = (famR X I hX U Xg tr).A.r + (famR X I hX U Xg tr).A.t :=
    fun i => X.toD7.sp.V_rank _ (by omega) i.2
  let B : Seed.BType (famR X I hX U Xg tr) L cX cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) :=
    { R := sR, L := fun i t => sL i t, rankR := hrk, rankL := hrkL }
  classical
  refine ⟨cX, fun P => P.1, L.Pg, B, fun Q => Q.1, L.Pg.image (fun PP => PP.under (𝓞 X.toD7.host.F)), prX,
    hcX, hdual, hiso, ?_, hstR, hstL, hrd⟩
  exact
    { red_R := fun t q => (hsR t).1 q
      red_L := fun i t q => (hsL i t).1 q
      tie := ⟨gramR, c0R, c0L,
        { ranks := ⟨rfl, rfl, rfl⟩
          v0 := rfl
          tauL_ok := fun τ => RingHom.ext fun x => embLL_labLL_eq τ x
          pl_inj := fun a b h => Subtype.ext h
          q := fun P => rfl
          S_fin := Set.toFinite _
          ok := hok
          gramR_eq := hgram
          mapR := hmapR
          mapL := hmapL
          coefR := fun t => (hsR t).2.1
          coefL := fun i t => (hsL i t).2.1 }⟩
      sb := rfl
      roots := hroots
      pl_onto := hon
      degR := hdR
      degL := hdL
      muVal := hmu
      etaVal := heta
      in_tie := hit
      in_onto := hion
      in_R := fun t => (hsR t).2.2
      in_L := fun i t => (hsL i t).2.2
      in_SF := fun v => by
        simp only [Finset.mem_image]
        refine exists_congr fun PP => and_congr_right fun _ => ?_
        rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, Ideal.under_def] }

end GlobalTheory.Mem.R3.BrgAt

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicReading_definiteForms_given_coefficients : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (c0L : ∀ i : Fin X.toD7.R.m, VV X.toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc X.toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[X.toD7.what₂.embLL] (cV i).W), (∀ i, (cV i).Is) → (∀ i, Bridge.CoefMapTie (Vc X.toD7 i) (cV i).coef (c0L i) (rhoVr (labLL X.toD7) _)) → (∀ i x y, inner ℂ (c0L i x) (c0L i y) = X.toD7.what₂.embLL (pairVr (labLL X.toD7) _ (if X.toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc X.toD7 i).gram else (Vc X.toD7 i).gram) x y)) → ∃ (cX : CoefA X.toD7.sp.X') (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ (∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ) ∧ ∀ i : Fin X.toD7.R.m, ∀ (t : TupU I U) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)) v', HEq v' (φ.1 (LiftBrg.ptL X I U i t 1 1 h)) → Bd.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res (Formalism.L2.Col.mtKOk X.B.wts I.Ch I.sel t.1 hX ((i : ℕ) + 1)) φ :))) h = c0L i v' := by
  atlas_forward_decl GlobalTheory.Mem.R3.BrgAt.exists_brgL_at
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CoefIso

theorem bcVV_rhoVr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
    (σ : K →+* ℂ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (g : GL (Fin n) E) (v : VV K lam) :
    GlobalTheory.CoefSpace.bcVV σ lam (rhoVr emb lam g v) =
      rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (GlobalTheory.CoefSpace.bcVV σ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map σ (actP lam (invTrK (embGL emb g)) v.1) =
    actP lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (MvPolynomial.map σ v.1)
  rw [GlobalTheory.CoefSpace.map_actP]
  congr 2

theorem invTr_unitary_one {n : ℕ} (U : GL (Fin n) ℂ) (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U = 1) :
    ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * (1 : Matrix (Fin n) (Fin n) ℂ) *
      ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hi : ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    calc ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        = ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U) * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [hU, Matrix.one_mul]
      _ = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  show (((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)ᴴ * 1 * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = 1
  have e : (((U : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᵀ)ᴴ = (U : Matrix (Fin n) (Fin n) ℂ)ᵀ := by
    ext i j
    simp
  rw [hi, Matrix.mul_one, e, ← Matrix.transpose_mul, hU, Matrix.transpose_one]

theorem ratMat_unitary {D : D7} (V : HSp D) (hg : V.gram = 1) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E)
    (h : Bridge.IsRatMat V γ γE) (φ : D.host.E →+* ℂ) :
    ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ *
      ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1 := by
  obtain ⟨γ, ⟨g, hgU, hgm⟩⟩ := γ
  have e1 : Formalism.UG.bc (incA D) g = Formalism.UG.bc (incA D) γE := hgm.trans h
  have e2 : g = γE := Units.ext (Matrix.ext fun i j =>
    (Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F))
      (congrArg (fun u => (Units.val u) i j) e1))
  subst e2
  have hu : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram := hgU
  rw [hg, Matrix.mul_one] at hu
  have hc : ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ)ᴴ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map φ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (D.sp.cm.cmUnram.2.1 φ _).symm
  rw [bc_coe, hc, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]

set_option maxHeartbeats 1000000 in

theorem coef_iso : ∀ (D : D7) (V : HSp D) (n : ℕ), V.rank = n → V.gram = 1 → ∀ (c : CoefA V), c.Is → ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (emb : ι → (D.host.E →+* K)) (lam : ι → DomWeight n) (c0 : VV K lam →ₛₗ[σ] c.W), Nonempty (VVIdx lam) →
  (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ v, c0 (rhoVr emb lam g v) = c.coef.ρ γ (c0 v)) →
  (LinearIndependent ℂ fun i => c0 (bVV K lam i)) →
  ∃ (e : VV ℂ lam ≃ₗ[ℂ] c.W) (s : ℝ), 0 < s ∧ (∀ v, c0 v = (s : ℂ) • e (GlobalTheory.CoefSpace.bcVV σ lam v)) ∧
    (∀ x y, inner ℂ (e x) (e y) = pairK lam (fun _ => 1) x y) ∧
    ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g →
      ∀ x, e (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.coef.ρ γ (e x) := by
  intro D V n hn hg c hc K ι _ _ _ σ emb lam c0 hne hint hli
  subst hn
  classical
  have hMat : ∀ γ : GQ V, ∃ γE, Bridge.IsRatMat V γ γE ∧ MatEq γE γE := fun γ => by
    obtain ⟨γE, h⟩ := GlobalTheory.Mem.StdUnique.exists_ratMat γ
    exact ⟨γE, h, rfl, fun i j i' j' hi hj => by rw [Fin.ext hi, Fin.ext hj]⟩
  have hmem : ∀ v, c0 v ∈ Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range (bVV K lam)) := by rw [(bVV K lam).span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  obtain ⟨i₀⟩ := hne
  have htop : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤ := by
    refine (GlobalTheory.Mem.StdUnique.bot_or_top c hc _ fun γ hγ w hw => ?_).resolve_left fun h0 => ?_
    · obtain ⟨γE, h1, h2⟩ := hMat ⟨γ, hγ⟩
      have hle : (Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i))).map (c.ρ γ) ≤
          Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨i, rfl⟩
        rw [show c.ρ γ (c0 (bVV K lam i)) = c.coef.ρ ⟨γ, hγ⟩ (c0 (bVV K lam i)) from rfl,
          ← hint ⟨γ, hγ⟩ γE γE h1 h2]
        exact hmem _
      exact hle ⟨w, hw, rfl⟩
    · have := hmem (bVV K lam i₀)
      rw [h0, Submodule.mem_bot] at this
      exact hli.ne_zero i₀ this
  let b1 : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (GlobalTheory.CoefSpace.bcVV_indep σ lam) (GlobalTheory.CoefSpace.bcVV_span σ lam).ge
  let b2 : Module.Basis (VVIdx lam) ℂ c.W := Module.Basis.mk hli htop.ge
  have hb1 : ∀ i, b1 i = GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  have hb2 : ∀ i, b2 i = c0 (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  obtain ⟨e0, he0b⟩ : ∃ e0 : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ i, e0 (b1 i) = b2 i :=
    ⟨b1.equiv b2 (Equiv.refl _), fun i => by simp⟩
  have he0 : ∀ v, e0 (GlobalTheory.CoefSpace.bcVV σ lam v) = c0 v := by
    intro v
    have : (e0.toLinearMap.comp (GlobalTheory.CoefSpace.bcVV σ lam) : VV K lam →ₛₗ[σ] c.W) = c0 :=
      (bVV K lam).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hb1, he0b, hb2]
    exact LinearMap.congr_fun this v
  have hR : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x,
      e0 (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.ρ γ (e0 x) := by
    intro γ γE g h1 h2 x
    have : e0.toLinearMap.comp (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g)) =
        (c.ρ γ).comp e0.toLinearMap := b1.ext fun i => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hb1, ← bcVV_rhoVr, LinearEquiv.coe_coe, he0, he0,
        hint γ γE g h1 h2]
      rfl
    exact LinearMap.congr_fun this x
  have hP : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x y : VV ℂ lam,
      pairK lam (fun _ => 1) (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x)
        (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) y) = pairK lam (fun _ => 1) x y := by
    intro γ γE g h1 h2
    obtain rfl : γE = g := Units.ext (Matrix.ext fun i j => h2.2 i j i j rfl rfl)
    exact pairInv ℂ ι V.rank lam (fun _ => 1) _ fun τ =>
      invTr_unitary_one (Formalism.UG.bc (σ.comp (emb τ)) γE) (ratMat_unitary V hg γ γE h1 _)
  have hgr : GlobalTheory.CoefSpace.gramOf (fun _ : ι => (1 : GL (Fin V.rank) ℂ)) = fun _ => 1 := by
    funext τ
    simp [GlobalTheory.CoefSpace.gramOf]
  let S : c.W →ₗ[ℂ] GlobalTheory.CoefSpace.HV lam (fun _ => (1 : GL (Fin V.rank) ℂ)) := e0.symm.toLinearMap
  have hS : ∀ w, S w = e0.symm w := fun _ => rfl
  let T : Module.End ℂ c.W := (LinearMap.adjoint S).comp S
  have hT : ∀ w w', inner ℂ w (T w') = pairK lam (fun _ => 1) (e0.symm w) (e0.symm w') := by
    intro w w'
    show inner ℂ w (LinearMap.adjoint S (S w')) = _
    rw [LinearMap.adjoint_inner_right, GlobalTheory.CoefSpace.inner_HV, hgr]
    rfl
  have hBinv : ∀ (γ : GQ V) a b, pairK lam (fun _ => 1) (e0.symm (c.ρ γ a)) (e0.symm (c.ρ γ b)) =
      pairK lam (fun _ => 1) (e0.symm a) (e0.symm b) := by
    intro γ a b
    obtain ⟨γE, h1, h2⟩ := hMat γ
    have key : ∀ a, e0.symm (c.ρ γ a) = rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) γE) (e0.symm a) :=
      fun a => by rw [LinearEquiv.symm_apply_eq, hR γ γE γE h1 h2, LinearEquiv.apply_symm_apply]
    rw [key, key, hP γ γE γE h1 h2]
  have hcomm : ∀ (γ : GQ V) x, T (c.ρ γ x) = c.ρ γ (T x) := by
    intro γ x
    refine ext_inner_left ℂ fun w => ?_
    have hinv : c.ρ γ (c.ρ (γ⁻¹ : GQ V) w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one,
        Module.End.one_apply]
    calc inner ℂ w (T (c.ρ γ x)) = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (T (c.ρ γ x)) := by rw [hinv]
      _ = pairK lam (fun _ => 1) (e0.symm (c.ρ (γ⁻¹ : GQ V) w)) (e0.symm x) := by rw [hT, hBinv]
      _ = inner ℂ (c.ρ (γ⁻¹ : GQ V) w) (T x) := (hT _ _).symm
      _ = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (c.ρ γ (T x)) := (hc.2.1 _ _ _).symm
      _ = inner ℂ w (c.ρ γ (T x)) := by rw [hinv]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Mem.RowCoord.scalar_of_comm_rat c hc T hcomm
  have hx₀ : GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀) ≠ 0 := by
    rw [← hb1]
    exact b1.ne_zero i₀
  have hpos := GlobalTheory.CoefSpace.pairK_pos lam (fun _ => 1) _ hx₀
  rw [hgr] at hpos
  have h1 := hT (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀)))
  have hsq : inner ℂ (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) =
      ((‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hμ, inner_smul_right, LinearEquiv.symm_apply_apply, hsq] at h1
  rw [← h1] at hpos
  have hn : 0 < ‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (e0.map_ne_zero_iff.2 hx₀)) 2
  obtain ⟨hre, him⟩ := Complex.lt_def.1 hpos
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal, Complex.zero_re, Complex.zero_im] at hre him
  have hm : 0 < μ.re := (pos_iff_pos_of_mul_pos hre).2 hn
  have hμr : ((μ.re : ℝ) : ℂ) = μ := Complex.ext rfl (by
    rw [Complex.ofReal_im]
    exact ((mul_eq_zero.1 him.symm).resolve_right hn.ne').symm)
  have hr : 0 < Real.sqrt μ.re := Real.sqrt_pos.2 hm
  have hr0 : ((Real.sqrt μ.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ x, e x = ((Real.sqrt μ.re : ℝ) : ℂ) • e0 x :=
    ⟨e0.trans (LinearEquiv.smulOfNeZero ℂ c.W _ hr0), fun _ => rfl⟩
  refine ⟨e, (Real.sqrt μ.re)⁻¹, inv_pos.2 hr, fun v => ?_, fun x y => ?_, fun γ γE g h1 h2 x => ?_⟩
  · rw [he, he0, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  · rw [he, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hm.le, hμr, ← inner_smul_right, ← hμ, hT, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  · rw [he, he, hR γ γE g h1 h2]
    exact ((c.ρ γ).map_smul _ _).symm

end GlobalTheory.Mem.CoefIso
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.GsdIso

open Formalism.L2.Col Formalism.IndefR.Bridge

theorem exists_isom_vec : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (ok : S.Ok) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* G) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : Bridge.ClassPres ι (S.toCSD ok) σ ρ J χ) (c : S.V →ₛₗ[σ] W) (d : G → S.D),
  (∀ (φ : S.EqFun) (h : G), P.extL (S.res ok φ) h = c (φ.1 (d h))) → (∃ φ : S.EqFun, φ ≠ 0) → ∃ v : S.V, c v ≠ 0 ∧ inner ℂ (c v) (c v) = σ (S.pair v v) := by
  classical
  intro K _ _ _ S ok G Γ W _ _ _ _ ι σ ρ J χ P c d H hne
  obtain ⟨φ, hφ⟩ := hne
  obtain ⟨k, hk⟩ : ∃ k, φ.1 (S.outSec.rep k) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ ((S.res ok).map_eq_zero_iff.1 (Subtype.ext (funext h)))
  set x := φ.1 (S.outSec.rep k) with hx
  have vi := (S.res ok φ).2 k
  let f : (S.toCSD ok).Forms := ⟨Pi.single k x, fun c' γ => by
    by_cases h : c' = k
    · subst h
      rw [Pi.single_eq_same]
      exact vi γ
    · rw [Pi.single_eq_of_ne h, map_zero]⟩
  have H1 := H ((S.res ok).symm f) (P.y k)
  rw [ClassPres.extL_apply, LinearEquiv.apply_symm_apply, GlobalTheory.PresBasic.ext_y] at H1
  have e2 : ((S.res ok).symm f).1 (d (P.y k)) =
      S.ρ (S.outSec.mv (d (P.y k))) ((Pi.single k x : S.Cl → S.V) (S.cls (d (P.y k)))) := rfl
  rw [e2] at H1
  have hfk : ((f : S.Cl → S.V)) k = x := by simp [f]
  rw [hfk] at H1
  have hc0 : P.coef x ≠ 0 := fun h => hk (GlobalTheory.PresBasic.coef_injective P (h.trans (map_zero _).symm))
  have hc : S.cls (d (P.y k)) = k := by
    by_contra h
    rw [Pi.single_eq_of_ne h, map_zero, map_zero] at H1
    exact hc0 H1
  rw [hc, Pi.single_eq_same] at H1
  refine ⟨S.ρ (S.outSec.mv (d (P.y k))) x, H1 ▸ hc0, ?_⟩
  rw [← H1, P.coef_pair, ok.inv]

end GlobalTheory.Mem.GsdIso
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.RsCoef

theorem glue {α β : Type} {a : α} {b c : β} (h2 : c = b) (h1 : HEq a b) : HEq a c := h2 ▸ h1

theorem coef_of_iso {D : D7} (V : HSp D) (c : CoefA V) {n : ℕ} (h : n = V.rank) (j : ℕ) (lam : D.what₂.Tau → DomWeight n)
    (hlam : ∀ τ a, (lam τ).w a = (Bridge.lamLdef (D := D) V.rank j τ).w (Fin.cast h a))
    (e : VV ℂ lam ≃ₗ[ℂ] c.W) (hinn : ∀ x y, inner ℂ (e x) (e y) = pairK lam (fun _ => 1) x y)
    (hie : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g →
      ∀ x, e (rhoK lam (invTrK fun τ => Formalism.UG.bc (tauE D τ) g) x) = c.coef.ρ γ (e x))
    (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hJ : J = 1) :
    ∃ c0 : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₛₗ[D.what₂.embLL] c.W,
      Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) _) ∧
      (∀ x y, inner ℂ (c0 x) (c0 y) = D.what₂.embLL (pairVr (labLL D) _ J x y)) ∧
      ∀ (v' : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ)) (x : VV ℂ lam),
        HEq (MvPolynomial.map D.what₂.embLL v'.1) x.1 → c0 v' = e x := by
  subst h
  have hl : lam = fun τ => Bridge.lamLdef (D := D) V.rank j τ := by
    funext τ
    have h1 := hlam τ
    rcases hw : lam τ with ⟨w1, hw1⟩
    rcases hw' : Bridge.lamLdef (D := D) V.rank j τ with ⟨w2, hw2⟩
    rw [hw, hw'] at h1
    have : w1 = w2 := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hl
  refine ⟨e.toLinearMap.comp (GlobalTheory.CoefSpace.bcVV D.what₂.embLL _), ⟨fun γ γE hr v => ?_, ?_, ?_⟩, fun x y => ?_,
    fun v' x hx => ?_⟩
  · show e (GlobalTheory.CoefSpace.bcVV _ _ (rhoVr (labLL D) _ γE v)) = c.coef.ρ γ (e (GlobalTheory.CoefSpace.bcVV _ _ v))
    rw [GlobalTheory.Mem.CoefIso.bcVV_rhoVr]
    have ht : (fun τ => Formalism.UG.bc (D.what₂.embLL.comp (labLL D τ)) γE) = fun τ => Formalism.UG.bc (tauE D τ) γE :=
      funext fun τ => by rw [show D.what₂.embLL.comp (labLL D τ) = tauE D τ from GlobalTheory.ThetaFiresProbe.labE_fixed τ]
    rw [ht]
    exact hie γ γE γE hr ⟨rfl, fun a b a' b' ha hb => by rw [Fin.ext ha, Fin.ext hb]⟩ _
  · exact (GlobalTheory.CoefSpace.bcVV_indep D.what₂.embLL _).map' e.toLinearMap (LinearEquiv.ker e)
  · have hs := congrArg (Submodule.map e.toLinearMap)
      (GlobalTheory.CoefSpace.bcVV_span D.what₂.embLL (fun τ => Bridge.lamLdef (D := D) V.rank j τ))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at hs
    exact hs
  · subst hJ
    show inner ℂ (e _) (e _) = _
    rw [hinn, pairVr, ← GlobalTheory.CoefModel.pairK_mapVV D.what₂.embLL _ D.starLL_cx]
    have h1 : (fun τ => (gramKd (labLL D) (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) τ).map D.what₂.embLL) =
        fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
      funext τ
      simp [gramKd]
    rw [h1]
    rfl
  · show e (GlobalTheory.CoefSpace.bcVV _ _ v') = e x
    congr 1
    exact Subtype.ext (eq_of_heq hx)

theorem cast_one {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (y : GL (Fin a) A) :
    LiftBrg.castGL h (y * 1) = (1 : GL (Fin b) A)⁻¹ * LiftBrg.castGL h y * 1 * 1 := by
  simp only [mul_one, inv_one, one_mul]

theorem scale_eq_one {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {s : ℝ} (hs : 0 < s) {x : W} (h0 : (s : ℂ) • x ≠ 0)
    (h : inner ℂ ((s : ℂ) • x) ((s : ℂ) • x) = inner ℂ x x) : s = 1 := by
  have hx : x ≠ 0 := fun e => h0 (by rw [e, smul_zero])
  have hne : inner ℂ x x ≠ 0 := fun e => hx (inner_self_eq_zero.1 e)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc] at h
  have h2 : ((s : ℂ) * s) = 1 := (mul_eq_right₀ hne).1 h
  have h3 : s * s = 1 := by exact_mod_cast h2
  nlinarith

theorem pair_bc {K E ι : Type} [Field K] [NumberField K] [StarRing K] [Field E] [NumberField E] [StarRing E] [Fintype ι] {n : ℕ} (σ : K →+* ℂ)
    (hσ : ∀ x, σ (star x) = star (σ x)) (emb : ι → (E →+* K)) (lam : ι → DomWeight n) (x y : VV K lam) :
    σ (pairVr emb lam 1 x y) = pairK lam (fun _ => 1) (GlobalTheory.CoefSpace.bcVV σ lam x) (GlobalTheory.CoefSpace.bcVV σ lam y) := by
  rw [pairVr, ← GlobalTheory.CoefModel.pairK_mapVV σ _ hσ]
  have h1 : (fun τ => (gramKd emb (1 : Matrix (Fin n) (Fin n) E) τ).map σ) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    simp [gramKd]
  rw [h1]
  rfl

theorem read_iso {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (ok : S.Ok) {G Γ W : Type} [Group G] [Group Γ]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* G} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι (S.toCSD ok) σ ρ J χ) (c : S.V →ₛₗ[σ] W) (d : G → S.D) (u : S.V → W) {s : ℝ} (hs : 0 < s)
    (hc : ∀ v, c v = (s : ℂ) • u v) (hu : ∀ v, inner ℂ (u v) (u v) = σ (S.pair v v))
    (hr : ∀ (φ : S.EqFun) (h : G), P.extL (S.res ok φ) h = c (φ.1 (d h))) (φ : S.EqFun) (h : G) :
    P.extL (S.res ok φ) h = u (φ.1 (d h)) := by
  by_cases hφ : φ = 0
  · have h0 : c (φ.1 (d h)) = 0 := by rw [hφ]; exact map_zero c
    have h1 := hc (φ.1 (d h))
    rw [h0] at h1
    rw [hr, h0]
    exact ((smul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast hs.ne')).symm
  · obtain ⟨v, hv0, hv⟩ := GlobalTheory.Mem.GsdIso.exists_isom_vec S ok ι σ ρ J χ P c d hr ⟨φ, hφ⟩
    rw [hc] at hv0 hv
    rw [hr, hc, scale_eq_one hs hv0 (hv.trans (hu v).symm), Complex.ofReal_one, one_smul]

set_option maxHeartbeats 2000000 in

theorem std_iso {X : Stages} {px : PreX X.B.toPre} {I : Col2.ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B} {Wt : Set X.B.places.Pl}
    (z : Dat X I hX T Wt) (hS : z.Std) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    ∃ e : VV ℂ (X.B.wts.lamV ((i : ℕ) + 1)) ≃ₗ[ℂ] (z.R.cV i).W,
      (∀ x y, inner ℂ (e x) (e y) = pairK (X.B.wts.lamV ((i : ℕ) + 1)) (fun _ => 1) x y) ∧
      (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E)
          (g : GL (Fin X.B.R.nV) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE → MatEq γE g →
        ∀ x, e (rhoK (X.B.wts.lamV ((i : ℕ) + 1)) (invTrK fun τ => Formalism.UG.bc (tauE X.toD7 τ) g) x) =
          (z.R.cV i).coef.ρ γ (e x)) ∧
      ∀ (t : TupU I (usedOf I T Wt)) (ok : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)),
        z.R.B.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res ok φ :))) h =
          e (GlobalTheory.CoefSpace.bcVV X.B.embLL (X.B.wts.lamV ((i : ℕ) + 1)) (φ.1 (LiftBrg.ptL X I (usedOf I T Wt) i t 1 1 h))) := by
  have hh := hS.2 i
  unfold BrgStdV StdSide at hh
  refine hh.elim fun c hh => ?_
  have hint := hh.1
  have hread := hh.2.1
  have hli := hh.2.2.1
  refine hh.2.2.2.elim fun hcm hx => ?_
  have hlab : ∀ τ, X.B.embLL.comp (X.B.fields.emb τ) = tauE X.toD7 τ := fun τ =>
    GlobalTheory.ThetaFiresProbe.labE_fixed (D := X.toD7) τ
  refine (GlobalTheory.Mem.CoefIso.coef_iso X.toD7 (Vc X.toD7 i) X.B.R.nV
    (LiftBrg.rkEq X i).symm hg (z.R.cV i)
    (z.pins.char.base.models.cV i) (K := X.B.fields.K) X.B.embLL X.B.fields.emb
    (X.B.wts.lamV ((i : ℕ) + 1)) c (GlobalTheory.TestLat.SumLat.idx_nonempty _)
    (fun γ γE g h1 h2 v => hint γ γE g h1 h2 v) hli).elim fun e he => he.elim fun s he => ?_
  have hβ : z.R.toLevCh.βV i = 1 := z.lev.beta.1 i
  have hrd : ∀ (t : TupU I (usedOf I T Wt)) (ok : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)),
      z.R.B.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res ok φ :))) h = c (φ.1 (LiftBrg.ptL X I (usedOf I T Wt) i t 1 1 h)) := by
    intro t ok φ h
    refine (hx h).elim fun x hm => ?_
    refine (hread hcm t ⟨⟨ok⟩, φ⟩ h x hm).trans (congrArg (fun d => c (φ.1 d)) ?_)
    have hm' := hm
    rw [hβ] at hm'
    have hx' := LiftBrg.castGL_of_matEq (LiftBrg.rkEq X i).symm _ _ hm'
    rw [Formalism.L2.Col.decoPt_mk]
    unfold LiftBrg.ptL
    refine congrArg (Formalism.L2.Col.decoOf ∅ _) (hx'.trans ?_)
    exact (by with_unfolding_all exact ((cast_one (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (h : GL (Fin (Vc X.toD7 i).rank) _))) :))
  refine ⟨e, he.2.2.1, fun γ γE g h1 h2 x => ?_, fun t ok φ h => ?_⟩
  · have h5 := he.2.2.2 γ γE g h1 h2 x
    have h3 : (fun τ => Formalism.UG.bc (X.B.embLL.comp (X.B.fields.emb τ)) g) = fun τ => Formalism.UG.bc (tauE X.toD7 τ) g :=
      funext fun τ => congrArg (fun a => Formalism.UG.bc a g) (hlab τ)
    have h4 := (congrArg (fun q => e (rhoK (X.B.wts.lamV ((i : ℕ) + 1)) (invTrK q) x)) h3).symm
    exact (by with_unfolding_all exact ((@Eq.trans _ _ _ ((z.R.cV i).coef.ρ γ (e x)) h4 ((by with_unfolding_all exact (h5 :)))) :))
  · exact (by with_unfolding_all exact ((read_iso (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)) ok (G := Bridge.Gf (Vc X.toD7 i)) (Γ := GQ (Vc X.toD7 i)) (W := (z.R.cV i).W)
      (ι := Bridge.ratF (Vc X.toD7 i)) (σ := X.B.embLL) (ρ := (z.R.cV i).coef.ρ) (J := (LiftBrg.envL X I hX (usedOf I T Wt) z.Xg z.tr z.R.toLevCh z.R.cV i t).lev.J) (χ := (LiftBrg.envL X I hX (usedOf I T Wt) z.Xg z.tr z.R.toLevCh z.R.cV i t).lev.χ) ((by with_unfolding_all exact ((z.R.B.L i t).pres :))) c (fun h => LiftBrg.ptL X I (usedOf I T Wt) i t 1 1 h)
      (fun v => e (GlobalTheory.CoefSpace.bcVV X.B.embLL (X.B.wts.lamV ((i : ℕ) + 1)) v)) he.1 he.2.1
      (fun v => (he.2.2.1 _ _).trans (pair_bc X.B.embLL X.B.starLL_cx X.B.fields.emb _ v v).symm) ((by with_unfolding_all exact ((hrd t ok) :))) φ h) :))

set_option maxHeartbeats 4000000 in

theorem rs_coef : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → ∃ (cV' : ∀ i', CoefA (Vc (w'.st Z').toD7 i')) (c0L' : ∀ i' : Fin (w'.st Z').toD7.R.m, VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ) →ₛₗ[(w'.st Z').toD7.what₂.embLL] (cV' i').W),
    (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (cV' i').W (z.R.cV i).W ∧ HEq (cV' i').ρ (z.R.cV i).ρ ∧ HEq (cV' i').nW (z.R.cV i).nW ∧ HEq (cV' i').iW (z.R.cV i).iW) ∧ (∀ i', (cV' i').Is) ∧
    (∀ i', Bridge.CoefMapTie (Vc (w'.st Z').toD7 i') (cV' i').coef (c0L' i') (rhoVr (labLL (w'.st Z').toD7) _)) ∧
    (∀ i' x y, inner ℂ (c0L' i' x) (c0L' i' y) = (w'.st Z').toD7.what₂.embLL (pairVr (labLL (w'.st Z').toD7) _
      (if (w'.st Z').toD7.sp.Vneg ((i' : ℕ) + 1) then -(Vc (w'.st Z').toD7 i').gram else (Vc (w'.st Z').toD7 i').gram) x y)) ∧
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (h : Bridge.Gf (Vc (w.st Z).toD7 i)) (v' : VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ)),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h)).1) →
      HEq (c0L' i' v') (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))) h) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS
  choose e he1 he2 he3 using fun i => std_iso z hS i (GlobalTheory.Mem.R3.BrgRead.gram_V (w.st Z) w.ok.spaces i)
  obtain ⟨hPre, -, -, -⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let cp : ∀ i' : Fin (w'.st Z').toD7.R.m, CoefA (Vc (w'.st Z').toD7 i') := fun i' =>
    @CoefA.mk (w'.st Z').toD7 (Vc (w'.st Z').toD7 i') (z.R.cV ((by with_unfolding_all exact (i' :)))).W (z.R.cV ((by with_unfolding_all exact (i' :)))).nW (z.R.cV ((by with_unfolding_all exact (i' :)))).iW (z.R.cV ((by with_unfolding_all exact (i' :)))).fW
      ((by with_unfolding_all exact ((z.R.cV ((by with_unfolding_all exact (i' :)))).ρ :)))
  have hG := fun i' : Fin (w'.st Z').toD7.R.m => coef_of_iso (D := (w'.st Z').toD7) (Vc (w'.st Z').toD7 i')
    (cp i') (n := B.R.nV) ((by with_unfolding_all exact ((LiftBrg.rkEq (w.st Z) ((by with_unfolding_all exact (i' :)))) :))) ((i' : ℕ) + 1)
    ((by with_unfolding_all exact ((B.wts.lamV ((i' : ℕ) + 1)) :))) ((by with_unfolding_all exact ((GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef (w.st Z) ((by with_unfolding_all exact (i' :)))) :)))
    ((by with_unfolding_all exact ((e ((by with_unfolding_all exact (i' :)))) :))) ((by with_unfolding_all exact ((he1 ((by with_unfolding_all exact (i' :)))) :))) ((by with_unfolding_all exact ((he2 ((by with_unfolding_all exact (i' :)))) :)))
    (if (w'.st Z').toD7.sp.Vneg ((i' : ℕ) + 1) then -(Vc (w'.st Z').toD7 i').gram else (Vc (w'.st Z').toD7 i').gram)
    (by
      rw [GlobalTheory.StdFrame.neg_eq_false_of_posDef _ i' ((by with_unfolding_all exact ((B.V_posDef ((i' : ℕ) + 1) (by omega) ((by with_unfolding_all exact (i'.2 :)))) :)))]
      simp only [Bool.false_eq_true, if_false]
      exact GlobalTheory.Mem.R3.BrgRead.gram_V (w'.st Z') w'.ok.spaces i')
  choose c0 hc1 hc2 hc3 using hG
  refine ⟨cp, c0, ?_, fun i' => (by with_unfolding_all exact ((z.pins.char.base.models.cV ((by with_unfolding_all exact (i' :)))) :)), hc1, hc2, ?_⟩
  · rintro i ⟨i', hi'⟩ hi
    dsimp only at hi
    subst hi
    exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  · rintro i ⟨i', hi'⟩ hi
    dsimp only at hi
    subst hi
    intro ok φ h v' hv
    have h1 := hc3 ⟨i, hi'⟩ v' ((by with_unfolding_all exact ((GlobalTheory.CoefSpace.bcVV B.embLL (B.wts.lamV ((i : ℕ) + 1))
      (φ.1 (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h))) :))) ((by with_unfolding_all exact (hv :)))
    have h2 := he3 i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ok φ h
    exact (by with_unfolding_all exact ((glue (a := c0 ⟨i, hi'⟩ v') h2 ((by with_unfolding_all exact ((heq_of_eq h1) :)))) :))

end GlobalTheory.Mem.RsCoef

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlargedBase_coefficientSpaces_isometric_maps : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → ∃ (cV' : ∀ i', CoefA (Vc (w'.st Z').toD7 i')) (c0L' : ∀ i' : Fin (w'.st Z').toD7.R.m, VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ) →ₛₗ[(w'.st Z').toD7.what₂.embLL] (cV' i').W),
    (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (cV' i').W (z.R.cV i).W ∧ HEq (cV' i').ρ (z.R.cV i).ρ ∧ HEq (cV' i').nW (z.R.cV i).nW ∧ HEq (cV' i').iW (z.R.cV i).iW) ∧ (∀ i', (cV' i').Is) ∧
    (∀ i', Bridge.CoefMapTie (Vc (w'.st Z').toD7 i') (cV' i').coef (c0L' i') (rhoVr (labLL (w'.st Z').toD7) _)) ∧
    (∀ i' x y, inner ℂ (c0L' i' x) (c0L' i' y) = (w'.st Z').toD7.what₂.embLL (pairVr (labLL (w'.st Z').toD7) _
      (if (w'.st Z').toD7.sp.Vneg ((i' : ℕ) + 1) then -(Vc (w'.st Z').toD7 i').gram else (Vc (w'.st Z').toD7 i').gram) x y)) ∧
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (h : Bridge.Gf (Vc (w.st Z).toD7 i)) (v' : VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ)),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h)).1) →
      HEq (c0L' i' v') (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))) h) := by
  atlas_forward_decl GlobalTheory.Mem.RsCoef.rs_coef
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.Mem GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isIdG_unique (X : Stages) {px : PreX X.B.toPre} {Pg : Finset (Pl X.toD7.host.E)} (hPg : Pg = (X.B.primes px).vGs)
    {eG eG' : Gc X.B px ≃* G0 Pg X.toD7.R.r} (h : IsPlacewiseIdentity X (px := px) eG) (h' : IsPlacewiseIdentity X (px := px) eG') : eG = eG' := by
  subst hPg
  exact MulEquiv.ext fun g => funext fun P => (h g P.1 P.2 P.2).trans (h' g P.1 P.2 P.2).symm

theorem isStdChar_unique {D : D7} {ψ ψ' : AddChar (AF D.host.F) ℂ} {s : ℤ} (h : IsStdChar D ψ s) (h' : IsStdChar D ψ' s) :
    ψ = ψ' := by
  obtain ⟨θ, hθ⟩ := h.2.1
  exact GlobalTheory.StdAdelicChar.eq_of_psiInf_eq h.1 h'.1 fun x => (h.2.2 θ hθ x).trans (h'.2.2 θ hθ x).symm

theorem isInfFam_unique {D : D7} {θ θ' : Formalism.IndefR.Datum.InfFam D} (h : IsInfFam θ) (h' : IsInfFam θ') : θ = θ' :=
  Formalism.IndefR.Eqv.infFamUnique_holds D θ θ' h h'


open Formalism.IndefR.Mult in

theorem parAt_enl (X X' : Stages) (hB : X'.B.toPre = X.B.toPre) (ι : X.toD7.what₂.LL →+* X'.toD7.what₂.LL)
    (hι : ∀ x, X'.toD7.what₂.embLL (ι x) = X.toD7.what₂.embLL x) (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (σ' : X'.toD7.what₂.LL →+* ℂ) : HEq (parAt (Wc X'.toD7 i') σ') (parAt (Wc X.toD7 i) (σ'.comp ι)) := by
  obtain ⟨⟨P, LL, eL, _, eE, eφ⟩, C, W, V, S, N, G⟩ := X
  obtain ⟨⟨P', LL', eL', _, eE', eφ'⟩, C', W', V', S', N', G'⟩ := X'
  dsimp only at hB
  subst hB
  obtain ⟨i, hi0⟩ := i
  obtain ⟨i', hi1⟩ := i'
  dsimp only at hi
  subst hi
  have hE : ∀ x, ι (eE x) = eE' x := fun x => by
    apply eL'.injective
    have h1 := congrArg (fun f => f x) eφ
    have h2 := congrArg (fun f => f x) eφ'
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 h2
    exact (hι (eE x)).trans (h1.trans h2.symm)
  apply heq_of_eq
  funext ρ
  have hc : ∀ τ, labE σ' τ = labE (σ'.comp ι) τ := fun τ => by
    ext x
    simp only [labE, labLL, RingHom.coe_comp, Function.comp_apply]
    exact congrArg σ' (hE _).symm
  have hl : labE σ' = labE (σ'.comp ι) := funext hc
  unfold parAt kapAt lab
  erw [hl]
  rfl

end GlobalTheory.Mem.R3.Rw

end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.RsA
open Formalism.IndefR.Mult Formalism.IndefR.Datum

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def newL (L : Formalism.IndefR.Links.LevCh D T) (ΛY : type_of% L.ΛY) (ΛV : type_of% L.ΛV) (ΛW : type_of% L.ΛW) (βY : type_of% L.βY) (βW : type_of% L.βW) :
    Formalism.IndefR.Links.LevCh D T := { L with ΛY := ΛY, ΛV := ΛV, ΛW := ΛW, βY := βY, βW := βW }

def newR (R : RealDat3 D A3 Ks) (L : Formalism.IndefR.Links.LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i))
    (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT R.MX →ₗ[ℂ] ℂ) : RealDat3 D A3 Ks :=
  { toRealDat :=
    { toLevCh := L
      hv0 := R.hv0
      eG := eG
      pl := pl
      Sb := Sb
      θ := R.θ
      ψ := R.ψ
      MY := R.MY
      MX := R.MX
      MW := R.MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := R.mu
      twPl := R.twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
    plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }

theorem newR_clauses (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (ΛY : type_of% R.ΛY) (ΛV : type_of% R.ΛV) (ΛW : type_of% R.ΛW) (βY : type_of% R.βY) (βW : type_of% R.βW)
    (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i))
    (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 (newL R.toLevCh ΛY ΛV ΛW βY βW) cX cV pl) (plI : I0 → Pl D.host.E)
    (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT R.MX →ₗ[ℂ] ℂ)
    (hL : (newL R.toLevCh ΛY ΛV ΛW βY βW).Is A3.A.μ0) (h0 : R.toRealDat.Pre0 F.lv2) (ht : R.IsTup) (hk : Keep R.toRealDat F.lv2 cG)
    (hfr : Seed.Frm.FramesExistDiagonal D R.Pg → Seed.Frm.NormalFrameConditionsDiagonal R.Pg βY βW)
    (hcX : cX.Is) (hcV : ∀ i, (cV i).Is) (hpr : IsDualPair R.θ R.MX cX prX) (hPr : Seed.PrIso R.MX cX prX)
    (hb : Seed.BrgL A3 (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF) :
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).toRealDat.Pre0 F.lv2 ∧
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).IsInert ∧
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).IsTup ∧
    (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).AllPlaces ∧
    Keep (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb B plI SF prX).toRealDat F.lv2 cG := by
  have hsub : R.Pg ⊆ Sb := by rw [hb.sb]; exact Finset.Subset.refl _
  refine ⟨⟨hL, hb.red_R, hb.red_L, h0.levels, h0.record, ⟨hb.tie, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, h0.inf, h0.vpos, hcX, hcV, hpr, h0.order, h0.std⟩, ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩,
      ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, hb.sb, ⟨h0.std, ?_, hfr, hk.beta, hPr, hk.grp, hk.psi, hk.guard, hk.valKs, hk.frameKs, hk.levKs⟩⟩
  refine hk.grp.elim fun plg h => h.elim fun iso h => ?_
  exact GlobalTheory.SignsAtTypePrimes.signsAtG _ _ _ _ _ _ _ _ cG h0.std hk.psi ⟨plg, iso, h.1, h.2.2.1, h.2.2.2⟩

theorem vv_cast_map {K : Type} [Field K] {ι : Type} [Fintype ι] {n n' : ℕ} (h : n = n') (lam : ι → DomWeight n) (lam' : ι → DomWeight n')
    (hl : ∀ τ a, (lam τ).w a = (lam' τ).w (Fin.cast h a)) (σ : K →+* ℂ) (v : VV K lam) :
    ∃ v' : VV K lam', HEq v' v ∧ HEq (MvPolynomial.map σ v'.1) (MvPolynomial.map σ v.1) := by
  subst h
  have hlam : lam = lam' := by
    funext τ
    have h1 := hl τ
    rcases hw : lam τ with ⟨w, hw1⟩
    rcases hw' : lam' τ with ⟨w', hw1'⟩
    rw [hw, hw'] at h1
    have : w = w' := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hlam
  exact ⟨v, HEq.rfl, HEq.rfl⟩

set_option maxHeartbeats 2000000 in

theorem stage {B' : Base} {f' : Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z' : w'.Lt} {hX' : B'.fields.Ok} {Wt' : Set B'.places.Pl}
    (hV : ∀ i, Seed.FrmC.StdLat (Vc (w'.st Z').toD7 i)) (hXl : Seed.FrmC.StdLat (w'.st Z').toD7.sp.X') (hval : ValsIn w'.I)
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd) (hK : Kept T' w' Z' hX' Wt' R cG)
    (ΛY : type_of% R.ΛY) (ΛV : type_of% R.ΛV) (ΛW : type_of% R.ΛW) (βY : type_of% R.βY) (βW : type_of% R.βW)
    (hY : ∀ j, j < (w'.st Z').toD7.R.m → IsSDFrame (Yc (w'.st Z').toD7 j) (βY j) (ΛY j) ((w'.st Z').toD7.host.g 0 * (w'.st Z').toD7.host.g 1))
    (hV' : ∀ i, IsSDFrame (Vc (w'.st Z').toD7 i) (R.βV i) (ΛV i) 1) (hW : ∀ i, IsSDFrame (Wc (w'.st Z').toD7 i) (βW i) (ΛW i) 1)
    (hfr : Seed.Frm.FramesExistDiagonal (w'.st Z').toD7 R.Pg → Seed.Frm.NormalFrameConditionsDiagonal R.Pg βY βW)
    (cV : ∀ i, CoefA (Vc (w'.st Z').toD7 i))
    (c0L : ∀ i : Fin (w'.st Z').toD7.R.m, VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i).rank ((i : ℕ) + 1) τ) →ₛₗ[(w'.st Z').toD7.what₂.embLL] (cV i).W)
    (h1 : ∀ i, (cV i).Is) (h2 : ∀ i, Bridge.CoefMapTie (Vc (w'.st Z').toD7 i) (cV i).coef (c0L i) (rhoVr (labLL (w'.st Z').toD7) _))
    (h3 : ∀ i x y, inner ℂ (c0L i x) (c0L i y) = (w'.st Z').toD7.what₂.embLL (pairVr (labLL (w'.st Z').toD7) _
      (if (w'.st Z').toD7.sp.Vneg ((i : ℕ) + 1) then -(Vc (w'.st Z').toD7 i).gram else (Vc (w'.st Z').toD7 i).gram) x y)) :
    ∃ (cX : _) (pl : _) (Sb : _) (Bd : _) (plI : _) (SF : _) (prX : _),
      Kept T' w' Z' hX' Wt' (newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb Bd plI SF prX) cG ∧ Sb = R.Pg ∧
      ∀ (i : Fin (w'.st Z').toD7.R.m) (t : TupU w'.I (usedOf w'.I T' Wt'))
        (ok : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel t.1 ((i : ℕ) + 1)).Ok)
        (φ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc (w'.st Z').toD7 i)),
        ∃ v', Bd.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel t.1 ((i : ℕ) + 1)).res ok φ :))) h = c0L i v' ∧
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1)
            (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ.1 (LiftBrg.ptL (w'.st Z') w'.I (usedOf w'.I T' Wt') i t 1 1 h)).1) := by
  have hLev := hK.1
  have h4 := hLev.is
  have hL1 : LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') (newL R.toLevCh ΛY ΛV ΛW βY βW) :=
    ⟨⟨h4.mu0, h4.eta, h4.xi, h4.xi_inj, h4.xi_base, h4.xi_fin, h4.xi_triv, h4.xi_tame, h4.Pg, h4.Q_pl,
      h4.Q_off, h4.Q_de, h4.Q_ram, h4.chi, h4.xiR, hY, h4.βX, hV', hW⟩, hLev.C, hLev.xiH, hLev.Pg, hLev.Q, hLev.beta⟩
  have h0 := hK.2.2.2.2.2.1
  refine (GlobalTheory.T.exists_adelicReading_definiteForms_given_coefficients (w'.st Z') w'.px w'.I hX' (usedOf w'.I T' Wt') Xg tr (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG w'.ok hval hL1 hK.2.1
    hLev.beta.2 hLev.beta.1 hXl hV R.θ h0.inf R.MX cV c0L h1 h2 h3).elim fun cX h => h.elim fun pl h => h.elim fun Sb h =>
      h.elim fun Bd h => h.elim fun plI h => h.elim fun SF h => h.elim fun prX h => ?_
  have hc := newR_clauses R (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG ΛY ΛV ΛW βY βW cX cV pl Sb Bd plI SF prX hL1.is h0
    hK.2.2.2.2.2.2.2.1 hK.2.2.2.2.2.2.2.2.2.1 hfr h.1 h1 h.2.1 h.2.2.1 h.2.2.2.1
  refine ⟨cX, pl, Sb, Bd, plI, SF, prX, ⟨hL1, hK.2.1, hK.2.2.1, hK.2.2.2.1, hK.2.2.2.2.1, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2,
    h.2.2.2.2.1, h.2.2.2.2.2.1⟩, h.2.2.2.1.sb, fun i t ok φ g => ?_⟩
  refine (vv_cast_map (LiftBrg.rkEq (w'.st Z') i) (B'.wts.lamV ((i : ℕ) + 1))
      (fun τ => Bridge.lamLdef (D := (w'.st Z').toD7) (Vc (w'.st Z').toD7 i).rank ((i : ℕ) + 1) τ) (GlobalTheory.T.baseWeight_eq_forcedLiftWeight (w'.st Z') i) B'.embLL
      (φ.1 (LiftBrg.ptL (w'.st Z') w'.I (usedOf w'.I T' Wt') i t 1 1 g))).elim fun v' hv => ?_
  exact ⟨v', h.2.2.2.2.2.2 i t φ g v' hv.1, hv.2⟩

theorem decoOf_heq {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E] {n : ℕ} [NeZero n]
    {S S' : Finset (HeightOneSpectrum (𝓞 E))} (h : S' = S) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    HEq (Formalism.L2.Col.decoOf ∅ S' x) (Formalism.L2.Col.decoOf ∅ S x) := by
  subst h
  rfl

set_option maxHeartbeats 2000000 in

theorem ptL_enl {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
    (Z : w.Lt) (Z' : w'.Lt) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl) (hPre : B'.toPre = B.toPre) (hp : HEq w'.px w.px)
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    (↥(Bridge.Gf (Vc (w'.st Z').toD7 i')) = ↥(Bridge.Gf (Vc (w.st Z).toD7 i))) ∧
    ∀ (h' : Bridge.Gf (Vc (w'.st Z').toD7 i')) (h : Bridge.Gf (Vc (w.st Z).toD7 i)), HEq h' h →
      HEq (LiftBrg.ptL (w'.st Z') w'.I (usedOf w'.I T' Wt') i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) 1 1 h')
        (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h) := by
  have s1 := rowLevelPrimes_colTuples_eq_vGs w Wt
  have s2 := rowLevelPrimes_colTuples_eq_vGs w' Wt'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  have hp' : w'.px = w.px := eq_of_heq hp
  have hv : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [hp']
    rfl
  obtain ⟨i, hi0⟩ := i
  obtain ⟨i', hi1⟩ := i'
  dsimp only at hi
  subst hi
  refine ⟨(@rfl Type ↥(@Bridge.Gf (@ColW.st B f T w Z).toD7 (Vc (@ColW.st B f T w Z).toD7 (@Fin.mk (@ColW.st B f T w Z).toD7.R.m i hi0)))), fun h' h e => ?_⟩
  have e' : h' = (h) := eq_of_heq ((e))
  rw [e']
  have hs := s2.trans (hv.trans s1.symm)
  exact (by with_unfolding_all exact ((decoOf_heq (F := B.host.F) hs (((1 : GL (Fin (w.st Z).B.R.nV) (LiftBrg.EA (w.st Z)))⁻¹ * LiftBrg.castGL (LiftBrg.rkEq (w.st Z) ⟨i, hi0⟩).symm
    (Formalism.UG.bc (swapAE (w.st Z).toD7) (h : GL (Fin (Vc (w.st Z).toD7 ⟨i, hi0⟩).rank) _)) * 1 * 1))) :))

set_option maxHeartbeats 2000000 in

theorem frames_enl {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} (w' : ColW B' f' T')
    {Z : w.Lt} (Z' : w'.Lt) {hX : B.fields.Ok} {Wt : Set B.places.Pl} (z : Dat (w.st Z) w.I hX T Wt)
    (hPre : B'.toPre = B.toPre) (hf : HEq f' f) (hp : HEq w'.px w.px) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 (w'.st Z').toD7.host.E) (Fin (Yc (w'.st Z').toD7 j).rank → (w'.st Z').toD7.host.E))
      (ΛV : ∀ j, Submodule (𝓞 (w'.st Z').toD7.host.E) (Fin (Vc (w'.st Z').toD7 j).rank → (w'.st Z').toD7.host.E))
      (ΛW : ∀ j, Submodule (𝓞 (w'.st Z').toD7.host.E) (Fin (Wc (w'.st Z').toD7 j).rank → (w'.st Z').toD7.host.E))
      (βY : ∀ j, GL (Fin (Yc (w'.st Z').toD7 j).rank) (Datum.EAf (w'.st Z').toD7))
      (βW : ∀ j, GL (Fin (Wc (w'.st Z').toD7 j).rank) (Datum.EAf (w'.st Z').toD7)),
      (HEq ΛY z.R.ΛY ∧ HEq ΛV z.R.ΛV ∧ HEq ΛW z.R.ΛW ∧ HEq βY z.R.βY ∧ HEq βW z.R.βW) ∧
      (∀ j, j < (w'.st Z').toD7.R.m → IsSDFrame (Yc (w'.st Z').toD7 j) (βY j) (ΛY j) ((w'.st Z').toD7.host.g 0 * (w'.st Z').toD7.host.g 1)) ∧
      (∀ i, IsSDFrame (Vc (w'.st Z').toD7 i) 1 (ΛV i) 1) ∧ (∀ i, IsSDFrame (Wc (w'.st Z').toD7 i) (βW i) (ΛW i) 1) ∧
      (∀ Pg : Finset (Pl (w'.st Z').toD7.host.E), Pg = (B'.primes w'.px).vGs →
        (Seed.Frm.FramesExistDiagonal (w'.st Z').toD7 Pg → Seed.Frm.NormalFrameConditionsDiagonal Pg βY βW) ∧ HEq Pg z.R.Pg ∧ HEq Pg z.R.Sb ∧
        ∀ eG : Gc B' w'.px ≃* G0 Pg (w'.st Z').toD7.R.r, IsPlacewiseIdentity (w'.st Z') (px := w'.px) eG → HEq eG z.R.eG) ∧
      (∀ ψ, IsStdChar (w'.st Z').toD7 ψ (-1) → HEq ψ z.R.ψ) ∧ (∀ θ : InfFam (w'.st Z').toD7, IsInfFam θ → HEq θ z.R.θ) ∧
      ∀ βV : ∀ j, GL (Fin (Vc (w'.st Z').toD7 j).rank) (Datum.EAf (w'.st Z').toD7), (∀ j, βV j = 1) → HEq βV z.R.βV := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  have hV : ∀ i, IsSDFrame (Vc (w.st Z).toD7 i) 1 (z.R.ΛV i) 1 := fun i => by
    have := z.lev.is.βV i
    rw [z.lev.beta.1 i] at this
    exact this
  have hall : z.R.Sb = z.R.Pg := z.pins.char.allPl
  refine ⟨(z.R.ΛY), (z.R.ΛV), (z.R.ΛW), (z.R.βY), (z.R.βW),
    ⟨(HEq.refl z.R.ΛY), (HEq.refl z.R.ΛV), (HEq.refl z.R.ΛW), (HEq.refl z.R.βY),
      (HEq.refl z.R.βW)⟩, (z.lev.is.βY), (hV), (z.lev.is.βW), fun Pg hPg => ?_, fun ψ hψ => ?_,
      fun θ hθ => ?_, fun βV hβ => ?_⟩
  · have e : Pg = (z.R.Pg) := hPg.trans ((by with_unfolding_all exact (z.lev.Pg.symm :)))
    subst e
    refine ⟨by kexactB z.pins.keep.frames, (HEq.refl z.R.Pg), (by with_unfolding_all exact ((heq_of_eq hall.symm) :)), fun eG hG => ?_⟩
    exact (by with_unfolding_all exact ((heq_of_eq (isIdG_unique (w.st Z) (px := w.px) z.lev.Pg (eG := (by with_unfolding_all exact (eG :))) ((by with_unfolding_all exact (hG :))) z.idG)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (isStdChar_unique (D := (w.st Z).toD7) (ψ := (by with_unfolding_all exact (ψ :))) ((by with_unfolding_all exact (hψ :))) z.pins.keep.std)) :))
  · exact (by with_unfolding_all exact ((heq_of_eq (isInfFam_unique (D := (w.st Z).toD7) (θ := (by with_unfolding_all exact (θ :))) ((by with_unfolding_all exact (hθ :))) z.pins.char.base.models.inf)) :))
  · have e : ((βV) : type_of% z.R.βV) = z.R.βV := funext fun j => Eq.trans ((hβ j)) (z.lev.beta.1 j).symm
    exact (by with_unfolding_all exact ((heq_of_eq e) :))

set_option maxHeartbeats 4000000 in

theorem reset_side : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → (∀ i, Seed.FrmC.StdLat (Vc (w'.st Z').toD7 i)) → Seed.FrmC.StdLat (w'.st Z').toD7.sp.X' → ValsIn w'.I →
    ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideA z Wt' R₁ := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS hV hXl hval Ks _ _ _ Xg tr R cG hK
  refine (GlobalTheory.T.enlargedBase_coefficientSpaces_isometric_maps (w' := w') (Z' := Z') (hX' := hX') (Wt' := Wt') z hE hf hp hS).elim fun cV h => h.elim fun c0L hc => ?_
  refine (frames_enl w' Z' z hE.1 hf hp).elim fun ΛY h => h.elim fun ΛV h => h.elim fun ΛW h => h.elim fun βY h => h.elim fun βW hF => ?_
  have hPg := hF.2.2.2.2.1 R.Pg hK.1.Pg
  refine (stage hV hXl hval R cG hK ΛY ΛV ΛW βY βW hF.2.1 (fun i => (hK.1.beta.1 i).symm ▸ hF.2.2.1 i) hF.2.2.2.1 hPg.1 cV c0L
    hc.2.1 hc.2.2.1 hc.2.2.2.1).elim fun cX h => h.elim fun pl h => h.elim fun Sb h =>
      h.elim fun Bd h => h.elim fun plI h => h.elim fun SF h => h.elim fun prX h => ?_
  refine ⟨newR R (newL R.toLevCh ΛY ΛV ΛW βY βW) R.eG cX cV pl Sb Bd plI SF prX, cG, h.1,
    hF.2.2.2.2.2.1 R.ψ hK.2.2.2.2.2.1.std, hF.2.2.2.2.2.2.1 R.θ hK.2.2.2.2.2.1.inf, hF.1.2.2.2.2, hF.1.2.2.2.1, hF.1.1,
    hF.2.2.2.2.2.2.2 R.βV hK.1.beta.1, hF.1.2.1, hF.1.2.2.1, hPg.2.1, hPg.2.2.2 R.eG hK.2.1, (heq_of_eq h.2.1).trans hPg.2.2.1,
    hc.1, fun i i' hi ok ok' φ φ' hφ => ?_⟩
  have hpt := ptL_enl w w' Z Z' Wt Wt' hE.1 hp i i' hi
  refine Function.hfunext hpt.1 fun g' g e => ?_
  refine (h.2.2 i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ok' φ' g').elim fun v' hv => ?_
  exact (heq_of_eq hv.1).trans (hc.2.2.2.2 i i' hi ok φ g v' (hv.2.trans (hφ _ _ (hpt.2 g' g e))))

end GlobalTheory.Mem.R3.RsA
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteFormsReading_reset_baseEnlargement : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → (∀ i, Seed.FrmC.StdLat (Vc (w'.st Z').toD7 i)) → Seed.FrmC.StdLat (w'.st Z').toD7.sp.X' → ValsIn w'.I →
    ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideA z Wt' R₁ := by
  atlas_forward_decl GlobalTheory.Mem.R3.RsA.reset_side
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory

theorem formsL_exists_baseChange_coordinates : ∀ {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L] [Algebra Ks L'] (ι : L →+* L'), (∀ y : Ks, ι (algebraMap Ks L y) = algebraMap Ks L' y) → ∀ (n : ℕ) (W : (L →+* ℂ) → Type) [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] (G : Type) [Group G] (F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G),
  ∃ F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G,
    (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
    (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
    (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
    (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
    F'.Pt = F.Pt ∧
    ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) → F'.nrm lp y' φ' = F.nrm lp y φ := by
  intro L L' Ks _ _ _ _ _ _ _ _ ι hι n W _ _ G _ F
  let m : (Fin n → L) →ₗ[Ks] (Fin n → L') :=
    { toFun := fun x k => ι (x k)
      map_add' := fun x y => by funext k; simp
      map_smul' := fun c x => by
        funext k
        simp only [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, map_mul, hι] }
  have minj : Function.Injective m := by
    intro x y h
    funext k
    exact ι.injective (congrFun h k)
  let e := Submodule.equivMapOfInjective m minj F.WK
  let ρ' : G →* ((Fin n → L') →ₗ[L'] (Fin n → L')) :=
    (Matrix.toLinAlgEquiv' (R := L') (n := Fin n)).toMonoidHom.comp
      ((ι.mapMatrix (m := Fin n)).toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv' (R := L) (n := Fin n)).toMonoidHom.comp F.ρ))
  let j' : ∀ σ' : L' →+* ℂ, (Fin n → L') →ₛₗ[σ'] W (σ'.comp ι) := fun σ' =>
    { toFun := fun x' => ∑ k, σ' (x' k) • F.j (σ'.comp ι) (Pi.single k 1)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  let F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G :=
    { WK := F.WK.map m
      Pt := F.Pt
      nrm := fun lp y φ' => F.nrm lp y (e.symm φ')
      nrm_nonneg := fun lp y f => F.nrm_nonneg lp y _
      nrm_zero := fun lp y => by simp only [map_zero]; exact F.nrm_zero lp y
      nrm_add := fun lp y f g => by simp only [map_add]; exact F.nrm_add lp y _ _
      nrm_smul := fun lp y a f => by simp only [map_smul]; exact F.nrm_smul lp y a _
      towKs := inferInstance
      ρ := ρ'
      chi := (Units.map ι.toMonoidHom).comp F.chi
      j := j' }
  refine ⟨F', ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro σ' x
    have hx : x = ∑ k, x k • (Pi.single k 1 : Fin n → L) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    show ∑ k, σ' (ι (x k)) • F.j (σ'.comp ι) (Pi.single k 1) = F.j (σ'.comp ι) x
    conv_rhs => rw [hx]
    simp only [map_sum, map_smulₛₗ, RingHom.comp_apply]
  · intro x'
    show x' ∈ F.WK.map m ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · intro g; rfl
  · intro g x
    show Matrix.toLin' ((LinearMap.toMatrix' (F.ρ g)).map ι) (fun k => ι (x k)) = _
    funext k
    rw [Matrix.toLin'_apply]
    have := RingHom.map_mulVec ι (LinearMap.toMatrix' (F.ρ g)) x k
    rw [LinearMap.toMatrix'_mulVec] at this
    exact this.symm
  · intro lp y' y hy φ' φ hφ
    have hyy : y' = y := eq_of_heq hy
    subst hyy
    show F.nrm lp y' (e.symm φ') = F.nrm lp y' φ
    have : φ' = e φ := Subtype.ext hφ
    rw [this, LinearEquiv.symm_apply_apply]

end GlobalTheory
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw

def labEE {D : D7} (e : D.host.E →+* ℂ) (τ : D.what₂.Tau) : D.host.E →+* ℂ :=
  e.comp (D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)

open Classical in

def labX {D : D7} (e : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : D.what₂.Tau :=
  if h : ∃ τ, labEE e τ = tauE D ρ ∨ labEE e τ = (starRingEnd ℂ).comp (tauE D ρ) then h.choose else ρ

open Classical in

def parAtE {D : D7} (W : HSp D) (e : D.host.E →+* ℂ) (ρ : D.what₂.Tau) : SPar :=
  if labEE e (labX e ρ) = tauE D ρ then
    Formalism.L2.NTheta.holPar (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 (Formalism.L2.NTheta.kapW (D.hc (labX e ρ)) _ _)
  else Formalism.IndefR.Mult.dualPar
    (Formalism.L2.NTheta.holPar (W.sig (tauE D ρ)).1 (W.sig (tauE D ρ)).2 (Formalism.L2.NTheta.kapW (D.hc (labX e ρ)) _ _))

theorem parAt_eq_parAtE {D : D7} (W : HSp D) (σ : D.what₂.LL →+* ℂ) : parAt W σ = parAtE W (σ.comp D.embE) := rfl

theorem exists_heq_io {L : Type} (F : L → Type) [∀ a, AddCommGroup (F a)] [∀ a, Module ℂ (F a)] {P : Type} [AddCommGroup P]
    [Module ℂ P] {a b : L} (hab : a = b) {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W]
    [nW' : NormedAddCommGroup W'] [iW' : InnerProductSpace ℂ W'] (h1 : W' = W) (h2 : HEq nW' nW) (h3 : HEq iW' iW)
    (f : F b →ₗ[ℂ] W →ₗ[ℂ] P) : ∃ f' : F a →ₗ[ℂ] W' →ₗ[ℂ] P, HEq f' f := by
  subst hab h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  exact ⟨f, HEq.rfl⟩

theorem forms_crdOver {L L' Ks : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Field Ks] [NumberField Ks] [Algebra Ks L]
    [Algebra Ks L'] {ι ι₂ : L →+* L'} (hι : ι₂ = ι) {n : ℕ} {W : (L →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)]
    [∀ σ, InnerProductSpace ℂ (W σ)] {G : Type} [Group G] {F : Formalism.IndefR.Arith.FormsL L Ks (Fin n → L) W G}
    {F' : Formalism.IndefR.Arith.FormsL L' Ks (Fin n → L') (fun σ' => W (σ'.comp ι)) G}
    (h : (∀ (σ' : L' →+* ℂ) (x : Fin n → L), F'.j σ' (fun k => ι (x k)) = F.j (σ'.comp ι) x) ∧
      (∀ x' : Fin n → L', x' ∈ F'.WK ↔ ∃ x ∈ F.WK, x' = fun k => ι (x k)) ∧
      (∀ g, ((F'.chi g : L'ˣ) : L') = ι ((F.chi g : Lˣ) : L)) ∧
      (∀ g (x : Fin n → L), F'.ρ g (fun k => ι (x k)) = fun k => ι (F.ρ g x k)) ∧
      F'.Pt = F.Pt ∧
      ∀ lp (y' : F'.Pt lp) (y : F.Pt lp), HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), (φ'.1 = fun k => ι (φ.1 k)) →
        F'.nrm lp y' φ' = F.nrm lp y φ) :
    (∀ (σ' : L' →+* ℂ) x x', CrdOver ι₂ x x' → HEq (F'.j σ' x') (F.j (σ'.comp ι₂) x)) ∧
      ((∀ x x', CrdOver ι₂ x x' → (x' ∈ F'.WK ↔ x ∈ F.WK)) ∧ ∀ x' ∈ F'.WK, ∃ x : Fin n → L, CrdOver ι₂ x x') ∧
      (∀ g' g, HEq g' g → ((F'.chi g' : L'ˣ) : L') = ι₂ ((F.chi g : Lˣ) : L)) ∧
      (∀ g' g, HEq g' g → ∀ x x', CrdOver ι₂ x x' → CrdOver ι₂ (F.ρ g x) (F'.ρ g' x')) ∧
      HEq F'.Pt F.Pt ∧
      (∀ lp' lp, HEq lp' lp → ∀ y' y, HEq y' y → ∀ (φ' : F'.WK) (φ : F.WK), CrdOver ι₂ φ.1 φ'.1 →
        F'.nrm lp' y' φ' = F.nrm lp y φ) := by
  subst hι
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hc : ∀ (x : Fin n → L) (x' : Fin n → L'), CrdOver ι₂ x x' ↔ x' = fun k => ι₂ (x k) := fun x x' =>
    ⟨fun hx => funext fun k => hx.2 k k rfl, fun hx => ⟨rfl, fun k k' e => by rw [hx, Fin.ext e]⟩⟩
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, heq_of_eq h5, ?_⟩
  · intro σ' x x' hx
    rw [(hc _ _).1 hx, h1]
  · intro x x' hx
    rw [(hc _ _).1 hx, h2]
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain rfl : x = y := funext fun k => ι₂.injective (congrFun hyx k)
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  · intro x' hx'
    obtain ⟨x, -, e⟩ := (h2 x').1 hx'
    exact ⟨x, (hc _ _).2 e⟩
  · intro g' g e
    obtain rfl := eq_of_heq e
    exact h3 g'
  · intro g' g e x x' hx
    obtain rfl := eq_of_heq e
    rw [hc, (hc _ _).1 hx, h4]
  · intro lp' lp e y' y ey φ' φ hx
    obtain rfl := eq_of_heq e
    exact h6 lp' y' y ey φ' φ ((hc _ _).1 hx)

set_option maxHeartbeats 4000000 in

theorem resetW : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
    (∀ y : core'.Q.c.F, B'.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) = (y : ℂ)) →
    HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG → RSideA z Wt' R →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideW z Wt' R₁ := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp core' alg' halg eH el ec Xg tr R cG hK hA
  obtain ⟨hPre, -, -, hLL⟩ := hE
  have hι := enlEmb_spec hLL
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := core'
  dsimp only at eH el ec
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  set D := (w.st Z).toD7 with hD
  set D' := (ColW.st _ Z').toD7 with hD'
  set ι := enlEmb hLL with hιdef
  have hιc : D'.what₂.embLL.comp ι = D.what₂.embLL := RingHom.ext hι
  have hE' : D'.embE = ι.comp D.embE := by
    ext x
    apply D'.what₂.embLL.injective
    have h1 := RingHom.congr_fun D'.embE_φ₀ x
    have h2 := RingHom.congr_fun D.embE_φ₀ x
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    exact (h1.trans h2.symm).trans (hι _).symm
  have hpar : ∀ (i : Fin D.R.m) (σ' : D'.what₂.LL →+* ℂ), parAt (Wc D' i) σ' = parAt (Wc D i) (σ'.comp ι) := by
    intro i σ'
    rw [parAt_eq_parAtE, parAt_eq_parAtE, hE']
    rfl

  let MW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), Mult.DSModel (Wc D' i) (parAt (Wc D' i) σ') := fun i σ' =>
    { z.R.MW i (σ'.comp ι) with enum := fun τ => by rw [hpar i σ']; exact (z.R.MW i (σ'.comp ι)).enum τ }
  let HW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), HMod (Mult.MMap (MW' i σ')) := fun i σ' => z.R.HW i (σ'.comp ι)
  let gW' : ∀ (i : Fin D'.R.m) (σ' : D'.what₂.LL →+* ℂ), Representation ℂ (Gc B w.px) (HW' i σ').H := fun i σ' => z.R.gW i (σ'.comp ι)
  have hs0' := sgAt_mk _ R.hv0
  have hs0 := sgAt_mk _ z.R.hv0
  have hs := (congrArg (fun s => RingHom.comp s ι) hs0').trans (hιc.trans hs0.symm)
  have hA0 := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hcV, hjL⟩ := hA
  have hio := fun i : Fin D.R.m =>
    exists_heq_io (fun σ => LowT (z.R.MW i σ)) hs (eq_of_heq (hcV i i rfl).1) (hcV i i rfl).2.2.1 (hcV i i rfl).2.2.2 (z.R.ioP i)
  choose ioP' hioP using hio
  letI := z.alg
  have halgι : ∀ y : z.core.Q.c.F, ι (algebraMap z.core.Q.c.F D.what₂.LL y) = algebraMap z.core.Q.c.F D'.what₂.LL y := by
    intro y
    apply D'.what₂.embLL.injective
    exact (hι _).trans ((z.alg_eq y).trans (halg y).symm)
  have hfw := fun i : Fin D.R.m => GlobalTheory.formsL_exists_baseChange_coordinates (L := D.what₂.LL) (L' := D'.what₂.LL) ι halgι (z.R.nW i) (fun σ => (z.R.HW i σ).H) _ (z.R.FW i)
  choose FW' hFW using hfw
  let R₁ : RealDat3 D' _ z.core.Q.c.F :=
    { R with
      MW := MW'
      HW := HW'
      gW := gW'
      νW := (fun i => z.R.νW i)
      fdW := (fun i => z.R.fdW i)
      vacP := (fun i => z.R.vacP i)
      BV := (fun i => z.R.BV i)
      ioP := ioP'
      nW := z.R.nW
      FW := FW'
      thF := (fun _ _ => 0)
      thG := (fun _ _ => 0) }
  refine ⟨R₁, cG, ?_, ?_⟩
  · obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := hK
    have f6 := k6.fam
    refine ⟨k1, k2, k3, k4, k5,
      { k6 with fam := ⟨f6.tie, f6.Sb, f6.roots, f6.pl_onto, f6.degR, f6.degL, f6.muVal, f6.etaVal⟩, order := ?hord },
      ⟨k7.tie, k7.onto, k7.hR, k7.hL, k7.SF⟩, ⟨k8.mu_off, k8.mu_used, k8.mu_ne, k8.mu_conj, k8.mu_on⟩, k9,
      { k10 with frameKs := ⟨?hfk1, ?hfk2⟩ }, k11⟩
    case hord =>
      intro i τ a
      have e := z.pins.char.base.models.order i τ a
      exact (congrArg (fun s => (z.R.MW i s).ε τ a) hs).trans e
    case hfk1 =>
      intro i σ σ' h ρ
      have h' : (σ.comp ι).comp (algebraMap z.core.Q.c.F D.what₂.LL) = (σ'.comp ι).comp (algebraMap z.core.Q.c.F D.what₂.LL) := by
        ext y
        have := RingHom.congr_fun h y
        show σ (ι (algebraMap _ D.what₂.LL y)) = σ' (ι (algebraMap _ D.what₂.LL y))
        rw [halgι]
        exact this
      exact z.pins.keep.frameKs.1 i (σ.comp ι) (σ'.comp ι) h' ρ
    case hfk2 =>
      intro i σ h τ a
      have h'' : ∀ ρ, labE (σ.comp ι) (lab (σ.comp ι) ρ) = tauE D ρ := by
        intro ρ
        have e : labEE (D := D') (σ.comp D'.embE) (labX (D := D') (σ.comp D'.embE) ρ) = tauE D' ρ := h ρ
        rw [hE'] at e
        exact e
      exact z.pins.keep.frameKs.2 i (σ.comp ι) h'' τ a
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, -⟩ := hA0
    have hinj : Function.Injective ι := ι.injective
    refine ⟨a1, a2, a3, a4, a5, HEq.rfl, a6, a7, a8, a9, a10, a11, ?blk, hjL⟩
    rintro i ⟨i', hi'⟩ e
    dsimp only at e
    subst e
    refine ⟨(hcV i i rfl).1, (hcV i i rfl).2.1, (hcV i i rfl).2.2.1, (hcV i i rfl).2.2.2, HEq.rfl, hioP i, HEq.rfl,
      congr_arg_heq (fun s => (z.R.MW i s).H) hιc, congr_arg_heq (fun s => (z.R.MW i s).nacg) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).ips) hιc, congr_arg_heq (fun s => (z.R.MW i s).σ) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).lam) hιc, congr_arg_heq (fun s => (z.R.MW i s).ε) hιc,
      congr_arg_heq (fun s => (z.R.MW i s).fr) hιc, proof_irrel_heq _ _, congr_arg_heq (z.R.HW i) hιc, HEq.rfl, HEq.rfl, ?rest⟩
    intro ι₂ hι₂
    have hιι : ι₂ = ι := RingHom.ext fun x => D'.what₂.embLL.injective ((hι₂ x).trans (hι x).symm)
    have hσ : ∀ σ' : D'.what₂.LL →+* ℂ, σ'.comp ι = σ'.comp ι₂ := fun σ' => congrArg σ'.comp hιι.symm
    have hF := forms_crdOver (L := D.what₂.LL) (L' := D'.what₂.LL) (n := z.R.nW i) (W := fun σ => (z.R.HW i σ).H) (F := z.R.FW i)
      (F' := FW' i) hιι (hFW i)
    refine ⟨fun σ' => ⟨⟨congr_arg_heq (fun s => (z.R.MW i s).H) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).nacg) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).ips) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).σ) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).lam) (hσ σ'), congr_arg_heq (fun s => (z.R.MW i s).ε) (hσ σ'),
        congr_arg_heq (fun s => (z.R.MW i s).fr) (hσ σ'), proof_irrel_heq _ _⟩,
        congr_arg_heq (z.R.HW i) (hσ σ'), congr_arg_heq (z.R.gW i) (hσ σ'), hF.1 σ'⟩,
      hF.2.1, hF.2.2.1, hF.2.2.2.1, hF.2.2.2.2.1, hF.2.2.2.2.2⟩

end GlobalTheory.Mem.R3.Rw
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reset_modelsMeasuresForms_enlargedCoefficientBase : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
    (∀ y : core'.Q.c.F, B'.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) = (y : ℂ)) →
    HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG → RSideA z Wt' R →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideW z Wt' R₁ := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.resetW
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 2000000 in

theorem reset_stepW : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        (LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) →
        ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₁.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₁.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₁.eG.trans cG₁) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₁.mu R₁.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₁.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₁.IsInert ∧ R₁.IsTup ∧
        R₁.AllPlaces ∧ Keep R₁.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG₁ ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₁.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₁) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine Step.of_evLgG (GlobalTheory.Mem.Top.evLgG_of_evLg ?_)
  refine GlobalTheory.Mem.Top.V4.TwoPass.ev_mono ?_ (GlobalTheory.Mem.Top.V4.TwoPass.ev_and GlobalTheory.Mem.HostFrames.hostHyp_frames_ev GlobalTheory.T.valsIn_and_fam3_ok_of_coefficientField)
  rintro K ⟨hK, hO⟩
  refine hO.imp ?_
  rintro B' f' T' hOv hOB w' ⟨pin⟩ B f T w hE hf _ hp Z hX Wt z _ _ hFine _ Z' hX' _ hgrp _ core' alg' ha _ hKs hc _ _ _ _
  intro Xg tr R₀ cG hKept
  letI := alg'
  obtain ⟨hHH, -, -, hPos, hStd, hStdX, -, -⟩ := hK (w'.st Z') hOv
  obtain ⟨hVals, -⟩ := hOB w'.px w'.I hX' w'.ok w'.C_eq w'.xi_range
  refine (GlobalTheory.T.definiteFormsReading_reset_baseEnlargement z hE hf hp hFine.2.2.2 (fun i => (hStd _).2.1) hStdX hVals R₀ cG hKept).elim fun Ra h => h.elim fun cGa h => ?_
  refine (GlobalTheory.T.reset_modelsMeasuresForms_enlargedCoefficientBase z hE hf hp core' ha hc.1 hc.2.1 hc.2.2.1 Ra cGa h.1 h.2).elim fun R₁ h => h.elim fun cG₁ h => ?_
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩, b⟩ := h
  exact ⟨R₁, cG₁, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, b⟩

end GlobalTheory.Mem.R3.Rw
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reset_tuple_free_fields_keeps_clauses_comparison : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
    ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
      (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
      (∀ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y ∈ B'.LL0) →
      (∀ x ∈ B'.Ks, ∃ y : core'.Q.c.F, @algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y = x) →
      (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
      Formalism.L2.Pj.LawsCore core'.toCore → core'.Q.Canon → (∀ j, 1 ≤ (core'.Q.Dw j).p + (core'.Q.Dw j).q) → core'.pb = f'.P.pb →
      letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr₀ : TrI B' w'.px)
        (R₀ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG : G0 R₀.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        (LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₀.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₀.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₀.eG.trans cG) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₀.mu R₀.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₀.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧
        R₀.AllPlaces ∧ Keep R₀.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₀.toRealDat) →
        ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀) core'.Q.c.F)
        (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
        LevOf (w'.st Z') w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) R₁.toLevCh ∧ IsPlacewiseIdentity (w'.st Z') (px := w'.px) R₁.eG ∧
        GoodSet (w'.st Z') (px := w'.px) (R₁.eG.trans cG₁) Xg ∧ MuOf (w'.st Z') w'.I T' {v | B'.places.resChar v ∈ T'.pl} R₁.mu R₁.twPl ∧
        IdemClass (D := (w'.st Z').toD7) (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).A ∧ R₁.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 ∧ R₁.IsInert ∧ R₁.IsTup ∧
        R₁.AllPlaces ∧ Keep R₁.toRealDat (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀).lv2 cG₁ ∧ BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) Xg tr₀ R₁.toRealDat ∧
        RSideW z {v | B'.places.resChar v ∈ T'.pl} R₁) := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.reset_stepW
end
