import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CorrUniqHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowHodge
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHopLies
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowPiece
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCoverOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverOfIsQProjOverOfIsProper
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowCov
import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JConjBridge
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JJumpOfHT2
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHCube
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHForms
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHSections
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapSecEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.CechHEquivCohOnCechCubeMapOver
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.ClosedHT
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NiceBc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GoodOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.IntMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CoverOfPf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.HOpCover
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.OccMoveHolds
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpsExHolds

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jTrBc :
    BcSplits → TrBc.{u} := by
  intro hbc B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hspl x
  have key := (hbc g p q r s hs c hc J σ hσ).2.2 hspl
  exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
    (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j)) key x
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV GlobalTheory.HodgeCoh UpperTheory.Gal.G3 UpperTheory.Gal.Int.Geo
universe u v

private theorem hodgeTrace_pull_congr {F : Type} [Field F] {Y Z : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s]
    (p : Z ⟶ sp F) {q q' : Y ⟶ sp F} (e : q = q') (h₁ : s ≫ p = q) (h₂ : t ≫ p = q) (h₁' : s ≫ p = q') (h₂' : t ≫ p = q')
    (a b : ℕ) (x : hodgeH p a b) :
    hodgeTrace h₁ a b (hodgePull h₂ a b x) = hodgeTrace h₁' a b (hodgePull h₂' a b x) := by
  subst e; rfl

theorem UpperTheory.Gal.G3.jHodgeOpBc :
    BcSplits → HodgeTr → TrBc.{0} → HodgeOpBc := by
  intro hBc hTr hTrBc k F _ _ φ H g _ _ a b
  letI : Algebra k F := φ.toAlgebra
  obtain ⟨hF, hE, -⟩ := hBc (Spec.map (CommRingCat.ofHom φ)) H.q (H.s g ≫ H.q) (H.s g ≫ H.q) (H.s g) rfl
    (H.s g) rfl PEmpty (fun e => e.elim) (fun e => e.elim)
  refine ⟨hF, hE, hodgeTrace (bcMap_snd _ (H.s g) rfl) a b, ?_, ?_⟩
  · exact hTrBc (hodge F a b) _ H.q (H.s g ≫ H.q) (H.s g) rfl _ (hTr F a b _ _ _ (bcMap_snd _ _ _))
  · intro hF' hE' x
    exact @hodgeTrace_pull_congr _ _ _ _ _ _ hF' hE' _ _ _
      (bcMap_snd (Spec.map (CommRingCat.ofHom φ)) (H.s g) rfl) _ _ _ _ a b x
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem sq_bc {T Y S B : Scheme.{0}} (s : T ⟶ Y) (p : Y ⟶ S) (c : B ⟶ S) :
    IsPullback (pullback.fst (s ≫ p) c)
      (pullback.lift (pullback.fst (s ≫ p) c ≫ s) (pullback.snd (s ≫ p) c)
        (by rw [Category.assoc, pullback.condition]) : pullback (s ≫ p) c ⟶ pullback p c)
      s (pullback.fst p c) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := p) (h₃₁ := c) ?_ ?_
    (IsPullback.of_hasPullback p c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (s ≫ p) c
  · rw [pullback.lift_fst]

theorem UpperTheory.Gal.G3.jLowNice :
    FEtBasic → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowNice := by
  intro hb k L _ _ H θ O _ _ C D
  haveI : Smooth C.p := C.smooth
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (pullback.snd C.p (UpperTheory.Gal.Int.Geo.gen O k))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap O k) C.proj
  · intro g
    exact ⟨D.d g, hb.1 _ _ _ _ _ (sq_bc (D.s g) C.p (UpperTheory.Gal.Int.Geo.gen O k)) (D.fet g)⟩
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3.BaseChangeTowers

private noncomputable def cmp {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    pullback p ab ⟶ pullback p a :=
  pullback.lift (pullback.fst p ab) (pullback.snd p ab ≫ b)
    (by rw [pullback.condition, Category.assoc, h])

private theorem cmp_fst {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.fst p a = pullback.fst p ab := pullback.lift_fst _ _ _

private theorem cmp_snd {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.snd p a = pullback.snd p ab ≫ b := pullback.lift_snd _ _ _

private theorem cmp_isPullback {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp p a ab b h) (pullback.snd p ab) (pullback.snd p a) b := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p a) (h₂₂ := a) (v₁₃ := p) ?_ (cmp_snd p a ab b h)
    (IsPullback.of_hasPullback p a)
  rw [cmp_fst, h]
  exact IsPullback.of_hasPullback p ab

private theorem cmp_bcMap {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp q a ab b h ≫ bcMap a f hf = bcMap ab f hf ≫ cmp p a ab b h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, cmp_fst, bcMap_fst, ← Category.assoc, cmp_fst]
  · rw [Category.assoc, Category.assoc, bcMap_snd, cmp_snd, cmp_snd, ← Category.assoc, bcMap_snd]

private theorem cmp_bcMap_isPullback {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp q a ab b h) (bcMap ab f hf) (bcMap a f hf) (cmp p a ab b h) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p ab) (v₂₂ := pullback.snd p a) (h₃₁ := b) ?_
    (cmp_bcMap p q f hf a ab b h) (cmp_isPullback p a ab b h)
  rw [bcMap_snd, bcMap_snd]
  exact cmp_isPullback q a ab b h

end UpperTheory.Gal.G3.BaseChangeTowers

open UpperTheory.Gal.G3.BaseChangeTowers in
theorem UpperTheory.Gal.G3.jBCTower :
    UpperTheory.Gal.Seam.NiceBc → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BCTower := by
  intro hN k K F _ _ _ τ φ H hH
  refine ⟨hN k K τ H hH, ⟨?_⟩⟩
  have hab : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom (φ.comp τ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let a := Spec.map (CommRingCat.ofHom τ)
  let ab := Spec.map (CommRingCat.ofHom (φ.comp τ))
  let b := Spec.map (CommRingCat.ofHom φ)
  have hz : IsPullback (cmp H.q a ab b hab) (UpperTheory.Gal.Int.Geo.bcAlong H (φ.comp τ)).q
      (UpperTheory.Gal.Int.Geo.bcAlong H τ).q b := cmp_isPullback H.q a ab b hab
  refine
    { z := cmp H.q a ab b hab
      hz := hz
      y := fun j => cmp (H.s j ≫ H.q) a ab b hab
      hs := fun j => ?_
      ht := fun j => ?_ }
  · exact cmp_bcMap_isPullback H.q (H.s j ≫ H.q) (H.s j) rfl a ab b hab
  · exact cmp_bcMap H.q (H.s j ≫ H.q) (H.t j) (H.comm j) a ab b hab
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem isMatF_of_isMat {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
    (θ : H.Γ → Formalism.ConjugateSelfDual.Qbar l) {d : ℕ} (ρ₁ : (Ω ≃ₐ[k] Ω) →* Matrix.GeneralLinearGroup (Fin d) (Formalism.ConjugateSelfDual.Qbar l))
    (h : UpperTheory.Gal.Int.Geo.IsMat l H Ω (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁)
    (f : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Formalism.ConjugateSelfDual.Qbar l)) (hf : ∀ σ, (ρ₁ σ).val = f σ) :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.IsMatF H Ω θ f := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun σ j => ?_⟩
  rw [hb σ j, hf σ]

theorem UpperTheory.Gal.G3.jLocalMat :
    UpperTheory.Gal.Seam.NiceBc → UpperTheory.Gal.Seam.HopEx → UpperTheory.Gal.Seam.LocTower → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LocalMat := by
  intro hNice hHop hLoc E Ω _ _ _ _ _ l _ H θ hN Gw O _ _ _ Bw τK hτ
  refine ⟨fun g => ⟨_, hHop l _ _ (UpperTheory.Gal.Int.Geo.bcAlong H τK) (hNice _ _ τK H hN) g⟩, ?_⟩
  intro d ρ hρ
  obtain ⟨ρ₁, hρ₁, hc⟩ := hLoc l E _ Ω (Formalism.ConjugateSelfDual.Qbar l) τK Bw.j (fun x => (hτ x).symm) H hN
    (Formalism.ConjugateSelfDual.Qbar l) θ d ρ hρ
  refine isMatF_of_isMat (UpperTheory.Gal.Int.Geo.bcAlong H τK) (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁ hρ₁ _
    (fun σ => congrArg Units.val (hc _ σ (fun x => ?_)))
  rw [← Bw.e_comm]
  erw [MulEquiv.apply_symm_apply]
  rfl
end

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

theorem jGenIso : GenIso := by
  intro O O' k K _ _ _ _ _ _ φ τ h X p
  have hg : gen O' K ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom τ) ≫ gen O k := by
    simp only [gen, ← Spec.map_comp]
    congr 1
    ext x
    simpa using h x
  refine ⟨pullbackLeftPullbackSndIso p (Spec.map (CommRingCat.ofHom φ)) (gen O' K) ≪≫
    pullback.congrHom rfl hg ≪≫
    (pullbackLeftPullbackSndIso p (gen O k) (Spec.map (CommRingCat.ofHom τ))).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst]
    rw [pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

end UpperTheory.Gal.G3

end
end

section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jModBc :
    UpperTheory.Gal.Seam.GoodOf → ModBc := by
  intro hG l _ K O _ _ φ Y W p d hs hp c _ _
  haveI : SmoothOfRelativeDimension d p := hs
  haveI : SmoothOfRelativeDimension 0 c := (Etale.iff_smoothOfRelativeDimension_zero c).1 inferInstance
  have hcs : SmoothOfRelativeDimension d (c ≫ p) := by
    have h : SmoothOfRelativeDimension (0 + d) (c ≫ p) := inferInstance
    rwa [Nat.zero_add] at h
  have hqs : SmoothOfRelativeDimension d (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hcs
  have hcq : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (c ≫ p) :=
    GlobalTheory.isQProjOver_comp_of_isFinite_general c (GlobalTheory.SchemeWords.isQProjOver_of_isProjOver hp)
  haveI : IsProper p := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  have hcp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (c ≫ p) :=
    GlobalTheory.UPel.isProjOver_of_isQProjOver_of_isProper O W (c ≫ p) hcq inferInstance
  have hqp : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd φ hcp
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  have hsm : Smooth (pullback.snd (c ≫ p) (Spec.map (CommRingCat.ofHom φ))) :=
    SmoothOfRelativeDimension.smooth d _
  exact ⟨⟨hG l K.1 ⟨_, _⟩ hsm hqp, hsm⟩, hqs⟩
end

section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jBridgeInt :
    UpperTheory.Gal.Seam.IntMap → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BridgeInt := by
  intro hInt E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hB γ x
  obtain ⟨φ, hφ, -⟩ := hInt E Ω l w A hA O Bw hB
  have h1 : Bw.j (algebraMap E Ω x) =
      ((algebraMap (CrystallineSemistableComparison.OK l Bw.Kw.1) Bw.Kw.1 (φ x) : Bw.Kw.1) : PadicAlgCl l) := by
    rw [hφ x]
    rfl
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ ≤ 1 := by
    rw [h1]
    have hm : ‖(((φ x : Bw.Kw.1)) : PadicAlgCl l)‖₊ ≤ 1 := (φ x).2
    exact_mod_cast hm
  have h3 : ‖γ (Bw.j (algebraMap E Ω x))‖ = ‖Bw.j (algebraMap E Ω x)‖ :=
    (GlobalTheory.Cyc.Model.isom_gal γ).norm_map_of_map_zero (map_zero _) _
  rw [h3]
  exact h2
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHBasis :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis := by
  classical
  intro k k' _ _ _ J e M N _ _ _ _ ψ hψ I c
  let T : (I →₀ k') ≃+ (J →₀ M) :=
    (Finsupp.mapRange.addEquiv e.repr.toAddEquiv).trans ((Finsupp.curryAddEquiv).symm.trans
      ((Finsupp.domCongr (Equiv.prodComm I J)).trans
        (Finsupp.curryAddEquiv.trans (Finsupp.mapRange.addEquiv c.repr.symm.toAddEquiv))))
  have hTs : ∀ (i : I) (a : k'),
      T (Finsupp.single i a) = Finsupp.mapRange (fun b : k => b • c i) (zero_smul k _) (e.repr a) := by
    intro i a
    ext j
    simp only [Finsupp.mapRange_apply]
    simp [T, Finsupp.curryAddEquiv]
    have h : ((Finsupp.equivMapDomain (Equiv.prodComm I J) (Finsupp.single i (e.repr a)).uncurry).curry j)
        = Finsupp.single i (e.repr a j) := by
      ext i'
      simp only [Finsupp.curry_apply, Finsupp.equivMapDomain_apply, Finsupp.uncurry_apply]
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp_all
    rw [h, Finsupp.linearCombination_single]
  have hbc : ∀ f : J →₀ M, bcSum e ψ f = f.sum (fun j m => e j • ψ m) := by
    intro f
    simp [bcSum]; rfl
  let Φ : (I →₀ k') →ₗ[k'] N := Finsupp.linearCombination k' (fun i => ψ (c i))
  have key : ∀ g, Φ g = bcSum e ψ (T g) := by
    intro g
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, map_add, map_add, hf, hg]
    | single i a =>
      rw [hTs, hbc, Finsupp.sum_mapRange_index (by intro j; simp)]
      simp only [Φ, Finsupp.linearCombination_single]
      conv_lhs => rw [← e.linearCombination_repr a, Finsupp.linearCombination_apply]
      rw [Finsupp.sum, Finsupp.sum, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smulₛₗ, Algebra.smul_def, mul_comm, mul_smul]
  have hΦ : Function.Bijective Φ := by
    have h : (Φ : (I →₀ k') → N) = bcSum e ψ ∘ T := funext key
    rw [h]
    exact hψ.comp T.bijective
  let E := LinearEquiv.ofBijective Φ hΦ
  refine ⟨Module.Basis.ofRepr E.symm, fun i => ?_⟩
  rw [Module.Basis.coe_ofRepr]
  simp [E, Φ]
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHEquiv :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv := by
  intro k k' _ _ _ J e M N M₀ N₀ _ _ _ _ _ _ _ _ ψ E E' ψ₀ h hψ
  let R : (J →₀ M₀) ≃+ (J →₀ M) := Finsupp.mapRange.addEquiv E.toAddEquiv
  have key : ∀ f : J →₀ M₀, bcSum e ψ₀ f = E' (bcSum e ψ (R f)) := by
    intro f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add, map_add, map_add, map_add, hf, hg]
    | single j m =>
      simp only [R, Finsupp.mapRange.addEquiv_apply, Finsupp.mapRange_single]
      rw [bcSum_single, bcSum_single, h, map_smul]
      rfl
  have hfun : ⇑(bcSum e ψ₀) = ⇑E' ∘ ⇑(bcSum e ψ) ∘ ⇑R := funext key
  show Function.Bijective ⇑(bcSum e ψ₀)
  rw [hfun]
  exact E'.bijective.comp (hψ.comp R.bijective)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC

theorem UpperTheory.Gal.G3.jHAffine :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine := by
  intro k k' _ _ φ X X' s s' g h
  exact MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
end

section
open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.G3

theorem jHCover : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover := by
  intro k _ X s _
  haveI : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let C := X.affineCover.finiteSubcover
  let e := Fintype.equivFin C.I₀
  refine ⟨Fintype.card C.I₀, fun i => (C.f (e.symm i)).opensRange, ?_, ?_⟩
  · rw [e.symm.surjective.iSup_comp (fun j => (C.f j).opensRange)]
    exact C.iSup_opensRange
  · intro S hS
    have h := IsAffineOpen.biInf (X := X) (S : Set (Fin (Fintype.card C.I₀))) S.finite_toSet
      (Finset.coe_nonempty.mpr hS) (U := fun i => (C.f (e.symm i)).opensRange)
      (fun i _ => isAffineOpen_opensRange _)
    simpa only [Finset.mem_coe] using h

end UpperTheory.Gal.G3
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHOmega :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_forms → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_sections → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega := by
  intro hE hF hS hA k k' _ _ _ J e X X' s s' g h a V hV
  letI := algΓ s
  letI := algΓ s'
  haveI : IsAffineHom g := hA k k' (algebraMap k k') X X' s s' g h
  have hV' : IsAffineOpen (g ⁻¹ᵁ V) := hV.preimage g
  have hForms : IsBC e (formPullS h.w V a) :=
    hF k k' J e _ _ _ (semiHom_appSecS h.w V) (hS k k' J e X X' s s' g h V hV) a
  refine hE k k' J e _ _ _ _ (formPullS h.w V a) (omSecEquiv s a ⟨V, hV⟩).symm
    (omSecEquiv s' a ⟨g ⁻¹ᵁ V, hV'⟩) _ (fun x ↦ ?_) hForms
  obtain ⟨y, rfl⟩ := (omSecEquiv s a ⟨V, hV⟩).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact omegaPullS_toOmega h.w a V y
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

theorem UpperTheory.Gal.G3.jHFun :
    ∀ (k k' : Type) [Field k] [Field k'] {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (f : Y ⟶ X) (f' : Y' ⟶ X') [IsFinite f] [Etale f] [IsFinite f'] [Etale f'], IsPullback e f' f g → ∀ (U : X.Opens) (hU : IsAffineOpen U) (hU' : IsAffineOpen (g ⁻¹ᵁ U)) (hle : f' ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ e ⁻¹ᵁ (f ⁻¹ᵁ U)) (b : Sec r (f ⁻¹ᵁ U)), appSecS s s' g U (secTrace s r hU b) = secTrace s' r' hU' (Sec.res r' hle (appSecS r r' e (f ⁻¹ᵁ U) b)) := by
  intro k k' _ _ X X' Y Y' s s' g r r' e f f' _ _ _ _ H U hU hU' hle b
  have hfU : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  have hUY : f' ⁻¹ᵁ (g ⁻¹ᵁ U) = e ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ f' ⁻¹ᵁ (g ⁻¹ᵁ U) := (inf_eq_right.mpr hle).symm
  have hP := (isIso_pushoutSection_iff H (US := U) (UT := g ⁻¹ᵁ U) (UX := f ⁻¹ᵁ U)
    le_rfl le_rfl hUY).mp (isIso_pushoutSection_of_isAffineOpen H le_rfl le_rfl hUY hU hU' hfU)
  rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app] at hP
  letI iBC : Algebra (Sec s U) (Sec s' (g ⁻¹ᵁ U)) := (appSecS s s' g U).toAlgebra
  letI iBB : Algebra (Sec s U) (Sec r (f ⁻¹ᵁ U)) := secAlg s r f U
  letI iCC : Algebra (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) := secAlg s' r' f' (g ⁻¹ᵁ U)
  letI iBC' : Algebra (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((Sec.res r' hle).toRingHom.comp (appSecS r r' e (f ⁻¹ᵁ U))).toAlgebra
  letI iBX : Algebra (Sec s U) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    ((algebraMap (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))).comp
      (algebraMap (Sec s U) (Sec s' (g ⁻¹ᵁ U)))).toAlgebra
  haveI t1 : IsScalarTower (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t2 : IsScalarTower (Sec s U) (Sec r (f ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    IsScalarTower.of_algebraMap_eq (fun x => (congrArg (fun φ => CommRingCat.Hom.hom φ x) hP.w).symm)
  haveI := sec_finite (s := s) (s' := r) (f := f) hU
  haveI := sec_etale (s := s) (s' := r) (f := f) hU
  haveI := projective_of_etale (Sec s U) (Sec r (f ⁻¹ᵁ U))
  haveI := sec_finite (s := s') (s' := r') (f := f') hU'
  haveI := sec_etale (s := s') (s' := r') (f := f') hU'
  haveI := projective_of_etale (Sec s' (g ⁻¹ᵁ U)) (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U)))
  haveI hPo : Algebra.IsPushout (Sec s U) (Sec s' (g ⁻¹ᵁ U)) (Sec r (f ⁻¹ᵁ U))
      (Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) :=
    CommRingCat.isPushout_iff_isPushout.mp hP.flip
  exact (algTrace_of_isPushout (B := Sec s U) (B' := Sec r (f ⁻¹ᵁ U)) (C := Sec s' (g ⁻¹ᵁ U))
    (C' := Sec r' (f' ⁻¹ᵁ (g ⁻¹ᵁ U))) b).symm
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN

private theorem iInf_pre {X X' : Scheme.{0}} (g : X' ⟶ X) {n : ℕ} (U : Fin n → X.Opens)
    (S : Finset (Fin n)) : (⨅ i ∈ S, g ⁻¹ᵁ U i) = g ⁻¹ᵁ (⨅ i ∈ S, U i) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro i S _ ih
    rw [Finset.iInf_insert, Finset.iInf_insert, Scheme.Hom.preimage_inf, ih]

private theorem pull_isBC (pE : P_equiv) (pC : P_cube) (pA : P_affine) (pV : P_cover)
    (pO : P_omega) (pH : P_cech) {k k' : Type} [Field k] [Field k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {X X' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X)
    (h : IsPullback g s' s (spMap (algebraMap k k'))) [IsProper s] (a b : ℕ) :
    IsBC e (hodgePullS h.w a b) := by
  letI := algΓ s
  letI := algΓ s'
  obtain ⟨n, U, hc, hU⟩ := pV k X s
  haveI : IsAffineHom g := pA k k' (algebraMap k k') X X' s s' g h
  have hc' : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hc, Scheme.Hom.preimage_top]
  have hU' : ∀ S : Finset (Fin n), S.Nonempty → IsAffineOpen (⨅ i ∈ S, g ⁻¹ᵁ U i) := by
    intro S hS
    rw [iInf_pre]
    exact IsAffineHom.isAffine_preimage _ (hU S hS)
  have hcube : IsBC e
      ((cechCubeMapOver ⊤ U (appTop_algebraMapS h.w) (omegaPullS h.w a)).homology b) := by
    apply pC k k' J e (Fin n)
    intro S hS
    have hA : IsAffineOpen (cechOpen ⊤ U S) := by
      rw [cechOpen, top_inf_eq]
      exact hU S hS
    refine pE k k' J e _ _ _ _
      (sectionsOn.mapOver (appTop_algebraMapS h.w) (omegaPullS h.w a) (cechOpen ⊤ U S))
      (LinearEquiv.refl k _) (sectionsOn.congrOpens k' _ (preimage_cechOpen g ⊤ U S)) _ ?_
      (pO k k' J e X X' s s' g h a _ hA)
    intro x
    exact (sectionsOn.congrOpens_apply k' (Omega s' a) (preimage_cechOpen g ⊤ U S) _).symm
  refine pE k k' J e _ _ _ _ _ (cechHEquivCoh k hc hU (Omega s a) b).symm
    (cechHEquivCoh k' hc' hU' (Omega s' a) b) (hodgePullS h.w a b) ?_ hcube
  intro x
  obtain ⟨y, rfl⟩ := (cechHEquivCoh k hc hU (Omega s a) b).surjective x
  rw [LinearEquiv.symm_apply_apply]
  exact pH k k' X X' s s' g h.w a b n U hc hU hc' hU' y

theorem UpperTheory.Gal.G3.jHBC :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_basis → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_equiv → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cube → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_affine → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_omega → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cech → (∀ (k k' : Type) [Field k] [Field k'] (φ : k →+* k') {X X' Y Y' : Scheme.{0}} (s : X ⟶ Sp k) (s' : X' ⟶ Sp k') (g : X' ⟶ X) (h : IsPullback g s' s (spMap φ)) (r : Y ⟶ Sp k) (r' : Y' ⟶ Sp k') (e : Y' ⟶ Y) (he : IsPullback e r' r (spMap φ)) (f : Y ⟶ X) (hf : f ≫ s = r) (f' : Y' ⟶ X') (hf' : f' ≫ s' = r'), e ≫ f = f' ≫ g → ∀ (a b : ℕ) [IsFinite f] [Etale f] [IsFinite f'] [Etale f'] (y : hodgeH r a b), hodgePullS h.w a b (hodgeTrace hf a b y) = hodgeTrace hf' a b (hodgePullS he.w a b y)) → PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC := by
  intro pB pE pC pA pV pO pH pT k k' _ _ φ
  refine ⟨fun s s' g h a b ↦ hodgePullS h.w a b, ?_, ?_⟩
  · intro X X' s s' g h _ a b I c
    letI : Algebra k k' := φ.toAlgebra
    have h₀ : IsPullback g s' s (spMap (algebraMap k k')) := h
    exact pB k k' _ (Module.Basis.ofVectorSpace k k') _ _ (hodgePullS h₀.w a b)
      (pull_isBC pE pC pA pV pO pH _ s s' g h₀ a b) I c
  · intro X X' Y Y' s s' g h r r' e he f hf f' hf' w a b
    exact ⟨fun x ↦ hodgePullS_nat_pull h.w he.w hf hf' w a b x,
      fun y ↦ pT k k' φ s s' g h r r' e he f hf f' hf' w a b y⟩
end

section
open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

theorem seamHopEx_holds : UpperTheory.Gal.Seam.HopEx := by
  intro l _ k Ω _ _ _ _ _ H hN g
  obtain ⟨d, hd⟩ := hN.2.2 g
  have hl : (l : k) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap k Ω) h
    rw [map_natCast, map_zero] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  exact (hopSpec_holds l hl H Ω g d hd).1

theorem locTower_holds : UpperTheory.Gal.Seam.LocTower := locTower_of vBcS_holds seamHopEx_holds UpperTheory.Gal.Seam.niceBc

theorem traceSplit_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.TraceSplit := by
  intro k _ Z Y W q s _ _ c _ _ I _ σ hσ hS a b y
  exact hodgeTr_holds k a b q (s ≫ q) s rfl W (c ≫ q) c rfl I σ hσ hS y

theorem hodgeBC_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HodgeBC :=
  jHBC jHBasis jHEquiv jHCube jHAffine jHCover (jHOmega jHEquiv jHForms jHSections jHAffine) PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.cech_holds
    (jHTrace jHFun jHAffine)

theorem coverOp_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := jCoverOp etnGood_holds @bcSplits_holds @bcGal_holds corrUniq_holds

theorem lowHodge_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowHodge :=
  jLowHodge hodgeGood_holds @bcGood_holds.{0} fEtBasic_holds
    (jHodgeOpBc @bcSplits_holds hodgeTr_holds (jTrBc.{0} @bcSplits_holds)) @coverInv_holds.{0} @liesOp_holds.{0}

theorem hopLies_holds : HopLies := jHopLies etGood_holds @bcGood_holds.{1} fEtBasic_holds hopSpec_holds @liesOp_holds.{1}

theorem lowPiece_holds : PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowPiece := jLowPiece hopLies_holds pieceLe_holds

theorem lowCov_holds : LowCov :=
  jLowCov @galClosD_holds @bcSplits_holds @bcGal_holds @jGenIso (jModBc UpperTheory.Gal.Seam.goodOf)

theorem jumpStep_of (hS : CrystallineSemistableComparison.HTSpecB.HTSpecGood) (hC : CrysStep) (hR : RepEx) : JumpStep :=
  PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpStep_of
    (PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpCore_of hS (jLowNice fEtBasic_holds) lowHodge_holds lowPiece_holds (matEx_of hR)
      (jLocalMat UpperTheory.Gal.Seam.niceBc seamHopEx_holds locTower_holds) (coverLow_of_cov PositivityTheory.AutomorphicGaloisHodgeTate.G8.coverOf lowCov_holds)
      (jBridgeInt UpperTheory.Gal.Seam.intMap) (jBCTower UpperTheory.Gal.Seam.niceBc)
      (PositivityTheory.AutomorphicGaloisHodgeTate.G8.locE_of hodgeBC_holds traceSplit_holds coverOp_holds) PositivityTheory.AutomorphicGaloisHodgeTate.G8.OccMove_holds
      PositivityTheory.AutomorphicGaloisHodgeTate.G8.jumpsEx_holds jConjBridge jJumpOfHT2) hC

end UpperTheory.Gal.G3
end
