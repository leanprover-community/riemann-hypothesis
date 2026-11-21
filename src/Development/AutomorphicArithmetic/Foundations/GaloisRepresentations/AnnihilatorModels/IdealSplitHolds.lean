import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MWModEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.ResSurj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRankN
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecCard
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPairCalc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullIsog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.UEltOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFactorsThroughMulN
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAdjoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKerFromU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsoOfKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MConstSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.TensorDecomp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecSurj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecEquiv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPowExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdReadOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftFF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLineC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PowSuccSubMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFFRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKerRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRedPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKillLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSplitAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.ExistsAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCaseE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRingHomog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCotanOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRepHomog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SpMapAlgComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobPass
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTanOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobHom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPicFrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MQuasiInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobIsog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsogComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCaseW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.EwOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCorrBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdEmb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevExistsPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdKSE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MUKerW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIdealSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLevPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjEEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CongKSOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProdHolds

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.valPtsX_of :
    ValPtsX := by
  intro S K h hp V _ _ _ z
  have : IsProper h := hp
  constructor
  · intro g g' hg hg' e
    have c : CommSq (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z :=
      ⟨by rw [Category.assoc, hg]⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, _, z, c⟩
    have hs : Subsingleton Q.commSq.LiftStruct := IsSeparated.valuativeCriterion h Q
    let l₁ : Q.commSq.LiftStruct := ⟨g, rfl, hg⟩
    let l₂ : Q.commSq.LiftStruct := ⟨g', e.symm, hg'⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  · intro g hg
    have c : CommSq g (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z := ⟨hg⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, g, z, c⟩
    have hu : (ValuativeCriterion.Existence ⊓ @QuasiCompact) h := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    obtain ⟨l, h₁, h₂⟩ := (hu.1 Q).exists_lift
    exact ⟨l, h₂, h₁⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.objTri_of :
    ObjTri := by
  intro p _ D R _ b N hN hNp S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g
  refine ⟨fun m m' => GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ f m m', ?_⟩
  intro fg h m₁₃ m₂₃
  subst h
  obtain ⟨m₁₂⟩ := GlobalTheory.UPel.HT.MapComp.cancel m₁₃ m₂₃
  obtain ⟨c, hc⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁₂ m₂₃
  exact ⟨m₁₂, by rw [← hc]; exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ _ c m₁₃⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledEx_of :
    ObjTri → PullIsog → PullKer → PulledEx := by
  intro hTri hIsog hKer p _ D R _ b N hN hc M r w j c T S x σ hx o₁ m₁ y hy
  obtain ⟨m₀, htri⟩ := (hTri p D R b N hN hc S T.Y M.X σ (T.s ≫ M.s) M.s o₁ T.o M.univ y T.s).2 x hy m₁ T.ms
  have hσ : y ≫ T.s ≫ M.s = σ := by rw [← Category.assoc, hy, hx]
  obtain ⟨o', m', ψ, hisog, hsq⟩ := hIsog p D R b N T.Y S (T.s ≫ M.s) σ y hσ c T.o T.o' T.ψ T.isog o₁ m₀
  have htj := (hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ o' m₀ m' T.ψ ψ hsq).2 r w j T.tj
  exact ⟨⟨o', ψ, m₀, m', hsq, htri, hisog, htj⟩⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledRead_of :
    PullKer → PulledRead := by
  intro hKer p _ D R _ b N M r w j c T S x σ o₁ m₁ y hy P a
  have hw : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = y := by
    have h1 := P.m₀.cart.1.w
    have h2 : a.left ≫ o₁.A.hom = 𝟙 S := Over.w a
    rw [Category.assoc, h1, ← Category.assoc, h2]
    exact Category.id_comp y
  have htri : (a.left ≫ P.m₀.φ) ≫ T.ms.φ = a.left ≫ m₁.φ := by
    rw [Category.assoc, P.tri]
  let a₀ : Over.mk y ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw
  have ha₀ : a₀.left = a.left ≫ P.m₀.φ := rfl
  have hk := ((hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
    (𝟙_ (Over S)) (Over.mk y) rfl a a₀ (by simp [ha₀])).1
  refine ⟨⟨fun h a' ha' => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have hEq : a' = a₀ := by
      apply Over.OverMorphism.ext
      apply T.ms.cart.1.hom_ext
      · rw [ha', ha₀, htri]
      · have h3 : a'.left ≫ T.o.A.hom = y := Over.w a'
        rw [h3, ha₀, hw]
    rw [hEq]
    exact hk.1 h
  · exact hk.2 (h a₀ (by rw [ha₀, htri]))
  · have hl : T.ms.cart.1.lift (a.left ≫ m₁.φ) y h = a.left ≫ P.m₀.φ := by
      apply T.ms.cart.1.hom_ext
      · rw [T.ms.cart.1.lift_fst, htri]
      · rw [T.ms.cart.1.lift_snd, hw]
    unfold TjD.img
    rw [hl, Over.comp_left]
    simp only [Category.assoc]
    rw [reassoc_of% P.sq]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.divC_of :
    DivC := by
  intro S A B _ _ _ _ hA c hc
  obtain ⟨hfin, hflat, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA c hc
  have hmon : IsMonHom (mulN A c) := by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow]
    exact GlobalTheory.AbLaw.MulN.isMonHom_mulA A c
  have hqc : QuasiCompact (mulN A c).left := inferInstance
  have key : ∀ ν : A ⟶ B, IsMonHom ν → mulN A c ≫ ν = ν ^ c := by
    intro ν _
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.pow_comp, Category.id_comp]
  have hker : ∀ (T : Over S) (g : T ⟶ A), g ≫ mulN A c = g ^ c := by
    intro T g
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
  refine ⟨fun h hh htors => ?_, fun ν ν' hν hν' heq => ?_⟩
  · obtain ⟨⟨ψ, hψ, hcomp⟩, _⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S A A B (mulN A c) h
      hmon hh hflat hsurj hqc (fun T x hx => htors T x (by rw [← hker]; exact hx))
    exact ⟨ψ, hψ, by rw [← key ψ hψ, hcomp]⟩
  · obtain ⟨_, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S A A A (mulN A c) (mulN A c)
      hmon hmon hflat hsurj hqc (fun _ _ hx => hx)
    rw [← cancel_epi (mulN A c), key ν hν, key ν' hν', heq]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.torsFree_of :
    DivC → TorsFree := by
  intro h k _ A B _ _ _ _ hA hB L hL hadd hadd' c hc hcls
  obtain ⟨D, instD, Q, hD, -, hQ, hQ'⟩ := GlobalTheory.dualAbelianScheme _ A hA
  have hcomm : IsCommMonObj D := hD.comm
  obtain ⟨x, hx, hx'⟩ := GlobalTheory.BirigidLift.exists_hom hQ hQ'.additive hL hadd hadd'
  have hone : IsMonHom (1 : B ⟶ D) := inferInstance
  have hev : ∀ (Y : Over (Sp k)) (a : Y ⟶ A) (b b' : Y ⟶ D),
      evc hQ.isLB a (b * b') = evc hQ.isLB a b + evc hQ.isLB a b' :=
    (GlobalTheory.BirigidLift.isAdditive_swap_iff hQ.isLB).1 hQ'.additive
  have hpow : ∀ (n : ℕ) (b : B ⟶ D), evc hQ.isLB (fst A B) (snd A B ≫ b ^ n) =
      n • evc hQ.isLB (fst A B) (snd A B ≫ b) := by
    intro n b
    induction n with
    | zero => rw [pow_zero, MonObj.comp_one, zero_smul, GlobalTheory.AbDual.evc_one_right hQ.isLB hQ.zero]
    | succ n ih => rw [pow_succ, MonObj.comp_mul, hev, ih, succ_nsmul]
  have h1 : evc hQ.isLB (fst A B) (snd A B ≫ x ^ c) =
      evc hQ.isLB (fst A B) (snd A B ≫ (1 : B ⟶ D)) := by
    rw [hpow, ← hx', hcls, MonObj.comp_one, GlobalTheory.AbDual.evc_one_right hQ.isLB hQ.zero]
  have h2 : x ^ c = 1 := GlobalTheory.BirigidLift.dual_ext hQ h1
  have h3 : x = 1 := (h (Sp k) B D hB c hc).2 x 1 hx hone (by rw [h2, one_pow])
  rw [hx', h3, MonObj.comp_one, GlobalTheory.AbDual.evc_one_right hQ.isLB hQ.zero]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.grCard_of :
    GrCard := by
  intro k H _ _ _ _ n j hn
  have hdim : Module.finrank k H = Module.finrank k (Fin n → k) := by simp [hn]
  let e : H ≃ₗ[k] (Fin n → k) := LinearEquiv.ofFinrankEq H (Fin n → k) hdim
  apply Nat.card_congr
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro D
  change Module.finrank k D = j ↔ Module.finrank k (D.map (e : H →ₗ[k] (Fin n → k))) = j
  rw [LinearEquiv.finrank_map_eq]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma closed_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of O)) (z : X) :
    s z = IsLocalRing.closedPoint O ↔ z ∉ X.basicOpen (fn s ϖ) := by
  have key : z ∈ X.basicOpen (fn s ϖ) ↔ ϖ ∉ (s z).asIdeal := by
    rw [show X.basicOpen (fn s ϖ) = s ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) from (Scheme.preimage_basicOpen_top s _).symm]
    change s z ∈ (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) ↔ _
    rw [basicOpen_eq_of_affine]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [key, not_not]
  constructor
  · intro h
    have hm : (s z).asIdeal = IsLocalRing.maximalIdeal O := congrArg PrimeSpectrum.asIdeal h
    rw [hm]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · intro h
    have hne : (s z).asIdeal ≠ ⊥ := fun hb0 => hϖ.ne_zero (by simpa [hb0] using h)
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (s z).2))

theorem UpperTheory.Gal.crystallineComparison.Mod.genDown_of :
    GenDown := by
  intro O _ _ _ ϖ hϖ X Y s h hflat y hy
  have hc : ∀ y' : Y, s (h y') = IsLocalRing.closedPoint O ↔
      y' ∉ Y.basicOpen (fn (h ≫ s) ϖ) := by
    intro y'
    rw [← closed_iff hϖ (h ≫ s) y', Scheme.Hom.comp_apply]
  refine ⟨(hc y).mpr hy.1, fun z' hz' hsp => ?_⟩
  obtain ⟨y', hy'sp, rfl⟩ := Flat.generalizingMap h hsp
  have := hy.2 y' ((hc y').mp hz') hy'sp
  rw [this]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.resClosed_of :
    ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hm hirr
  have hsurj : Function.Surjective (IsLocalRing.residue V) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue V) :=
    Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hpos : 0 < P.natDegree := hdeg ▸ hirr.natDegree_pos
  have hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact (Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral V x := by
    refine ⟨P, hPm, ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hy : P.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.algOf_of :
    AlgOf := by
  intro S K h hfin hflat V _ _ z
  let h' : pullback h z ⟶ Sp V := pullback.snd h z
  haveI : IsFinite h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hfin
  haveI : Flat h' := MorphismProperty.of_isPullback (IsPullback.of_hasPullback h z) hflat
  haveI : IsAffine (pullback h z) := isAffine_of_isAffineHom h'
  let φ : CommRingCat.of V ⟶ Γ(pullback h z, ⊤) := (Scheme.ΓSpecIso (.of V)).inv ≫ h'.appTop
  letI alg : Algebra V Γ(pullback h z, ⊤) := φ.hom.toAlgebra
  have hfinite : φ.hom.Finite := by
    have h1 : h'.appTop.hom.Finite := Scheme.Hom.finite_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Finite :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv).2
    exact RingHom.Finite.comp h1 h2
  have hflat' : φ.hom.Flat := by
    have h1 : h'.appTop.hom.Flat := Scheme.Hom.flat_appTop h'
    have h2 : (Scheme.ΓSpecIso (.of V)).inv.hom.Flat :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).inv)
    exact RingHom.Flat.comp h2 h1
  haveI mf : Module.Finite V Γ(pullback h z, ⊤) := hfinite
  haveI mfl : Module.Flat V Γ(pullback h z, ⊤) := hflat'
  refine ⟨Γ(pullback h z, ⊤), inferInstance, alg, (pullback h z).isoSpec.inv ≫ pullback.fst h z, mf,
    Module.free_of_flat_of_isLocalRing, ?_⟩
  have key : (pullback h z).isoSpec.inv ≫ h' = spMap (algebraMap V Γ(pullback h z, ⊤)) := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have sq : IsPullback (pullback h z).isoSpec.inv (spMap (algebraMap V Γ(pullback h z, ⊤))) h' (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, key]⟩
  have := sq.paste_horiz (IsPullback.of_hasPullback h z)
  rwa [Category.id_comp] at this
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.sameE_of :
    KillLocal → InfE → SameE := by
  intro hK hI p _ D R _ b N r κ _ _ s o o₁ o₂ ψ₁ ψ₂ hψ₂ hsub d hrep hcard hkill T g hg
  refine ⟨hK κ o.A o₂.A ψ₂ hψ₂ (UKer r o ψ₁) d hrep hsub hkill ?_ T g hg, hg.2⟩
  intro Λ _ _ _ ε g' hP hinf
  rw [hI κ o.A (UKer r o ψ₁) d hrep hcard Λ ε g' hP hinf]
  exact MonObj.one_comp _
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.imgEq_of :
    ObjTri → ImgEq := by
  intro hTri p _ D R _ b N hN hNp M S s o₁ o₂ t₁ t₂ h₁ h₂ n₁ n₂ m
  obtain ⟨c, hc⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m n₂
  have ht : t₁ = 𝟙 S ≫ t₂ :=
    (M.rep S s o₁).unique ⟨h₁, ⟨n₁⟩⟩ ⟨by rw [Category.id_comp]; exact h₂, ⟨c⟩⟩
  have ht' : t₁ = t₂ := by rw [ht, Category.id_comp]
  refine ⟨ht', ?_⟩
  have key : ∀ f : S ⟶ M.X, f = t₁ → ∀ mm : ObjMap o₁ M.univ f, mm.φ = n₁.φ := by
    intro f hf mm
    subst hf
    exact (hTri p D R b N hN hNp S M.X M.X s M.s M.s o₁ M.univ M.univ f (𝟙 _)).1 mm n₁
  rw [← hc]
  exact key _ ht.symm c
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repOfFF_of :
    AlgOf → RepOfFF := by
  rintro hA κ _ A P ⟨K, i, hm, hfin, hfl, hP⟩
  obtain ⟨B, _, _, k, hf, hfr, pb⟩ := hA (Sp κ) K.left K.hom hfin hfl κ (𝟙 _)
  have hk : IsIso k := pb.isIso_fst_of_isIso
  have hw : k ≫ K.hom = spMap (algebraMap κ B) := by
    simpa using pb.w
  let e : algPt κ B ≅ K := Over.isoMk (asIso k) hw
  refine ⟨Module.finrank κ B, B, ‹_›, ‹_›, hf, hfr, rfl, e.hom ≫ i, inferInstance, fun T g => ?_⟩
  rw [← hP T g]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.hom, by simpa using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.inv, by simpa using hy⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.levPull_of :
    PullKer → LevPull := by
  intro _ p _ D R _ b N S S' s s' f o o₁ m 𝔞 ρ lv h
  exact GlobalTheory.UPel.HT.EtLev.isEtLev_exists_pull m h
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.etInj_of :
    ObjTri → LevPull → EtInj := by
  intro hTri hPull p _ D R _ b N h3 hc M 𝔞 ρ E π hπ mπ X u v huv hlv
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N E.X X E.s u E.univ
  obtain ⟨l, hl, hlu⟩ := hPull p D R b N E.X X E.s (u ≫ E.s) u E.univ o₁ m₁ 𝔞 ρ E.lv E.isLev
  obtain ⟨m₁₃, hm₁₃⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mπ
  obtain ⟨m₂, hm₂⟩ := (hTri p D R b N h3 hc X E.X M.X (u ≫ E.s) E.s M.s o₁ E.univ M.univ v π).2
    (u ≫ π) huv.symm m₁₃ mπ
  have hvs : v ≫ E.s = u ≫ E.s := by
    rw [← hπ, ← Category.assoc, ← Category.assoc, huv]
  have hsec : ∀ y, (l y).left ≫ o₁.A.hom = 𝟙 X := fun y => by
    simpa using Over.w (l y)
  have hsec' : ∀ y, (E.lv y).left ≫ E.univ.A.hom = 𝟙 E.X := fun y => by
    simpa using Over.w (E.lv y)
  have hlv₂ : ∀ y, (l y).left ≫ m₂.φ = v ≫ (E.lv y).left := fun y => by
    refine mπ.cart.1.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [hm₂, hm₁₃, ← Category.assoc, hlu y, Category.assoc, hlv y]
    · simp only [Category.assoc]
      rw [m₂.cart.1.w, ← Category.assoc, hsec, hsec', Category.comp_id]
      exact Category.id_comp v
  exact (E.rep X _ o₁ l hl).unique ⟨rfl, m₁, hlu⟩ ⟨hvs, m₂, hlv₂⟩
end

section
namespace UpperTheory.Gal.crystallineComparison.Mod

theorem wModEx_holds  : WModEx := wModEx_of
theorem valPtsX_holds  : ValPtsX := valPtsX_of
theorem wVal_holds  : WVal := wVal_of valPtsX_holds
theorem rankN_holds  : RankN := rankN_of wVal_holds
theorem secCard_holds  : SecCard := secCard_of
theorem objTri_holds  : ObjTri := objTri_of
theorem pairCalc_holds  : PairCalc := pairCalc_of
theorem pullIsog_holds  : PullIsog := pullIsog_of
theorem pullKer_holds  : PullKer := pullKer_of
theorem pulledEx_holds  : PulledEx := pulledEx_of objTri_holds pullIsog_holds pullKer_holds
theorem pulledRead_holds  : PulledRead := pulledRead_of pullKer_holds
theorem uElt_holds  : UElt := uElt_of
theorem divC_holds  : DivC := divC_of
theorem torsFree_holds  : TorsFree := torsFree_of divC_holds
theorem adjoint_holds  : Adjoint := adjoint_of pairCalc_holds torsFree_holds
theorem kerFromU_holds  : KerFromU := kerFromU_of uElt_holds pairCalc_holds adjoint_holds divC_holds
theorem isoOfKer_holds  : IsoOfKer := isoOfKer_of pairCalc_holds adjoint_holds divC_holds torsFree_holds
theorem secInj_holds  : SecInj := secInj_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds
theorem constSub_holds  : ConstSub := constSub_of
theorem oMod_holds  : OMod := oMod_of
theorem secSurj_holds (h4 : QuotObj) : SecSurj := secSurj_of constSub_holds oMod_holds h4 objTri_holds pullKer_holds
theorem secEquiv_holds (h4 : QuotObj) : SecEquiv := secEquiv_of wVal_holds rankN_holds valPtsX_holds secCard_holds secInj_holds (secSurj_holds h4)
theorem grCard_holds  : GrCard := grCard_of
theorem powExt_holds  : PowExt := powExt_of
theorem genDown_holds  : GenDown := genDown_of
theorem resClosed_holds  : ResClosed := resClosed_of
theorem ordReadOf_holds  : OrdReadOf := ordReadOf_of countIn_of countOut_of
theorem algOf_holds  : AlgOf := algOf_of
theorem liftPt_holds  : LiftPt := liftPt_of
theorem liftFF_holds  : LiftFF := liftFF_of algOf_holds liftPt_holds
theorem lineC_holds  : LineC := lineC_of rankN_holds liftFF_holds
theorem kerU_holds  : KerU := kerU_of uElt_holds
theorem fFRead_holds  : FFRead := fFRead_of algOf_holds
theorem kerRead_holds  : KerRead := kerRead_of kerU_holds fFRead_holds liftFF_holds pullKer_holds wVal_holds
theorem redPts_holds  : RedPts := redPts_of
theorem killLocal_holds  : KillLocal := killLocal_of
theorem splitAlg_holds  : SplitAlg := splitAlg_of
theorem infE_holds  : InfE := infE_of splitAlg_holds
theorem sameE_holds  : SameE := sameE_of killLocal_holds infE_holds
theorem imgEq_holds  : ImgEq := imgEq_of objTri_holds
theorem caseE_holds  : CaseE := caseE_of sameE_holds kerU_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
theorem ringHomog_holds  : RingHomog := ringHomog_of
theorem cotanOne_holds  : CotanOne := cotanOne_of
theorem chainLoc_holds  : ChainLoc := chainLoc_of
theorem chainRing_holds  : ChainRing := chainRing_of chainLoc_holds
theorem repHomog_holds  : RepHomog := repHomog_of
theorem frobRing_holds  : FrobRing := frobRing_of
theorem infW_holds  : InfW := infW_of ringHomog_holds cotanOne_holds chainRing_holds repHomog_holds frobRing_holds
theorem frobPass_holds  : FrobPass := frobPass_of infE_holds
theorem repOfFF_holds  : RepOfFF := repOfFF_of algOf_holds
theorem tanOne_holds  : TanOne := tanOne_of uElt_holds
theorem sameW_holds  : SameW := sameW_of killLocal_holds infW_holds frobPass_holds kerU_holds repOfFF_holds tanOne_holds
theorem frobHom_holds  : FrobHom := frobHom_of
theorem frobFin_holds  : FrobFin := frobFin_of
theorem picFrob_holds  : PicFrob := picFrob_of
theorem quasiInv_holds  : QuasiInv := quasiInv_of pairCalc_holds divC_holds
theorem frobIsog_holds  : FrobIsog := frobIsog_of frobHom_holds frobFin_holds picFrob_holds quasiInv_holds
theorem isogComp_holds  : IsogComp := isogComp_of pairCalc_holds
theorem caseW_holds  : CaseW := caseW_of sameW_holds frobIsog_holds isogComp_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
theorem eW_holds (h4 : QuotObj) : EW := ew_of wModEx_holds rankN_holds lineC_holds (secEquiv_holds h4) kerRead_holds redPts_holds countIn_of pulledEx_holds caseE_holds caseW_holds
theorem corrBC_holds (h4 : QuotObj) : CorrBC := corrBC_of wModEx_holds rankN_holds (secEquiv_holds h4) grCard_holds
theorem ordEmb_holds (h3 : OrdGen) (h4 : QuotObj) : OrdEmb := ordEmb_of h3 genDown_holds resClosed_holds ordReadOf_holds (eW_holds h4)
theorem levPull_holds  : LevPull := levPull_of pullKer_holds
theorem etInj_holds  : EtInj := etInj_of objTri_holds levPull_holds
theorem ordKSE_holds (h3 : OrdGen) (h4 : QuotObj) : OrdKSE := ordKSE_of (corrBC_holds h4) (ordEmb_holds h3 h4) powExt_holds etInj_holds
theorem tjExF_holds (h1 : EsNorm) (h2 : EsGen) : TjExF := tjExF_of h1 h2 objTri_holds pullIsog_holds pullKer_holds
theorem uKerW_holds  : UKerW := uKerW_of kerU_holds pullKer_holds
theorem idealSplit_holds  : IdealSplit := idealSplit_of
theorem levPush_holds  : LevPush := levPush_of idealSplit_holds
theorem tjEEx_holds  : TjEEx := tjEEx_of objTri_holds pulledEx_holds pullKer_holds uKerW_holds levPull_holds levPush_holds
theorem congKS_holds (h1 : EsNorm) (h2 : EsGen) (h3 : OrdGen) (h4 : QuotObj) : CongKS :=
  congKS_of (tjExF_holds h1 h2) tjEEx_holds (ordKSE_holds h3 h4) ptIdOfOrd_holds

end UpperTheory.Gal.crystallineComparison.Mod
end
