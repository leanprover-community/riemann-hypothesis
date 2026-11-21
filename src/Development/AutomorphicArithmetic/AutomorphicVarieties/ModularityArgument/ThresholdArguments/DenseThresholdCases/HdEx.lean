import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HdEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.TypeEx
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ExistsIrreducibleTypeCharacters
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PTypeEx
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroGDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfTypeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroKIface
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.SubquotientSupport.TypeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPProdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPCuspSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.ExtraV
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GMain
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NeedCProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCJDefs
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacNeZero
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetFiniteLength2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Tensor2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPSuppProd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ThetaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LaArtin
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ReHecke

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
theorem nz_of_typeData_alt (h2 : SmoothRepIrreducibleSubcontainingVector) (h3 : SmoothRepMinimalSubrepresentation) (h4 : SchurInjectiveFromIrreducible) (TD : _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt) : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes := by
  intro E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨J, lam, m, V0, v0, -, -, hsm, hv0, hvec, himp, hemb⟩ := TD E Ω A w h rc hrc n χ ho
  have : CompactSpace (GlobalTheory.LFun.KGL w n) :=
    isCompact_iff_compactSpace.1 (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  obtain ⟨S, p, hS0, hSst, hSirr, hpS, hpid, hpeq, hpv⟩ := h2 _ m V0 hsm v0 hv0
  obtain ⟨d, ξ, ι, hι, hrange, hint, hirr, hsmξ⟩ := h3 _ m V0 hsm S hS0 hSst hSirr
  refine ⟨d, ξ, hirr, hsmξ, fun π => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg0, hg⟩
    have hgi : Function.Injective g := h4 _ d ξ hirr π.V (π.ρ.comp (GlobalTheory.LFun.KGL w n).subtype) g hg0 hg
    obtain ⟨z, hz⟩ : p v0 ∈ LinearMap.range ι := hrange ▸ hpS v0
    refine himp π ⟨g z, fun h0 => hpv ?_, fun j => ?_⟩
    · have : z = 0 := hgi (h0.trans (map_zero g).symm)
      rw [← hz, this, map_zero]
    · have hξz : ξ (j : ↥(GlobalTheory.LFun.KGL w n)) z = ((lam j : ℂˣ) : ℂ) • z := hι (by
        rw [← hint, hz, ← hpeq, hvec j, map_smul, ← hz, map_smul])
      have := hg (j : ↥(GlobalTheory.LFun.KGL w n)) z
      rw [hξz, map_smul] at this
      exact this.symm
  · intro hc
    obtain ⟨f, hf, hfeq⟩ := hemb π hc
    obtain ⟨z, hz⟩ : ∃ z : Fin d → ℂ, z ≠ 0 := by
      by_contra hne
      push Not at hne
      have : S = ⊥ := by
        rw [← hrange, LinearMap.range_eq_bot]
        exact LinearMap.ext fun v => by rw [hne v, map_zero, LinearMap.zero_apply]
      exact hS0 this
    refine ⟨f ∘ₗ ι, fun h0 => hz (hι (hf ?_)), fun k v => ?_⟩
    · rw [map_zero, map_zero]
      exact LinearMap.congr_fun h0 z
    · simp only [LinearMap.comp_apply]
      rw [← hint, hfeq]
end UpperTheory.NonzeroTypeTheory
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
abbrev _root_.UpperTheory.NonzeroTypeTheory.typeData_of_s_ty : Prop := ∀ (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct) (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia)
    (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp) (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp),
    _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt
end UpperTheory.NonzeroTypeTheory
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ UpperTheory.NonzeroTypeTheory UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win.T2
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}
  {rc : IrrGL (w.adicCompletion E) → WD h}
private theorem good_of_sph (x : IrrGL (w.adicCompletion E)) (hx : IsSpherical x.rep) : Good x := by
  obtain ⟨s, hs, h1⟩ := GlobalTheory.SphSupport.toral_of_isSpherical GlobalTheory.bernsteinZelevinskyFiniteness_holds _ x hx
  refine ⟨s, hs, fun y hy => Or.inl ?_⟩
  obtain ⟨χ, -, hχ, rfl⟩ := h1 y hy
  rfl
private theorem sph_of {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X) (hs : IsSmooth σ) (hi : σ.IsIrreducible)
    (hσ : IsSpherical σ) : IsSpherical (IrrGL.of σ hs hi).rep :=
  SphericalUnramified.isSpherical_of_equiv (IrrGL.equivOf σ hs hi) hσ
private theorem sphOfUnrV (H : UpperTheory.V.Z.Win.LawsV a ha ε rc) (d : ℕ) (v : WD h) (hv : v.unr) (hd : v.lpDim = d) :
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (σ : Representation ℂ (GL (Fin d) (w.adicCompletion E)) X)
      (hs : IsSmooth σ) (hi : σ.IsIrreducible), IsSpherical σ ∧ rc (IrrGL.of σ hs hi) = v := by
  subst hd
  obtain ⟨α, hα⟩ := GlobalTheory.LocLanglands.unr_eq_diag_inv E Ω A w h v hv
  obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
  have φ := equivRep π
  have hπ' : HasSatake (GlobalTheory.LocLanglands.cls π).rep α := ⟨IrrRep.irr _, SphericalUnramified.isSpherical_of_equiv φ hπ.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
  refine ⟨π.V, inferInstance, inferInstance, π.ρ, π.smooth, π.irr, hπ.2.1, ?_⟩
  exact (H.sat (GlobalTheory.LocLanglands.cls π) α hπ').trans hα.symm
private theorem prodRcV (L : UpperTheory.V.Z.Win.LawsV a ha ε rc) :
    ∀ (s N : ℕ) (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type) [∀ b, AddCommGroup (X b)]
      [∀ b, Module ℂ (X b)] (σ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b))
      (hs : ∀ b, IsSmooth (σ b)) (hi : ∀ b, (σ b).IsIrreducible)
      (hI : (multiProd (stdBlocks d hd) σ).IsIrreducible),
      rc (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI) =
        sumList (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b))) := by
  intro s
  induction s with
  | zero =>
    intro N d hd X _ _ σ hs hi hI
    have h0 : N = 0 := by simpa using hd.symm
    rw [List.ofFn_zero, sumList, List.foldr_nil]
    exact P_prodRc.wd_eq_lpZero ((L.dim (IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI)).trans h0)
  | succ s ih =>
    intro N d hd X _ _ σ hs hi hI
    obtain rfl : N = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨Φ⟩ := GlobalTheory.SmGL.MultiIrr.nonempty_prod₂_equiv_multiProd_succ d hd σ
    have hts : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => σ i.succ) :=
      isSmooth_parInd _ _
    have hti := GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ _ _ _ _ _ _ (σ 0) _ (multiProd (stdBlocks d hd) σ)
      (hs 0) (hi 0) hts hI ⟨Φ.symm⟩
    have key := L.prod (d 0) (∑ i : Fin s, d i.succ) ⟨X 0, σ 0, hs 0, hi 0⟩ ⟨_, _, hts, hti⟩
      ⟨_, multiProd (stdBlocks d hd) σ, isSmooth_parInd _ _, hI⟩ ⟨Φ.symm⟩
    refine key.trans ?_
    rw [List.ofFn_succ, sumList, List.foldr_cons]
    congr 1
    exact ih _ (fun i => d i.succ) rfl (fun i => X i.succ) (fun i => σ i.succ) (fun i => hs i.succ)
      (fun i => hi i.succ) hti
private theorem good_prod (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt) {s N : ℕ} (d : Fin s → ℕ) (hd : ∑ b, d b = N) (X : Fin s → Type)
    [∀ b, AddCommGroup (X b)] [∀ b, Module ℂ (X b)]
    (τ : ∀ b, Representation ℂ (GL (Fin (d b)) (w.adicCompletion E)) (X b)) (hs : ∀ b, IsSmooth (τ b))
    (hi : ∀ b, (τ b).IsIrreducible) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ) (hη : ∀ b, IsSmoothChar (η b))
    (hdet : ∀ b, HasDetVec (τ b) (η b)) (hI : (multiProd (stdBlocks d hd) τ).IsIrreducible) :
    Good (IrrGL.of (multiProd (stdBlocks d hd) τ) (isSmooth_parInd _ _) hI) := by
  choose μ hμ hcs using fun b => _root_.UpperTheory.TNZ.step_cuspSupp_alt hL _ (d b) (X b) (τ b) (hs b) (hi b) (η b) (hη b) (hdet b)
  have hS := GlobalTheory.LocGL.SupportRing.hasSupport_multiProd hL.zel hd τ hs hi
    (fun b => hasSupport_of_isCuspSupport (hcs b)) hI
  refine ⟨_, hS.of_equiv (IrrGL.equivOf _ _ _), fun y hy => Or.inl ?_⟩
  obtain ⟨c, -, hc⟩ := Multiset.mem_sum.1 hy
  obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hc
  rfl
private theorem gMainV (hLit : _root_.GlobalTheory.Mem.LiteralAutomorphy.LitLocAlt) (gi : ArtinInertiaProp) (H : UpperTheory.V.Z.Win.LawsV a ha ε rc)
    {s : ℕ} (d : Fin s → ℕ) (η : Fin s → (w.adicCompletion E)ˣ →* ℂˣ) (hη : ∀ b, IsSmoothChar (η b))
    (hdist : ∀ b c, b ≠ c → ∃ t : Ine (F := E) A, η b (a (ineIncl h t)) ≠ η c (a (ineIncl h t)))
    (x : IrrGL (w.adicCompletion E)) (hd : ∑ b, d b = x.1) :
    ((rc x).mono0 ∧ ∀ t : Ine (F := E) A,
        (rc x).charPol (ineIncl h t) = ∏ b, (X - C ((η b (a (ineIncl h t)) : ℂˣ) : ℂ)) ^ d b) ↔
      IsTwSphProd x.rep d hd η := by
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := step_isotypic E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := step_scalarInertia E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => sphOfUnrV H (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    have hs' : ∀ b, IsSmooth (twist (σ b) (detChar (Fin (d b)) (η b))) :=
      fun b => isSmooth_twist (hs b) (hη b).detChar
    have hi' : ∀ b, (twist (σ b) (detChar (Fin (d b)) (η b))).IsIrreducible := fun b => isIrreducible_twist (hi b) _
    have hrc' : ∀ b, rc (IrrGL.of (twist (σ b) (detChar (Fin (d b)) (η b))) (hs' b) (hi' b)) =
        (rc (IrrGL.of (σ b) (hs b) (hi b))).lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := fun b => by
      rw [← IrrGL.tw_of (hχ := hη b), H.twist _ _ _ (good_of_sph _ (sph_of _ _ _ (hsph b))), H.one]
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (step_detVec _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (gi E Ω A w h a ha).1 t, ht⟩
    have hI := _root_.UpperTheory.TNZ.step_prodIrr_alt _root_.UpperTheory.TNZ.step_cuspSupp_alt hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi'
      η hη hdet hdistU
    have hrcP := prodRcV H s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (H.inj x _ (good_prod hLit d hd Xs _ hs' hi' η hη hdet hI) heq.symm).symm.trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      have hs' : IsSmooth (twist (σ b) (detChar (Fin (d b)) (η b)⁻¹)) := isSmooth_twist (hs b) (hη b).inv.detChar
      have hi' : (twist (σ b) (detChar (Fin (d b)) (η b)⁻¹)).IsIrreducible := isIrreducible_twist (hi b) _
      have hsp := sph_of _ hs' hi' ((step_detVec _ (d b) (Xs b) (σ b) (η b)).2 (hdet b))
      refine ⟨_, (H.sph _).1 hsp, H.dim _, ?_⟩
      rw [P_untwistRc.of_eq_tw (σ b) (hs b) (hi b) (η b) (hη b), H.twist _ _ _ (good_of_sph _ hsp), H.one]
    choose u hu hud hur using hfac
    have hl := step_sumList E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := prodRcV H s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (step_unrTwist E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (step_unrTwist E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl
end UpperTheory.V.Z.Win.T2
theorem UpperTheory.V.Z.Win.T2.typeData_alt :
    _root_.UpperTheory.NonzeroTypeTheory.typeData_of_s_ty := by
  intro P a1 a3 a4 a5 a6 a7 gm ge gi cm cp gr E Ω _ _ _ _ _ A w h rc hrc n χ ho
  obtain ⟨a, ha, ε, H⟩ := _root_.UpperTheory.V.Z.Win.toV' hrc
  obtain ⟨μ, hμs, hμ⟩ := a1 E Ω A w h a ha n χ ho
  obtain ⟨G, σ, hG⟩ := gr (w.adicCompletion E) n μ hμs
  have hcond : ∀ π : SmIrr (GL (Fin n) (w.adicCompletion E)), Cond h rc χ ho π ↔ IsTwSphProd π.ρ G.d G.hd G.μ := by
    intro π
    have e := gMainV P.loc gi H G.d G.μ G.smooth (a6 gi E Ω A w h a ha n G)
      (IrrGL.of π.ρ π.smooth π.irred) G.hd
    rw [← a5 _ n π.V π.ρ π.smooth π.irred G.s G.d G.hd G.μ, ← e]
    unfold Cond
    refine and_congr_right fun _ => forall_congr' fun s => ?_
    rw [a3 E Ω A w h a ha n χ ho μ hμ G σ hG s]
  obtain ⟨hJK, h1J, hmul, hinv, hne, hKCo, h1KC, hKCJ, hlam1, hst, hfin, hv0m, hv00, hv0e⟩ := cp (w.adicCompletion E) n G
  have hK : KO (w.adicCompletion E) (Fin n) = GlobalTheory.LFun.KGL w n := SphCompletion.KO_completion w n
  rw [← hK]
  let J : Subgroup ↥(KO (w.adicCompletion E) (Fin n)) :=
    { carrier := {j | (j : GL (Fin n) (w.adicCompletion E)) ∈ G.JSet}
      mul_mem' := fun {x y} hx hy => (hmul _ hx _ hy).1
      one_mem' := h1J
      inv_mem' := fun {x} hx => hinv _ hx }
  let lam : ↥J →* ℂˣ :=
    { toFun := fun j => Units.mk0 (G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E))) (hne _ j.2)
      map_one' := Units.ext (by simpa using hlam1 1 h1KC)
      map_mul' := fun x y => Units.ext (by simpa using (hmul _ x.2 _ y.2).2) }
  have hlamv : ∀ j : ↥J, ((lam j : ℂˣ) : ℂ) = G.lam ((j : ↥(KO (w.adicCompletion E) (Fin n))) : GL (Fin n) (w.adicCompletion E)) :=
    fun _ => rfl
  obtain ⟨m, V0, e, he, hre, heq, hsm⟩ := a4 _ G.V0sp hfin (fun φ hφ k' => hst φ hφ k') (a7 _ n G hKCo h1KC)
  obtain ⟨v0, hv0⟩ : G.v0 ∈ LinearMap.range e := hre ▸ hv0m
  have hU : IsOpen {j : ↥(KO (w.adicCompletion E) (Fin n)) | (j : GL (Fin n) (w.adicCompletion E)) ∈ KC _ n G.lev} :=
    hKCo.preimage continuous_subtype_val
  refine ⟨J, lam, m, V0, v0, ?_, ?_, hsm, fun h0 => hv00 (by rw [← hv0, h0, map_zero]), fun j => he ?_, ?_, ?_⟩
  · exact Subgroup.isOpen_of_mem_nhds J (Filter.mem_of_superset (hU.mem_nhds (show (1 : ↥(KO (w.adicCompletion E) (Fin n))) ∈ _ from h1KC)) fun j hj => hKCJ hj)
  · exact Subgroup.isOpen_of_mem_nhds lam.ker (Filter.mem_of_superset
      ((hU.preimage continuous_subtype_val).mem_nhds (show (1 : ↥J) ∈ _ from h1KC)) fun j hj => MonoidHom.mem_ker.2 (Units.ext (by
        rw [hlamv]; exact hlam1 _ hj)))
  · rw [heq, hv0, hv0e _ j.2, map_smul, hv0, hlamv]
  · rintro π ⟨x, hx, hxj⟩
    rw [hcond]
    refine cm P _ n G π.V π.ρ π.smooth π.irred ⟨x, hx, fun g hg => ?_⟩
    have := hxj ⟨⟨g, hJK hg⟩, hg⟩
    rwa [hlamv] at this
  · intro π hc
    rw [hcond] at hc
    obtain ⟨f, hf, hfeq⟩ := ge _ n G π.V π.ρ hc
    let e' : (Fin m → ℂ) →ₗ[ℂ] ↥G.V0sp := LinearMap.codRestrict G.V0sp e fun v => hre ▸ LinearMap.mem_range_self e v
    refine ⟨f ∘ₗ e', hf.comp fun v v' hvv => he (congrArg Subtype.val hvv), fun κ v => ?_⟩
    exact hfeq κ (e' v) (e' (V0 κ v)) (heq κ v)
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
theorem nz_of_steps_alt (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (k2 : SmoothRepIrreducibleSubcontainingVector) (k3 : SmoothRepMinimalSubrepresentation) (k4 : SchurInjectiveFromIrreducible) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct)
    (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia) (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp)
    (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp) : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes :=
  _root_.UpperTheory.NonzeroTypeTheory.nz_of_typeData_alt k2 k3 k4 (_root_.UpperTheory.V.Z.Win.T2.typeData_alt P a1 a3 a4 a5 a6 a7 gm ge gi cm cp gr)
end UpperTheory.NonzeroTypeTheory
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TNZ
theorem gMain_alt (h1 : DeterminantVectorProp) (h2 : UnramifiedTwistProp) (h3 : SumOverListProp) (h4a : IsotypicComponentProp)
    (h4b : ScalarOnInertiaProp) (h5 : SphericalOfUnramifiedProp) (h5' : SphericalUnramifiedProp) (h6 : TwistRestrictionProp) (h6' : UntwistRestrictionProp)
    (h7 : ProductRestrictionProp) (h8a : _root_.UpperTheory.TNZ.Step_cuspSupp_alt) (h8b : _root_.UpperTheory.TNZ.Step_prodIrr_alt) (h9 : ArtinInertiaProp) : _root_.UpperTheory.TNZ.GMainAlt := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL hLit s d η hη hdist x hd
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := h4a E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := h4b E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => h5 E Ω A w h a ha ε rc hL (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    choose hs' hi' hrc' using fun b => h6 E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (h1 _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (h9 E Ω A w h a ha).1 t, ht⟩
    have hI := h8b h8a hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' η hη hdet hdistU
    have hrcP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (hL.bij.1 heq).trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨hs', hi', hr⟩ := h6' E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
      exact ⟨_, h5' E Ω A w h a ha ε rc hL (d b) (Xs b) _ hs' hi' ((h1 _ (d b) (Xs b) (σ b) (η b)).2 (hdet b)),
        hL.dim _, hr⟩
    choose u hu hud hur using hfac
    have hl := h3 E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (h2 E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (h2 E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl
end UpperTheory.TNZ
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
def Step_jacProd_alt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible →
    (∃ y : Jacquet π (unipRad k G.e), y ≠ 0 ∧ ∀ m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)), jacU G.e π m y = G.eta m • y) →
    IsTwSphProd π G.d G.hd G.μ
def CMainForAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → (∃ x : V, x ≠ 0 ∧ x ∈ G.Eig π) → IsTwSphProd π G.d G.hd G.μ
end Grp
end UpperTheory.TNZ
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem cMain_alt (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k)) (hlL : LeviSubgroupRestriction) (hjI : G.JacquetImageProp) (hjP : G.Step_jacProd_alt) : G.CMainForAlt := by
  intro L V _ _ π hs hirr ⟨x, hx0, hx⟩
  refine hjP L V π hs hirr ⟨_, G.jac_ne_zero hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp
    hjK hTI hun π hs x hx0 hx, fun m hm => hjI hlL hJone V π x hx m hm⟩
end Grp
end UpperTheory.TNZ
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem jacProd_of_alt (hjF : G.Step_jacFin_alt) (hsub : G.SubquotientProp) (hten : G.Step_tensor_alt) (hsupp : G.Step_suppProd_alt) :
    G.Step_jacProd_alt := by
  intro L V _ _ π hs hirr hy
  obtain ⟨hsm, hfl⟩ := hjF L V π hs hirr
  obtain ⟨X, _, _, σ, hσs, hσi, hsq, hση⟩ := hsub _ (jacU G.e π) hsm hfl hy
  obtain ⟨Y, _, _, τ, hτs, hτi, hτd, ⟨eqv⟩⟩ := hten L X σ hσs hσi hση
  refine hsupp L V π hs hirr Y τ hτs hτi hτd ?_
  obtain ⟨S, f, hf⟩ := hsq
  exact ⟨S, (eqv.toIntertwiningMap).comp f, eqv.toLinearEquiv.surjective.comp hf⟩
end Grp
def CStepsAlt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Grp.CompactConductorBasicProp (k := k) ∧ Grp.UniformizerProp (k := k) ∧ Grp.ExistsGroupElementProp (k := k) ∧ ∀ (n : ℕ) (G : Grp k n),
    G.CompactConductorBoundProp ∧ G.JacquetOneProp ∧ G.JacquetMultiplicativeProp ∧ G.JacquetInverseProp ∧ G.CompactOpenKernelProp ∧ G.ModulusOnUnitsProp ∧ G.ModulusMultiplicativeProp ∧
    G.LambdaMultiplicativeProp ∧ G.LambdaBasicProp ∧ G.LambdaUnipotentProp ∧ G.IwahoriDecompositionProp ∧ G.FixedSubspaceStableProp ∧ G.FixedSubspaceFiniteProp ∧ G.NonzeroLeviEigenvectorExists ∧
    G.ParabolicJacquetProp ∧ G.AnnihilationProp ∧ G.NonIntegralProp ∧ G.TorusCentreEigenProp ∧ G.TorusPowerProp ∧ G.JacquetKernelProp ∧ G.TorusCentreInjectiveProp ∧
    G.JacquetImageProp ∧ G.Step_jacFin_alt ∧ G.SubquotientProp ∧ G.Step_tensor_alt ∧ G.Step_suppProd_alt
open UpperTheory.NonzeroTypeTheory in
theorem twisted_spherical_product_of_irreducible_of_eigenvector (hC : _root_.UpperTheory.TNZ.CStepsAlt) (hlL : LeviSubgroupRestriction) (L : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ := by
  intro k _ _ _ _ n G V _ _ ρ hs hi hx
  obtain ⟨hcb, hun, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, hlU, hiw, -, -, -, hPJ, hkill, hni, hTE, hTp, hjK, hTI,
    hjI, hjF, hsub, hten, hsupp⟩ := hG n G
  exact G.cMain_alt hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp hjK hTI hun hlL hjI
    (G.jacProd_of_alt hjF hsub hten hsupp) L V ρ hs hi hx
open UpperTheory.NonzeroTypeTheory in
theorem need_CProps_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_CProps := by
  intro k _ _ _ _ n G
  obtain ⟨hcb, -, -, hG⟩ := hC k
  obtain ⟨hccB, hJone, hJmul, hJinv, hKC, hΔU, hΔM, hlM, hlB, -, -, hV0s, hV0f, hv0, -⟩ := hG n G
  have hK := hKC hccB G.lev
  have hlB' := hlB hccB
  have hlM' := hlM hcb hΔU hΔM hccB
  obtain ⟨h1, h2, h3⟩ := hv0 hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  refine ⟨fun g hg => hg.1, hJone.1, fun g hg g' hg' => ⟨hJmul hcb hccB g hg g' hg', hlM' g hg g' hg'⟩, hJinv hcb hccB,
    fun g _ => hlB'.2.1 g, hK.2.2.1, ?_, hK.2.2.2.2 le_rfl, hlB'.2.2, fun φ hφ k' => hV0s hccB hKC k' φ hφ, hV0f hccB hKC, h1, h2, h3⟩
  rw [← hK.1]
  exact (KCg k n G.lev).one_mem
open UpperTheory.NonzeroTypeTheory in
theorem need_Grp_alt (hC : _root_.UpperTheory.TNZ.CStepsAlt) : Need_Grp := by
  intro k _ _ _ _ n μ hμ
  obtain ⟨-, -, hex, -⟩ := hC k
  obtain ⟨G, σ, h⟩ := hex n μ hμ
  exact ⟨G, σ, fun i => (h i).symm⟩
end UpperTheory.TNZ
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
namespace JacquetFiniteLength₂
variable {n : ℕ} (G : Grp k n)
end JacquetFiniteLength₂
theorem step_jacFin_alt {n : ℕ} (G : Grp k n) : G.Step_jacFin_alt := by
  intro L V _ _ π hπ hirr
  exact ⟨isSmooth_jacU G.e hπ,
    JacquetFiniteLength₂.hasFiniteLength_jacU G L.loc.bz π hπ (hasFiniteLength_of_isIrreducible hirr)⟩
end Grp
end UpperTheory.TNZ
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct
open Module
namespace UpperTheory.TNZ.Grp.Tensor₂
section Contr
variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {Y : ι → Type} [∀ b, AddCommGroup (Y b)]
  [∀ b, Module ℂ (Y b)]
end Contr
end UpperTheory.TNZ.Grp.Tensor₂
namespace UpperTheory.TNZ.Grp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem step_tensor_alt {n : ℕ} (G : Grp k n) : G.Step_tensor_alt := by
  intro hN X _ _ σ hs hirr hη
  obtain ⟨y, hy0, hy⟩ := hη
  obtain ⟨s, ⟨E⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi hN.loc.bz k (Fin G.s)
    (fun a => Fin (G.d a)) { V := X, ρ := σ, smooth := hs, irr := hirr }
  refine ⟨fun a => (s a).V, fun a => inferInstance, fun a => inferInstance, fun a => (s a).ρ,
    fun a => (s a).smooth, fun a => (s a).irr, fun a => ?_, ⟨E⟩⟩
  have hE : ∀ m, E (σ m y) = piTensor (fun b => (s b).ρ) m (E y) := fun m =>
    LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' m) y
  have hEy : E y ≠ 0 := (map_ne_zero_iff E (EquivLike.injective E)).2 hy0
  have hK : ∀ g ∈ (KO k (Fin (G.d a)) : Set (GL (Fin (G.d a)) k)),
      piTensor (fun b => (s b).ρ) (Pi.mulSingle a g) (E y) =
        ((G.μ a (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • E y := by
    intro g hg
    have hm : (Pi.mulSingle a g : Levi k fun b : Fin G.s => Fin (G.d b)) ∈
        leviK k (m := fun b : Fin G.s => Fin (G.d b)) := by
      rw [leviK, Subgroup.mem_pi]
      intro b _
      by_cases hb : b = a
      · subst hb
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne hb]
        exact one_mem _
    rw [← hE, hy _ hm, map_smul]
    congr 1
    rw [eta, Finset.prod_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, map_one, map_one, Units.val_one]
    · intro h
      exact absurd (Finset.mem_univ a) h
  exact Tensor₂.exists_factor_vec (fun b => (s b).ρ) a (E y) hEy _ _ hK
end UpperTheory.TNZ.Grp
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel UpperTheory.TNZ
namespace UpperTheory.NonzeroTypeTheory
theorem cSteps_all_alt
     :
    _root_.UpperTheory.TNZ.CStepsAlt := by
  intro k _ _ _ _
  exact ⟨Grp.step_ccBasic (k := k), Grp.step_unif (k := k), Grp.step_exGrp (k := k), fun n G => ⟨Grp.step_ccBound (G := G), Grp.step_Jone (G := G), Grp.step_Jmul (G := G), Grp.step_Jinv (G := G), Grp.step_KC (G := G), Grp.step_DUnit (G := G), Grp.step_DMul (G := G), Grp.step_lamMul (G := G), Grp.step_lamBasic (G := G), Grp.step_lamUnip (G := G), Grp.step_iwahori (G := G), Grp.step_V0stable (G := G), Grp.step_V0fin (G := G), Grp.leviEigenvector_holds (G := G), Grp.step_PJ (G := G), Grp.step_kill (G := G), Grp.step_nonint (G := G), Grp.step_TzE (G := G), Grp.step_Tpow (G := G), Grp.step_jacKer (G := G), Grp.step_TzInj (G := G), Grp.step_jacImage (G := G), _root_.UpperTheory.TNZ.Grp.step_jacFin_alt (G := G), Grp.step_subq (G := G), _root_.UpperTheory.TNZ.Grp.step_tensor_alt (G := G), _root_.UpperTheory.TNZ.Grp.step_suppProd_alt (G := G)⟩⟩
theorem nonzero_types_of_literal_automorphy (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis)
     : _root_.UpperTheory.NonzeroTypeTheory.NonzeroTypes :=
  _root_.UpperTheory.NonzeroTypeTheory.nz_of_steps_alt P invariantComplement_holds minimalSubrepresentation_holds schurInjective_holds artinTransferDecomposition_holds localArtinCharacterProduct_holds finiteDimensionalTranslation_holds twistedSphericalRepresentative_holds distinctOnInertia_holds smoothVectorsFixed_holds
    (_root_.UpperTheory.TNZ.gMain_alt step_detVec step_unrTwist step_sumList step_isotypic step_scalarInertia step_sphOfUnr step_sphUnr step_twistRc
      step_untwistRc step_prodRc _root_.UpperTheory.TNZ.step_cuspSupp_alt _root_.UpperTheory.TNZ.step_prodIrr_alt step_artinIne)
    (gEmb step_tensorVec step_lamLevi step_parabKO step_indDetK step_indExt) step_artinIne
    (fun L => _root_.UpperTheory.TNZ.twisted_spherical_product_of_irreducible_of_eigenvector (_root_.UpperTheory.NonzeroTypeTheory.cSteps_all_alt ) step_lamLevi L) (_root_.UpperTheory.TNZ.need_CProps_alt (_root_.UpperTheory.NonzeroTypeTheory.cSteps_all_alt ))
    (_root_.UpperTheory.TNZ.need_Grp_alt (_root_.UpperTheory.NonzeroTypeTheory.cSteps_all_alt ))
end UpperTheory.NonzeroTypeTheory
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep' :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ :=
  fun P => _root_.UpperTheory.V.Z.Desc.P.exists_integral_type_for_residual_rep P (_root_.UpperTheory.NonzeroTypeTheory.nonzero_types_of_literal_automorphy P )
end
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Hi.exists_integral_type_for_residual_rep :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀ :=
  fun P => _root_.UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep' P.litN
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
section SlopeTestRemainingChoices
private theorem th_Uc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (W : Subgroup kˣ) (hW : IsOpen (W : Set kˣ)) : ∃ c, ∀ d, c ≤ d → Uc k d ≤ W := by
  obtain ⟨c, hc⟩ := (glBridge k 1 ℂ 1).2.2.2.1 (W.comap Matrix.GeneralLinearGroup.det)
    (hW.preimage Matrix.GeneralLinearGroup.continuous_det)
  refine ⟨c, fun d hd => ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 : (u : 𝒪[k]) - 1 ∈ maximalIdeal 𝒪[k] ^ c :=
    Ideal.pow_le_pow_right hd (Ideal.Quotient.eq.1 (congrArg Units.val hu))
  have h2 := hc (x := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin 1) fun _ => u))
    ⟨_, by
      ext i j
      rw [Subsingleton.elim j i]
      simpa [val_diagT] using Ideal.Quotient.eq.2 h1, rfl⟩
  convert Subgroup.mem_comap.1 h2 using 1
  ext
  simp [val_diagT]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}
private theorem th_fin (ha : IsLocalArtin h a) {B : Type} [CommGroup B] [Finite B] (f : Weil h →* B)
    (hf : GlobalTheory.WeilDeligne.IsSmooth f) : ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → f σ = 1 := by
  choose φ hφ using fun b : {b : B // b ≠ 1} => CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity B ℂ b.2
  choose χ hχ e using fun b => ha.factor ((φ b).comp f) (hf.of_le fun σ hσ => by simp [hσ])
  obtain ⟨c, hc⟩ := th_Uc (⨅ b, (χ b).ker) (by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hχ)
  refine ⟨c, fun d hd σ hσ => by_contra fun h1 => hφ ⟨_, h1⟩ ?_⟩
  exact (DFunLike.congr_fun (e ⟨_, h1⟩) σ).trans (Subgroup.mem_iInf.1 (hc d hd hσ) _)
private theorem th_char (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ, (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → χ (a x) = ψ g) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  let f := ψ.comp (Subgroup.inclusion (Weil_le_Dec h))
  have key : ∀ N, ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → (f σ : R) - 1 ∈ maximalIdeal R ^ N := fun N => by
    haveI : Finite (R ⧸ maximalIdeal R) := IsCNL.finite
    haveI : Finite (R ⧸ maximalIdeal R ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    obtain ⟨c, hc⟩ := th_fin ha ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom).comp f) (by
      have := ((hψ N).comp_continuous (f := fun σ : Ine (F := F) A => Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ))
        (continuous_subtype_val.subtype_mk _)) {1}
      exact (congrArg IsOpen (Set.ext fun σ => Units.ext_iff)).mpr this)
    exact ⟨c, fun d hd σ hσ => Ideal.Quotient.eq.1 (congrArg Units.val (hc d hd σ hσ))⟩
  have hk : a.ker ≤ f.ker := fun σ hσ => by
    refine Units.ext (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R).2 fun N => ?_)
    obtain ⟨c, hc⟩ := key N
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact hc c le_rfl σ (by rw [show a σ = 1 from hσ]; exact one_mem _)
  have hf : ∀ x, a.liftOfSurjective ha.surj ⟨f, hk⟩ (a x) = f x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply a _ _ ⟨f, hk⟩ x
  refine ⟨a.liftOfSurjective ha.surj ⟨f, hk⟩, fun x g e => (hf x).trans (congrArg ψ (Subtype.ext e.symm)), fun N => ?_⟩
  obtain ⟨c, hc⟩ := key N
  refine ⟨c, fun d hd y hy => ?_⟩
  obtain ⟨σ, rfl⟩ := ha.surj y
  rw [hf]
  exact hc d hd σ hy
private theorem th_eps {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R] {l : ℕ} [Fact l.Prime]
    (j : ℤ_[l] →+* R) [IsLocalHom j] {e : Γ → ℤ_[l]} (he : Continuous e) :
    Alg.AdicCont (maximalIdeal R) fun g => j (e g) := fun N => by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have ho : IsOpen {y : Γ | ‖e y - e x‖ < (l : ℝ) ^ (-(N : ℤ))} :=
    isOpen_lt (by fun_prop) continuous_const
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  filter_upwards [ho.mem_nhds (by simpa using pow_pos hl N)] with y hy
  refine Ideal.Quotient.eq.2 ?_
  have h1 : e y - e x ∈ maximalIdeal ℤ_[l] ^ N := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hy.le
  rw [← map_sub]
  refine Ideal.pow_right_mono (I := (maximalIdeal ℤ_[l]).map j) ?_ N ?_
  · exact Ideal.map_le_iff_le_comap.2 fun z hz => map_nonunit j z hz
  · rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h1
private theorem th_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (i : ℕ) : Alg.AdicCont I fun x => f x * g x ^ i := fun N => by
  simp only [map_mul, map_pow]
  exact (hf N).mul ((hg N).comp (· ^ i))
private theorem th_diag (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∃ D : (glIwa k n).T →* (Fin n → kˣ), (∀ i y, D (eT k n i y) = Pi.mulSingle i (y : kˣ)) ∧
      ∀ c (t : (glIwa k n).T), (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → ∀ i, D t i ∈ Uc k (c + 1) := by
  have hi : Function.Injective (diagT k (Fin n)) := fun s t e => by
    have := congrArg Units.val e
    rw [val_diagT, val_diagT] at this
    exact funext fun i => Units.ext (congrFun (Matrix.diagonal_injective this) i)
  let D : (glIwa k n).T →* (Fin n → kˣ) :=
    (MonoidHom.ofInjective hi).symm.toMonoidHom.comp (Subgroup.inclusion (glIwa k n).T_le)
  have hD : ∀ t, diagT k (Fin n) (D t) = t := fun t => MonoidHom.apply_ofInjective_symm hi _
  refine ⟨D, fun i y => hi (hD _), fun c t ht i => ?_⟩
  obtain ⟨y, e, hy⟩ := (glBridge k n ℂ 1).2.2.2.2.2.2.2.2.2 t
  have e2 : D t = fun i => (y i : kˣ) := hi <| by
    rw [hD, e]
    show (List.ofFn (diagT k (Fin n) ∘ fun i => Pi.mulSingle i (y i : kˣ))).prod = _
    rw [← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]
  rw [e2]
  exact hy c ht i
private theorem th_char' (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ ε : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) (hε : Alg.AdicCont (maximalIdeal R) fun g => (ε g : R)) (i : ℕ) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ,
      (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → ψ g * ε g ^ i * χ (a x) = 1) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  obtain ⟨χ, h1, h2⟩ := th_char ha (ψ * ε ^ i)⁻¹ fun N => by
    refine (congrArg IsLocallyConstant (funext fun g => ?_)).mpr ((th_mul hψ hε i N).comp_continuous continuous_inv)
    refine congrArg (Ideal.Quotient.mk _) ?_
    simp only [MonoidHom.inv_apply, ← map_inv]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
  exact ⟨χ, fun x g e => by rw [h1 x g e]; exact mul_inv_cancel _, h2⟩
private theorem th_torus (n : ℕ) {V : Type} [Fintype V] (S : V → Plc F) {R : Type} [CommRing R] [IsLocalRing R]
    (χ : ∀ v, Fin n → ((S v).adicCompletion F)ˣ →* Rˣ)
    (hc : ∀ v i N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ v i y : R) - 1 ∈ maximalIdeal R ^ N) :
    ∃ θ : (iwS n S).T →* Rˣ, (∀ v i y, θ (eV n S v i y) = χ v i y) ∧ (iwS n S).ContChar θ := by
  classical
  choose D hD hDc using fun v => th_diag ((S v).adicCompletion F) n
  let p : ∀ v, (iwS n S).T →* (glIwa ((S v).adicCompletion F) n).T := fun v =>
    ((Pi.evalMonoidHom (fun v => GLw n (S v)) v).comp (iwS n S).T.subtype).codRestrict _ fun t => t.2 v trivial
  let θ : (iwS n S).T →* Rˣ := ∏ v, ∏ i, (χ v i).comp ((Pi.evalMonoidHom _ i).comp ((D v).comp (p v)))
  have hθ : ∀ t, θ t = ∏ v, ∏ i, χ v i (D v (p v t) i) := fun t => by
    simp only [θ, MonoidHom.finset_prod_apply]
    rfl
  refine ⟨θ, fun v i y => ?_, fun N => ?_⟩
  · have e : D v (p v (eV n S v i y)) = Pi.mulSingle i (y : ((S v).adicCompletion F)ˣ) :=
      (congrArg (D v) (Subtype.ext (Pi.mulSingle_eq_same (M := fun v => GLw n (S v)) _ _))).trans (hD v i y)
    rw [hθ, Finset.prod_eq_single v, Finset.prod_eq_single i]
    · rw [e, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [e, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
    · intro v' _ hv
      rw [show p v' (eV n S v i y) = 1 from Subtype.ext (Pi.mulSingle_eq_of_ne (M := fun v => GLw n (S v)) hv _)]
      simp
    · simp
  · choose d hd using fun x : V × Fin n => hc x.1 x.2 N
    refine ⟨Finset.univ.sup d, fun t ht => ?_⟩
    refine Ideal.Quotient.eq.1 ?_
    rw [hθ]
    simp only [Units.coe_prod, map_prod, map_one]
    refine Finset.prod_eq_one fun v _ => Finset.prod_eq_one fun i _ => ?_
    exact Ideal.Quotient.eq.2 (hd (v, i) _ ((Finset.le_sup (Finset.mem_univ _)).trans (Nat.le_succ _)) _
      (hDc v _ (p v t) (ht v trivial) i))
private theorem th_free {Γ Ga Gp A : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) {U : Subgroup X.Ub} (hU : X.Neat U) : X.Free τ θ U := by
  intro g γ u hu b hb e
  obtain ⟨rfl, rfl⟩ := hU g γ u hu b hb e
  refine ⟨one_mem _, one_mem _, ?_⟩
  rw [show (⟨1, one_mem _⟩ : X.I.T) = 1 from rfl, map_one, map_one]
  simp
end SlopeTestRemainingChoices
theorem UpperTheory.V.Hi.exists_theta_is_weight_of_lam_obj :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ (r : Resid V.frame c.O n) (Λ : LamObj r), ∃ θ : (hset Q τ₀).X.I.T →* Λ.Λˣ, IsTheta Q τ₀ Λ θ ∧ (hset Q τ₀).IsWt θ := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ r Λ
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (abelian₂.dvr_finite l c.O).2.2.2.2.2
  haveI : IsCNL Λ.Λ := IsCNL.ofCO c.O Λ.Λ
  choose ψ hψ hκ using Λ.inert
  have ha : ∀ v : V.frame.Vl, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := fun v =>
    Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' H (s.hw v.1))
  choose χ hχ hc using fun (v : V.frame.Vl) (i : Fin n) =>
    th_char' (ha v) (ψ v i) ((hset Q τ₀).epsV Λ.Λ v) (hψ v i).cont
      (th_eps ((algebraMap c.O Λ.Λ).comp (algebraMap ℤ_[l] c.O))
        (e := fun g : Dec (F := L) (s.A v.1) => (cycZ L Ω l g : ℤ_[l]))
        (Units.continuous_val.comp ((continuous_cycZ L Ω l).comp continuous_subtype_val))) i
  obtain ⟨θ, h1, h2⟩ := th_torus n (fun v : V.frame.Vl => s.w v.1) χ hc
  refine ⟨θ, fun v i x g hg y e1 e2 => ?_, h2, fun K => th_free _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩
  have e3 := hχ v i x g e1
  rw [e2, ← h1] at e3
  rw [hκ]
  exact e3
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem re_chi {n : ℕ} {k H : Type} [CommRing k] [Group H] (χ : Fin n → H →* kˣ) (g : H) :
    (W.GDet.ofRep (W.diagRep χ)).chi (MonoidAlgebra.single g 1) = ∏ i, (X - C (χ i g : k)) := by
  change (W.GDet.repAlg (W.diagRep χ) k[X] _).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [W.GDet.repAlg, W.diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]
private theorem re_hecke {k : Type} [Field k] {n q : ℕ} (hq : (q : k) ≠ 0) (P : k[X]) (hm : P.Monic)
    (hn : P.natDegree = n) : ∃ b : Fin n → k,
      P = heckePol n q fun j => if h : 0 < j ∧ j - 1 < n then b ⟨j - 1, h.2⟩ else 1 := by
  refine ⟨fun i => (-1) ^ (i + 1 : ℕ) * ((q : k) ^ ((i + 1) * i / 2 : ℕ))⁻¹ * P.coeff (n - (i + 1)), ?_⟩
  rw [Hi.heckePol, ← Finset.sum_range_reflect]
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow, hn]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj'
  rw [show j + d + 1 - 1 - j = d by omega, show j + d - d = j by omega]
  congr 2
  rcases d with _ | d
  · have := hm.coeff_natDegree
    rw [hn] at this
    simpa using this
  · rw [dif_pos ⟨by omega, by omega⟩]
    simp only [Nat.add_sub_cancel]
    have h1 : ((-1 : k) ^ (d + 1)) * (-1) ^ (d + 1) = 1 := by rw [← mul_pow]; simp
    have h2 : (q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq)
    linear_combination (-P.coeff j) * h2 - P.coeff j * ((q : k) ^ ((d + 1) * d / 2) * ((q : k) ^ ((d + 1) * d / 2))⁻¹) * h1
open scoped Pointwise in
private theorem re_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (χ : G E Ω →* M) {w : HeightOneSpectrum (𝓞 E)}
    (hχ : ∀ A, IsPlaceOver A w → ∀ s ∈ Ine (F := E) A, χ s = 1) {q : ℕ} {A B : ValuationSubring Ω}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) {σ τ : G E Ω} (hσ : IsFrob A q σ) (hτ : IsFrob B q τ) :
    χ τ = χ σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := E) hA hB
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  have h0 : IsFrob (F := E) A q (g⁻¹ * τ * g) := by
    refine ⟨?_, fun x hx => ?_⟩
    · have h1 : τ • g • A = g • A := hτ.1
      show (g⁻¹ * τ * g) • A = A
      rw [mul_smul, mul_smul, h1, inv_smul_smul]
    · have h1 := hτ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
        ← ValuationSubring.valuation_le_one_iff])
      have e : τ (g x) - g x ^ q = g ((g⁻¹ * τ * g) x - x ^ q) := by
        rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
      rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
        ← valuation_lt_one_iff'] at h1
  have h2 := hχ A hA _ (inv_mul_mem_Ine_of_isFrob hσ h0)
  rw [map_mul, map_inv, inv_mul_eq_one, map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul] at h2
  exact h2.symm
private theorem re_art {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) {M : Type} [CommGroup M]
    (ψ : Dec (F := E) A →* M) (hψ : IsOpen (ψ.ker : Set (Dec (F := E) A))) {x y : Weil h} (hxy : a x = a y) :
    ψ (Subgroup.inclusion (Weil_le_Dec h) x) = ψ (Subgroup.inclusion (Weil_le_Dec h) y) := by
  haveI : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : Finite (Dec (F := E) A ⧸ ψ.ker) := ψ.ker.quotient_finite_of_isOpen hψ
  haveI : Finite ψ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  let ι := Subgroup.inclusion (Weil_le_Dec h)
  by_contra hne
  have h1 : ψ.rangeRestrict (ι (x * y⁻¹)) ≠ 1 := fun h1 => hne (by
    have h2 : ψ (ι (x * y⁻¹)) = 1 := congrArg Subtype.val h1
    rwa [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h2)
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity ψ.range ℂ h1
  have hs : GlobalTheory.WeilDeligne.IsSmooth (ψ.comp ι) :=
    hψ.preimage (f := Subgroup.inclusion (Ine_le_Dec (F := E) A)) (continuous_inclusion (Ine_le_Dec (F := E) A))
  obtain ⟨χ, -, hχ⟩ := ha.factor (φ.comp (ψ.rangeRestrict.comp ι)) (hs.of_le fun σ hσ => by
    have : ψ.rangeRestrict (ι σ) = 1 := Subtype.ext hσ
    simp only [MonoidHom.comp_apply, this, map_one])
  apply hφ
  have h3 := DFunLike.congr_fun hχ (x * y⁻¹)
  rw [MonoidHom.comp_apply χ, map_mul a, map_inv a, hxy, mul_inv_cancel, map_one] at h3
  exact h3
private theorem re_eps {l : ℕ} [Fact l.Prime] (c : Coef l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (ε : H →* ℤ_[l]ˣ) (hε : Continuous ε) :
    IsOpen (((Units.map ((algebraMap c.O (ResidueField c.O)).comp (algebraMap ℤ_[l] c.O)).toMonoidHom).comp ε).ker : Set H) := by
  haveI : FaithfulSMul ℤ_[l] c.O := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    have h1 : algebraMap ℤ_[l] (PadicAlgCl l) x = algebraMap ℤ_[l] (PadicAlgCl l) y := congrArg Subtype.val hxy
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l], IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] _ y] at h1
    exact Subtype.ext ((algebraMap ℚ_[l] (PadicAlgCl l)).injective h1)
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := inferInstance
  have hc : Continuous fun g => ‖((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1‖ := by fun_prop
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
    (Filter.mem_of_superset ((isOpen_lt hc continuous_const (g := fun _ => 1)).mem_nhds (by simp)) fun g hg => ?_)
  have h1 : ((ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ maximalIdeal ℤ_[l] := PadicInt.mem_nonunits.2 hg
  have h2 := (residue_eq_zero_iff _).2 (map_nonunit (algebraMap ℤ_[l] c.O) _ h1)
  rw [map_sub, map_sub, map_one, map_one, sub_eq_zero] at h2
  exact Units.ext h2
theorem UpperTheory.V.Hi.exists_is_res_of_residual_rep_and_type :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ r : Resid V.frame c.O n, ∃ a, IsRes Q r τ₀ a := by
  intro hN l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r
  have H1 : ∀ w : (hset Q τ₀).Wp, ∃ b : Fin n → c.O, ∀ (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 →
      IsFrob B (normV w.1) σ → r.Dbar.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) =
      heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then residue c.O (b ⟨j - 1, h.2⟩) else 1 := by
    rintro ⟨w, hw, -⟩
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨φ, hφ⟩ := exists_isFrob hA
    have hl : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun hl => hw (V.sub (Or.inl (by
      change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
      rwa [map_natCast])))
    have hq : ((normV w : ℕ) : ResidueField c.O) ≠ 0 := by
      have h1 := (cycZ L Ω l φ).isUnit.map ((residue c.O).comp (algebraMap ℤ_[l] c.O))
      rw [cycZ_of_isFrob hl hA hφ, map_natCast] at h1
      exact h1.ne_zero
    have hI : ∀ B, IsPlaceOver B w → ∀ t ∈ Ine (F := L) B, V.pr t = 1 := fun B hB t ht => by
      refine Subtype.ext ((QuotientGroup.eq_one_iff _).2 ?_)
      refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
      simp only [Set.mem_iUnion]
      refine ⟨w.under (𝓞 (Lp L)), hw, B, fun x => ?_, ht.1, ht.2⟩
      rw [IsScalarTower.algebraMap_apply (Lp L) L Ω]
      exact hB (algebraMap (𝓞 (Lp L)) (𝓞 L) x)
    obtain ⟨b, hb⟩ := re_hecke (n := n) hq (∏ i, (X - C (r.chib i (V.pr φ⁻¹) : ResidueField c.O)))
      (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
      (by rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp)
    choose b' hb' using fun i => residue_surjective (b i)
    refine ⟨b', fun B σ hB hσ => ?_⟩
    simp only [hb']
    rw [← hb]
    refine (re_chi r.chib (V.pr σ⁻¹)).trans (Finset.prod_congr rfl fun i _ => ?_)
    have := re_frob ((r.chib i).comp V.pr) (fun B hB t ht =>
      (congrArg (r.chib i) (hI B hB t ht)).trans (map_one _)) hA hB hφ hσ
    rw [← inv_inj, ← map_inv, ← map_inv] at this
    exact congrArg (fun u : (ResidueField c.O)ˣ => X - C (u : ResidueField c.O)) this
  have H2 : ∀ (v : V.frame.Vl) (j : Fin n), ∃ b : c.O, ∀ (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)),
      (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, r.psib v i g * (hset Q τ₀).epsV (ResidueField c.O) v g ^ (i : ℕ) : (ResidueField c.O)ˣ) :
        ResidueField c.O) = residue c.O b := by
    intro v j
    have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' hN (s.hw v.1))
    obtain ⟨y, hy⟩ := ha.surj (unif _)
    obtain ⟨b, hb⟩ := residue_surjective (R := c.O) ((∏ i with i ≤ j,
      r.psib v i (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) *
      (hset Q τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) y) ^ (i : ℕ) :
        (ResidueField c.O)ˣ) : ResidueField c.O)
    refine ⟨b, fun x g hg hx => ?_⟩
    obtain rfl : g = Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) x := Subtype.ext hg
    rw [hb]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e1 := re_art ha (r.psib v i) (r.psib_open v i) (hx.trans hy.symm)
    have e2 := re_art ha ((hset Q τ₀).epsV (ResidueField c.O) v)
      (re_eps c ((cycZ L Ω l).comp (Dec (F := L) (s.A v.1)).subtype)
        ((continuous_cycZ L Ω l).comp continuous_subtype_val)) (hx.trans hy.symm)
    exact congrArg₂ (fun u t : (ResidueField c.O)ˣ => u * t ^ (i : ℕ)) e1 e2
  choose b1 hb1 using H1
  choose b2 hb2 using H2
  exact ⟨Sum.elim (fun x => b1 x.1 x.2) (fun x => b2 x.1 x.2), ⟨hb1, hb2⟩⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Hi.nonempty_unitaryHeckeData :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ Λ : LamObj r, Nonempty (_root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) := by
  intro P l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι Λ
  obtain ⟨m, τ₀, hτ⟩ := _root_.UpperTheory.V.Hi.exists_integral_type_for_residual_rep P l L Ω s n hn V Q c r ι
  obtain ⟨θ, hθ, hw⟩ := _root_.UpperTheory.V.Hi.exists_theta_is_weight_of_lam_obj P.litN l L Ω s n hn V Q c m τ₀ r Λ
  obtain ⟨a, ha⟩ := _root_.UpperTheory.V.Hi.exists_is_res_of_residual_rep_and_type P.litN l L Ω s n hn V Q c m τ₀ r
  exact ⟨⟨m, τ₀, hτ, θ, hθ, hw, a, ha⟩⟩
end
end
