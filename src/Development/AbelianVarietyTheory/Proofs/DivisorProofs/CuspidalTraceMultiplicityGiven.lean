import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteGroupActionPrincipalLevelFixedVector
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubrepWithGroupAlgebraFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleNotKilledByGoodProjectorSatisfiesH
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroupsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSplitFramePrincipalLevelFiniteGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PostOnGaLMemGoodPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAdelicIdentification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryConjDifferByInnerAutomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicLatticeIsometryEqProdLocalComponents
import Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspidalMultiplicityEqDiscreteSeriesModelMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermitiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleAdmissibleDecomposableCompEquiv

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.TypeVec

section Gen

theorem isIrreducible_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (τ : Representation ℂ H' X) (f : H →* H') (hf : Function.Surjective f) (hτ : τ.IsIrreducible) :
    Representation.IsIrreducible (τ.comp f) := by
  let e : Subrepresentation (τ.comp f : Representation ℂ H X) ≃o Subrepresentation τ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).2 hτ

def glMap {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    GL (Fin n) K →* GL (Fin m) K' :=
  (Units.map (Matrix.reindexAlgEquiv K' K' (finCongr h.symm)).toAlgHom.toRingHom.toMonoidHom).comp
    (Matrix.GeneralLinearGroup.map e.toRingHom)

theorem glMap_apply {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin n) K) (i j : Fin m) : (glMap e h g).1 i j = e (g.1 (Fin.cast h i) (Fin.cast h j)) := rfl

theorem glMap_symm {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n)
    (g : GL (Fin m) K') : glMap e h (glMap e.symm h.symm g) = g := by
  apply Units.ext
  ext i j
  rw [glMap_apply, glMap_apply]
  simp

theorem glMap_surjective {K K' : Type} [CommRing K] [CommRing K'] {m n : ℕ} (e : K ≃+* K') (h : m = n) :
    Function.Surjective (glMap e h) := fun g => ⟨glMap e.symm h.symm g, glMap_symm e h g⟩

theorem mem_fixed_iff {H X : Type} [Group H] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ H X}
    {K : Subgroup H} {x : X} : x ∈ GlobalTheory.PRep.fixed ρ K ↔ ∀ h : K, ρ h x = x := by
  show (∀ h : K, ρ h x = ((1 : K →* ℂˣ) h : ℂ) • x) ↔ _
  simp

end Gen

variable {D : D7}

def typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible) :
    TypeDataG V where
  S := S
  frame := s
  W := fun w => Fin (n (pl w)) → ℂ
  τ := fun w => (τ (pl w)).comp (glMap (ρv w) hr)
  irred := fun w => isIrreducible_comp _ _ (glMap_surjective _ _) (hτ (pl w))

theorem noFixed_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    (hne : S.Nonempty)
    (h : ∀ a, 0 < a → a < V.rank → ∃ v : S, ∀ y : Fin (n (pl v)) → ℂ,
      (∀ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF v.1) V.rank a, τ (pl v) (glMap (ρv v) hr g) y = y) → y = 0) :
    NoFixed (typeOf hr S pl s ρv n τ hτ) :=
  ⟨hne, h⟩

theorem hasTypeVec_typeOf {V : HSp D} {P : Finset (HeightOneSpectrum (𝓞 D.host.E))} {r : ℕ} (hr : r = V.rank)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ P) (s : ∀ v : S, SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1) (n : P → ℕ)
    (τ : ∀ PP : P, Representation ℂ (GL (Fin r) (kP PP.1)) (Fin (n PP) → ℂ)) (hτ : ∀ PP, (τ PP).IsIrreducible)
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) (x : W) (hx : x ≠ 0)
    (hoff : ∀ v ∉ S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x)
    (hon : ∀ v : S, x ∈ Submodule.span ℂ {y | ∃ φ : (Fin (n (pl v)) → ℂ) →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (τ (pl v) (glMap (ρv v) hr ((s v).red k)) z) = σ (locFin V v k) (φ z)) ∧
        y ∈ LinearMap.range φ}) :
    HasTypeVec (typeOf hr S pl s ρv n τ hτ) σ :=
  ⟨x, hx, hoff, hon⟩

set_option maxHeartbeats 1000000 in

theorem hasTypeVec_of_goodRep : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), IsAdmissible σ → GlobalTheory.CuspMult.IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ → ∃ T : TypeDataG (Yc D 0), NoFixed T ∧ HasTypeVec T σ := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F hF W _ _ σ _hadm hgood
  classical
  have hrk : (Yc D 0).rank = D.R.r := by rw [D.sp.Y_rank _ (min_le_right _ _)]; simp [Ranks.rankY]
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hlev := hF.core.lev
  obtain ⟨c0, hbase⟩ := hlev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hnc : ∀ PP ∈ (R.dat0 R.triv).Pg, ∀ PP' ∈ (R.dat0 R.triv).Pg, ¬ Formalism.IndefR.Lev.IsConjPl PP PP' := by
    intro PP hP PP' hP'
    obtain ⟨k, hk⟩ := (hlev.Pg PP).1 hP
    obtain ⟨k', hk'⟩ := (hlev.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_finiteGroupAction_principalLevelFixedVectors D (Yc D 0) (R.βY 0) (R.dat0 R.triv) (GlobalTheory.ProjectedLift.liftsExist_rows R hlev) W σ
  obtain ⟨v, hv0, hvK, κ, hκ, hve⟩ := hgood
  have hvmem : v ∈ GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))) :=
    mem_fixed_iff.2 fun k => hvK _ (Subgroup.mem_subgroupOf.1 k.2)
  haveI : Finite (G0 R.Pg D.R.r) := Finite.of_equiv G R.eG.toEquiv
  have hfix : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • ρ (R.eG g) ⟨v, hvmem⟩ = ⟨v, hvmem⟩ := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) hve
    rw [SetLike.val_smul, hρ (R.eG g) (κ g) (hκ g)]
  obtain ⟨U, hUfd, hUirr, y, hy0, hye⟩ := GlobalTheory.T.exists_irreducible_subrep_with_groupAlgebra_fixed _ _ _ ρ (fun g => R.eG g) _ ⟨v, hvmem⟩
    (fun h => hv0 (congrArg Subtype.val h)) hfix
  haveI := hUfd
  have hH := GlobalTheory.T.irreducible_not_killed_by_good_projector_satisfies_H hGC R F hF U.toSubmodule U.toRepresentation hUirr ⟨y, hy0, hye⟩
  choose n τ hτ hrest using GlobalTheory.T.isotypic_factor_of_isIrreducible_pi_finite_groups (↥R.Pg) (fun PP => GL (Fin D.R.r) (kP PP.1)) U.toSubmodule U.toRepresentation hUirr
  obtain ⟨a, S, pl, s, ρv, hoff, hon⟩ : ∃ (a : GfC (Yc D 0)) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (pl : S ≃ R.Pg)
      (s : ∀ v : S, SplitAt D.sp.cm.sig (Yc D 0).gram (frameLat (Yc D 0)) v) (ρv : ∀ v : S, ResF v.1 ≃+* kP (pl v).1),
      (∀ v ∉ S, ∀ k ∈ Kv (Yc D 0) v, ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∈
        levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))) ∧
      ∀ (v : S) (k : Kv (Yc D 0) v), ∃ g0 : G0 R.Pg D.R.r, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) g0
          ((a * locFin (Yc D 0) v k * a⁻¹ : GfC (Yc D 0)) : GA D (Yc D 0)) ∧
        (∀ PP, PP ≠ pl v → g0 PP = 1) ∧
        ∀ i j : Fin D.R.r, (g0 (pl v)).1 i j = ρv v (((s v).red k).1 (i.cast hrk.symm) (j.cast hrk.symm)) :=
    GlobalTheory.T.exists_splitFrame_principalLevel_finiteGroup D (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hrk.symm hbase rfl hnc

  let yW : W := (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)
  have hyK : ∀ h : ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))), σ h yW = yW := mem_fixed_iff.1 (y : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).2

  have hcomm : ∀ (l : GfC (Yc D 0)) (q : W), σ a⁻¹ (σ (a * l * a⁻¹) q) = σ l (σ a⁻¹ q) := by
    intro l q
    have e1 : σ a⁻¹ * σ (a * l * a⁻¹) = σ l * σ a⁻¹ := by
      rw [← map_mul, ← map_mul, show a⁻¹ * (a * l * a⁻¹) = l * a⁻¹ by group]
    exact congrArg (fun f : Module.End ℂ W => f q) e1
  have hconj : ∀ l : GfC (Yc D 0), σ (a * l * a⁻¹) yW = yW → σ l (σ a⁻¹ yW) = σ a⁻¹ yW :=
    fun l hl => (hcomm l yW).symm.trans (congrArg (σ a⁻¹) hl)
  refine ⟨typeOf hrk.symm S pl s ρv n τ hτ, noFixed_typeOf _ _ _ _ _ _ _ _ ?_ ?_,
    hasTypeVec_typeOf _ _ _ _ _ _ _ _ σ (σ a⁻¹ yW) ?_ ?_ ?_⟩
  · obtain ⟨PP, -⟩ := hH 1 one_pos (by omega)
    exact ⟨(pl.symm PP).1, (pl.symm PP).2⟩
  · intro b hb hbr
    obtain ⟨PP, hPP⟩ := hH b hb (lt_of_lt_of_eq hbr hrk)
    refine ⟨pl.symm PP, fun z hz => ?_⟩
    obtain ⟨⟨φ, hφi, hφ⟩, -⟩ := hrest (pl (pl.symm PP))
    have hpl : pl (pl.symm PP) = PP := pl.apply_symm_apply PP
    rw [← hpl] at hPP
    apply hφi
    refine Eq.trans ?_ (map_zero φ).symm
    apply hPP
    rintro u ⟨hu1, hu2⟩
    have e1 := hφ (u (pl (pl.symm PP))) z
    have hmem : glMap (ρv (pl.symm PP)).symm hrk (u (pl (pl.symm PP))) ∈ GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock (ResF (pl.symm PP).1) (Yc D 0).rank b := by
      intro i j hij
      rw [glMap_apply]
      have hent : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) =
          (1 : Matrix (Fin D.R.r) (Fin D.R.r) (kP (pl (pl.symm PP)).1)) (Fin.cast hrk i) (Fin.cast hrk j) := by
        by_contra hne
        exact hij (hu2 _ _ hne)
      by_cases hij' : i = j
      · subst hij'
        have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk i) = 1 := by simpa using hent
        simp only [h1, map_one, Matrix.one_apply_eq]
      · have h1 : (u (pl (pl.symm PP))).1 (Fin.cast hrk i) (Fin.cast hrk j) = 0 := by
          rw [hent, Matrix.one_apply_ne (fun h => hij' (Fin.cast_injective hrk h))]
        simp only [h1, map_zero, Matrix.one_apply_ne hij']
    have h2 := hz _ hmem
    rw [glMap_symm] at h2
    refine Eq.trans ?_ (congrArg φ h2)
    refine Eq.trans ?_ e1.symm
    refine congrArg (fun g => U.toRepresentation g (φ z)) ?_
    funext P'
    by_cases h : P' = pl (pl.symm PP)
    · subst h
      exact (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).symm
    · exact (hu1 P' h).trans (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) h _).symm
  · intro h0
    apply hy0
    have h1 : yW = 0 := by
      have := congrArg (σ a) h0
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, map_zero] at this
    exact Subtype.ext (Subtype.ext h1)
  · intro w hw k hk
    exact hconj _ (hyK ⟨_, Subgroup.mem_subgroupOf.2 (hoff w hw k hk)⟩)
  · intro w
    obtain ⟨-, hsp⟩ := hrest (pl w)
    have hkey : ∀ (k : Kv (Yc D 0) w) (q : U.toSubmodule),
        σ a⁻¹ ((((U.toRepresentation (Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k))) q) :
          U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) =
          σ (locFin (Yc D 0) w k) (σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) := by
      intro k q
      have h2 := hon w k
      have hlift := h2.choose_spec.1
      have hone := h2.choose_spec.2.1
      have hent := h2.choose_spec.2.2
      have hg0 : Pi.mulSingle (pl w) (glMap (ρv w) hrk.symm ((s w).red k)) = h2.choose := by
        funext P'
        by_cases hP : P' = pl w
        · subst hP
          refine (Pi.mulSingle_eq_same (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) _ _).trans ?_
          apply Units.ext
          ext i j
          exact (glMap_apply _ _ _ i j).trans (hent i j).symm
        · exact (Pi.mulSingle_eq_of_ne (M := fun PP : R.Pg => GL (Fin D.R.r) (kP PP.1)) hP _).trans (hone P' hP).symm
      have e2 := hρ _ (a * locFin (Yc D 0) w k * a⁻¹) hlift (q : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0))))
      exact (congrArg (fun g => σ a⁻¹ ((((U.toRepresentation g q) : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W)) hg0).trans
        ((congrArg (σ a⁻¹) e2).trans (hcomm _ _))
    have hy := Submodule.eq_top_iff'.1 hsp y
    show σ a⁻¹ (((y : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W) ∈ _
    clear hconj hyK yW hye hy0
    induction hy using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨ψ, hψ, z, rfl⟩ := hu
      exact Submodule.subset_span ⟨(σ a⁻¹ ∘ₗ (GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))).subtype ∘ₗ U.toSubmodule.subtype) ∘ₗ ψ,
        fun k z' => (congrArg (fun q : U.toSubmodule => σ a⁻¹ (((q : U.toSubmodule) : GlobalTheory.PRep.fixed σ ((levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 R.triv))).subgroupOf (GfC (Yc D 0)))) : W))
          (hψ _ z')).trans (hkey k (ψ z')), z, rfl⟩
    | zero => simpa using zero_mem _
    | add u u' _ _ hu hu' => simpa only [Submodule.coe_add, map_add] using add_mem hu hu'
    | smul c u _ hu => simpa only [Submodule.coe_smul, map_smul] using Submodule.smul_mem _ c hu

end GlobalTheory.TypeVec
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typeVector_of_good_level_representation : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), IsAdmissible σ → GlobalTheory.CuspMult.IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ → ∃ T : TypeDataG (Yc D 0), NoFixed T ∧ HasTypeVec T σ := by
  atlas_forward_decl GlobalTheory.TypeVec.hasTypeVec_of_goodRep
end

section
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FinIsoLocal

theorem bij_of_frame {A : Type} [CommRing A] {m n : ℕ} (h : n = m) (j : Matrix (Fin m) (Fin n) A) (β : GL (Fin n) A)
    (M : GL (Fin m) A) (hj : j * β.val = M.val.submatrix id (Fin.cast h)) : Function.Bijective j.mulVec := by
  subst h
  have hj' : j = M.val * (β⁻¹).val := by
    have e : M.val.submatrix id (Fin.cast rfl) = M.val := by ext a b; rfl
    rw [e] at hj
    rw [← hj, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  refine GlobalTheory.FinAdIdent.bij_of_inv (j' := β.val * (M⁻¹).val) ?_ ?_
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (β⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [hj', Matrix.mul_assoc, ← Matrix.mul_assoc (M⁻¹).val, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]

end GlobalTheory.FinIsoLocal

theorem GlobalTheory.FinIsoLocal.exists_local_inner : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), GlobalTheory.CuspMult.IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ → ∃ (jl : ∀ v, GLoc D.sp.cm.sig (Yc D 0).gram v ≃ₜ* GLoc D.sp.cm.sig (Wc D i).gram v) (Φ₀ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)) (b : GfC (Yc D 0)), (∀ v, IsLatticeConj (frameLat (Yc D 0)) (frameLat (Wc D i)) (jl v)) ∧ (∀ v g, Φ₀ (locFin (Yc D 0) v g) = locFin (Wc D i) v (jl v g)) ∧ ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ i j Φ hΦ
  obtain ⟨h, u, hu, -⟩ := hΦ.frame
  have hbij := GlobalTheory.FinIsoLocal.bij_of_frame h j (R.βY 0) (R.βW i * intGL D.host.F D.host.E (Wc D i).rank u) hu
  have hIs : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsIsom (Yc D 0) (Wc D i) (Formalism.L2.Herm.Af D.host.F) j := ⟨hbij, hΦ.isom⟩
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsConjBy (Yc D 0) (Wc D i) j Φ := hΦ.conj
  obtain ⟨β₀, hβ₀, -⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D (Yc D 0)
  obtain ⟨β₀', hβ₀', -⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D (Wc D i)
  have hT : GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.OnePlaceOver (D := D) (∅ : Set (Formalism.L2.DIV.Pl D.host.E)) := by
    intro PP hPP; exact absurd hPP (Set.notMem_empty PP)
  obtain ⟨j₀, hL, hM⟩ := GlobalTheory.FinAdIdent.globalIsometry D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ hT
  obtain ⟨Φ₀, hC₀, -⟩ := GlobalTheory.FinAdIdent.inducedIso D (Yc D 0) (Wc D i) h (frameLat (Yc D 0)) (frameLat (Wc D i))
    β₀ β₀' 1 1 hβ₀ hβ₀' ∅ j₀ hL hM
  obtain ⟨jl, h1, h2⟩ := GlobalTheory.T.adelicLatticeIsometry_eq_prod_localComponents D (Yc D 0) (Wc D i) j₀ Φ₀ hL hC₀
  obtain ⟨b, hb⟩ := GlobalTheory.T.adelicIsometryConj_differ_by_innerAutomorphism D (Yc D 0) (Wc D i) j j₀ Φ Φ₀ hIs hL.1 hC hC₀
  exact ⟨jl, Φ₀, b, h1, h2, hb⟩
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localIsometries_innerAut_adelicFrameIsometry : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)) (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), GlobalTheory.CuspMult.IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ → ∃ (jl : ∀ v, GLoc D.sp.cm.sig (Yc D 0).gram v ≃ₜ* GLoc D.sp.cm.sig (Wc D i).gram v) (Φ₀ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)) (b : GfC (Yc D 0)), (∀ v, IsLatticeConj (frameLat (Yc D 0)) (frameLat (Wc D i)) (jl v)) ∧ (∀ v g, Φ₀ (locFin (Yc D 0) v g) = locFin (Wc D i) v (jl v g)) ∧ ∀ g, Φ g = Φ₀ (b * g * b⁻¹) := by
  atlas_forward_decl GlobalTheory.FinIsoLocal.exists_local_inner
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section
namespace GlobalTheory.ParamMatch

theorem lamAt_anti_fin {Rk : Ranks} (h : HCParam Rk) {n : ℕ} (hn : n ≤ Rk.r) :
    StrictAnti fun a : Fin n => Formalism.L2.NTheta.lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have h1 := Formalism.L2.NTheta.lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at h1
  have h2 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ (b : ℕ) - a)
  show Formalism.L2.NTheta.lamAt h b < Formalism.L2.NTheta.lamAt h a
  linarith

theorem enum_fst {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum S lam ε)
    (f : Fin n → ℚ) (hf : StrictAnti f) (hS : S.image Prod.fst = Finset.univ.image f) (a : Fin n) :
    lam a = f a := by
  obtain ⟨h1, q, hq, rfl⟩ := he
  have h3 : StrictAnti q := fun a b hab => by
    have := h1 hab
    rw [hq, hq] at this
    exact_mod_cast this
  have h4 : Finset.univ.image q = Finset.univ.image f := by
    rw [← hS, Finset.image_image]; rfl
  have h5 : q = f := by
    refine (h3.range_inj hf).1 ?_
    have := congrArg (fun s : Finset ℚ => (s : Set ℚ)) h4
    simpa [Finset.coe_image] using this
  rw [hq, h5]

theorem lamAt_b' {Rk : Ranks} (h : HCParam Rk) (j : Fin Rk.m) :
    Formalism.L2.NTheta.lamAt h (Rk.k - 1 + j) = -h.b j := by
  have hc : ∀ (x y : ℕ) (hx : x < Rk.m) (hy : y < Rk.m), x = y → h.b ⟨x, hx⟩ = h.b ⟨y, hy⟩ := by
    rintro x _ _ _ rfl; rfl
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_neg (by omega), dif_pos (by omega)]
  rw [hc _ _ _ j.2 (by omega)]

theorem lamAt_v' {Rk : Ranks} (h : HCParam Rk) (j : Fin (Rk.k - 1)) :
    Formalism.L2.NTheta.lamAt h j = h.v j := by
  unfold Formalism.L2.NTheta.lamAt
  rw [dif_pos j.2]

theorem parA_fst (D : D7) (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parA (Ptw D) 0 ρ).image Prod.fst = Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  have hk := D.R.m_add_three_le_k
  have hv : (Ptw D).v ρ = (D.hc ρ).v := rfl
  have hb : (Ptw D).b ρ = (D.hc ρ).b := rfl
  ext x
  simp [parA, TPar.Dpar]
  rw [hv, hb]
  constructor
  · rintro (⟨a, rfl, -⟩ | ⟨a, rfl⟩ | ⟨a, rfl, -⟩)
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
    · exact ⟨⟨a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_v' _ a⟩
    · exact ⟨⟨D.R.k - 1 + a, by have := a.2; unfold Ranks.r; omega⟩, lamAt_b' _ a⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    unfold Ranks.r at ha
    by_cases h1 : (a : ℕ) < D.R.k - 1
    · exact Or.inr (Or.inl ⟨⟨a, h1⟩, (lamAt_v' _ ⟨a, h1⟩).symm⟩)
    · let c : Fin D.R.m := ⟨a - (D.R.k - 1), by omega⟩
      have hc : Formalism.L2.NTheta.lamAt (D.hc ρ) a = -(D.hc ρ).b c := by
        rw [← lamAt_b' _ c]; congr 1; simp only [c]; omega
      rw [hc]
      by_cases h2 : (c : ℕ) = 0 ∨ Even (c : ℕ)
      · exact Or.inr (Or.inr ⟨c, rfl, h2⟩)
      · push_neg at h2
        exact Or.inl ⟨c, rfl, h2.1, Nat.not_even_iff_odd.mp h2.2⟩

theorem tauE_inj {D : D7} {τ ρ : D.what₂.Tau} (h : tauE D τ = tauE D ρ) : τ = ρ :=
  D.eTau.injective (Subtype.ext (Formalism.IndefR.Conj.emb_injective h))

open Formalism.FrobeniusOrbits in
theorem tauE_ne_conj' {D : D7} (τ ρ : D.what₂.Tau) : tauE D τ ≠ (starRingEnd ℂ).comp (tauE D ρ) := by
  intro h
  unfold tauE at h
  rw [Formalism.IndefR.Conj.conj_comp_emb] at h
  have e1 : (D.eTau τ).1.1.2 = ((D.eTau ρ).1 * D.R.cc).1.2 :=
    congrArg (fun g : D.R.GG => g.1.2) (Formalism.IndefR.Conj.emb_injective h)
  have hc := Formalism.IndefR.Conj.snd_side (D := D) false
  simp only [Bool.false_eq_true, if_false] at hc
  rw [show ((D.eTau ρ).1 * D.R.cc).1.2 = (D.eTau ρ).1.1.2 * (D.R.cc).1.2 from rfl] at e1
  rw [(Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2, (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau ρ).2, one_mul, hc] at e1
  exact absurd e1 (by decide)

theorem lab_base {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (ρ : D.what₂.Tau) :
    lab (sg0 D A) ρ = ρ ∧ labE (sg0 D A) ρ = tauE D ρ := by
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hb : ∀ τ, labE D.what₂.embLL τ = tauE D τ := fun τ => Formalism.IndefR.Conj.labE_base τ
  rw [hs]
  refine ⟨?_, hb ρ⟩
  have hex : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (hb ρ)⟩
  unfold lab
  rw [dif_pos hex]
  rcases hex.choose_spec with h | h
  · rw [hb] at h; exact tauE_inj h
  · rw [hb] at h; exact absurd h (tauE_ne_conj' _ _)

theorem parAt_fst {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ρ : D.what₂.Tau) {n : ℕ} (hn : n = D.R.r) :
    (parAt (Wc D i) (sg0 D A) ρ).image Prod.fst =
      Finset.univ.image fun a : Fin n => Formalism.L2.NTheta.lamAt (D.hc ρ) a := by
  subst hn
  obtain ⟨h1, h2⟩ := lab_base R ρ
  have hpq : ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r := by
    have hk := D.R.m_add_three_le_k
    have hi := i.2
    rw [D.sp.W_sigval _ (Nat.le_add_left _ _) i.2]
    simp only [Ranks.sigW, Ranks.r]; omega
  rw [parAt, if_pos (by rw [h1]; exact h2), kapAt, h1]
  generalize ((Wc D i).sig (tauE D ρ)).1 = p at hpq ⊢
  generalize ((Wc D i).sig (tauE D ρ)).2 = q at hpq ⊢
  have ho : Odd (p + q) := hpq ▸ Formalism.L2.NTheta.odd_r D.R
  ext x
  simp only [Formalism.L2.NTheta.holPar, Finset.image_image, Finset.mem_image, Finset.mem_univ, true_and,
    Function.comp_def, Formalism.L2.NTheta.holEnt_kapW _ _ _ ho]
  constructor
  · rintro ⟨(a | c), rfl⟩
    · exact ⟨⟨a, by omega⟩, rfl⟩
    · exact ⟨⟨p + c, by omega⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    have ha := a.2
    by_cases hap : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hap⟩, rfl⟩
    · refine ⟨Sum.inr ⟨a - p, by omega⟩, ?_⟩
      simp only [Sum.elim_inr]
      congr 1
      omega

theorem params_match : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)), ∃ (hr : (Wc D i).rank = (Yc D 0).rank) (lam : D.what₂.Tau → Fin (Yc D 0).rank → ℤ), Odd (Yc D 0).rank ∧ (∀ ρ, Gap (lam ρ)) ∧ (∀ ρ a, M₀.lam ρ a = lam ρ a) ∧ ∀ ρ a, (R.MW i (sg0 D A)).lam ρ a = lam ρ (a.cast hr) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG i M₀
  have hY : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _), Nat.zero_min]
    simp [Ranks.rankY]
  have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have key : ∀ ρ (n : ℕ), (((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) n⌋ : ℤ) : ℚ)) = Formalism.L2.NTheta.lamAt (D.hc ρ) n := by
    intro ρ n
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc ρ) n
    rw [hz, Int.floor_intCast]
  have keyR : ∀ ρ (n : ℕ), (((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) n⌋ : ℤ) : ℝ)) = ((Formalism.L2.NTheta.lamAt (D.hc ρ) n : ℚ) : ℝ) := by
    intro ρ n
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc ρ) n
    rw [hz, Int.floor_intCast, Rat.cast_intCast]
  refine ⟨hW.trans hY.symm, fun ρ a => ⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (a : ℕ)⌋, hY ▸ Formalism.L2.NTheta.odd_r D.R, ?_, ?_, ?_⟩
  · intro ρ a b hab
    have hb : (b : ℕ) < D.R.r := lt_of_lt_of_eq b.2 hY
    have h1 := hG.gapR ρ a (by omega)
    rw [← hab] at h1
    have hr1 : ((Yc D 0).rank : ℚ) ≤ 100 * (D.R.r : ℚ) ^ 4 := by
      rw [hY]
      have : D.R.r ≤ 100 * D.R.r ^ 4 := by
        have := Nat.le_self_pow (by norm_num : (4 : ℕ) ≠ 0) D.R.r
        omega
      exact_mod_cast this
    have : ((Yc D 0).rank : ℚ) ≤ ((⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (a : ℕ)⌋ - ⌊Formalism.L2.NTheta.lamAt (D.hc ρ) (b : ℕ)⌋ : ℤ) : ℚ) := by
      push_cast
      rw [key, key]
      linarith
    exact_mod_cast this
  · intro ρ a
    rw [enum_fst (M₀.enum ρ) (fun a : Fin (Yc D 0).rank => Formalism.L2.NTheta.lamAt (D.hc ρ) a)
      (lamAt_anti_fin _ hY.le) (parA_fst D ρ hY) a, keyR]
  · intro ρ a
    rw [enum_fst ((R.MW i (sg0 D A)).enum ρ) (fun a : Fin (Wc D i).rank => Formalism.L2.NTheta.lamAt (D.hc ρ) a)
      (lamAt_anti_fin _ hW.le) (parAt_fst R i ρ hW) a]
    exact (keyR ρ (a : ℕ)).symm

end GlobalTheory.ParamMatch
end
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_odd_rank_gap : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)), ∃ (hr : (Wc D i).rank = (Yc D 0).rank) (lam : D.what₂.Tau → Fin (Yc D 0).rank → ℤ), Odd (Yc D 0).rank ∧ (∀ ρ, Gap (lam ρ)) ∧ (∀ ρ a, M₀.lam ρ a = lam ρ a) ∧ ∀ ρ a, (R.MW i (sg0 D A)).lam ρ a = lam ρ (a.cast hr) := by
  first | exact @GlobalTheory.ParamMatch.params_match | exact GlobalTheory.ParamMatch.params_match | (intros; apply GlobalTheory.ParamMatch.params_match <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.MultEqTrace

def conjEquiv {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (Φ Φ₀ : G ≃* H) (b : G) (hb : ∀ g, Φ g = Φ₀ (b * g * b⁻¹)) :
    Representation.Equiv (σ.comp Φ.symm.toMonoidHom : Representation ℂ H W)
      (σ.comp Φ₀.symm.toMonoidHom : Representation ℂ H W) :=
  Representation.Equiv.mk
    (LinearEquiv.ofLinear (σ b) (σ b⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl))
    fun h => by
      have e : Φ.symm h = b⁻¹ * Φ₀.symm h * b := by
        apply Φ.injective
        rw [Φ.apply_symm_apply, hb]
        simp [mul_assoc]
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        LinearEquiv.coe_coe, LinearEquiv.ofLinear_apply, e]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group

theorem multEq_of_trCusp : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.DixmierMalliavinFactorisation → GlobalTheory.Published.GreenCuspidal → TRCusp → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.CuspMult.MultEq R := by
  intro hRD hHC hDM hGC hTR D G _ _ Pl0 T A Ks _ _ _ R F hG
  intro i M₀ j Φ hΦ W _ _ σ hirr hadm hgood
  obtain ⟨Ty, hNF, hTV⟩ := GlobalTheory.T.exists_typeVector_of_good_level_representation hGC R F hG W σ hadm hgood
  obtain ⟨jl, Φ₀, b, hjl, hΦ₀, hb⟩ := GlobalTheory.T.exists_localIsometries_innerAut_adelicFrameIsometry R F hG i j Φ hΦ
  obtain ⟨hr, lam, hodd, hgap, hM₀, hMW⟩ := GlobalTheory.T.discrete_series_odd_rank_gap R F hG i M₀
  have hinf : IsInfFam R.θ := hG.core.models.inf
  let μ : Measure (GA D (Yc D 0)) := Measure.haar
  let μ' : Measure (GA D (Wc D i)) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ inferInstance
  haveI : μ'.IsMulRightInvariant := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D _ μ' inferInstance
  have hadm' : IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom) :=
    GlobalTheory.CuspMult.isAdmissible_comp_equiv σ Φ.symm hadm
  rw [GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Yc D 0) _ M₀ μ W σ hadm.1,
    GlobalTheory.T.cuspidalMultiplicity_eq_discreteSeriesModel_maps hRD hHC hDM D R.θ hinf (Wc D i) _ (R.MW i (sg0 D A)) μ' W _ hadm'.1,
    hTR D (Yc D 0) lam _ M₀ Ty hodd hgap hM₀ hNF (Wc D i) hr _ (R.MW i (sg0 D A)) hMW jl hjl Φ₀ hΦ₀ μ μ' W σ hirr hadm hTV]
  exact ((mDS_congr (GlobalTheory.MultEqTrace.conjEquiv σ Φ.toMulEquiv Φ₀.toMulEquiv b hb)).2).symm

end GlobalTheory.MultEqTrace
end
end
