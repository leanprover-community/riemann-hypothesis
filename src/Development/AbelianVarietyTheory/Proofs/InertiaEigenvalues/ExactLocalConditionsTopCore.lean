module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharUnramified
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.InvariantsVanishing
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientExtensionIffAdmissibleExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardHodgeTateJumpsCrystallineEqDimStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleClassAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantIsoTransportCocyclesExtensionsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivStableLatticeIntegralCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumericalGaloisDataLocalSituationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteModuleKilledByPowOfNotIsUnitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataDualExactStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionEqTwistedCoefficientsCocycleIffStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import ReciprocityTheory.BasicDefinitions.ExistsUnique

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.TopDict

open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

theorem mk_mem_unr_iff {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (I : Subgroup G) (z : ↥(Z1 π ⊤)) :
    (Submodule.Quotient.mk z : H1 π ⊤) ∈ unr π I ↔ ∃ b, ∀ g ∈ I, (z : G → M) g = π g b - b := by
  constructor
  · rintro ⟨z', ⟨b, hb⟩, h⟩
    obtain ⟨b', -, hb'⟩ := (Submodule.Quotient.eq _).mp h
    refine ⟨b - b', fun g hg => ?_⟩
    have h1 : π g b' - b' = (z' : G → M) g - (z : G → M) g := congrFun hb' g
    rw [hb g hg] at h1
    have h2 : (z : G → M) g = π g b - b - (π g b' - b') := by rw [h1]; abel
    rw [h2, map_sub]
    abel
  · rintro ⟨b, hb⟩
    exact ⟨z, ⟨b, hb⟩, rfl⟩

theorem admissibleExtension_iff_equivariantCoefIso {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ}
    (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
    {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (W : Representation O G M) (W' : Representation O G M') (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x))
    (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X)
    (hzz : ∀ g, z' g = LinearEquiv.rTensor X e (z g)) (hz : z ∈ Z1 (twCoef W χ X) ⊤)
    (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0) :
    Admissible PD emb Γ t Ut (Ea W χ hc ⟨z, hz⟩) ↔ Admissible PD emb Γ t Ut (Ea W' χ hc ⟨z', hz'⟩) := by
  obtain ⟨f, hf⟩ := (GlobalTheory.T.equivariantIso_transport_cocycles_extensions W W' e he χ X z z' hzz).2.1 hz hz' hc
  have hf' : ∀ g x, f.symm (Ea W' χ hc ⟨z', hz'⟩ g x) = Ea W χ hc ⟨z, hz⟩ g (f.symm x) :=
    fun g x => f.injective (by rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  exact ⟨fun h => h.of_equiv f hf, fun h => h.of_equiv f.symm hf'⟩

theorem WachMod_mem_B1_iff {O G M : Type} [CommRing O] [Group G] [AddCommGroup M] [Module O M]
    (π : Representation O G M) (z : G → M) : z ∈ B1 π ⊤ ↔ ∃ m, ∀ g, z g = π g m - m := by
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, fun g => rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, Submodule.mem_top, funext fun g => (hm g).symm⟩

private theorem mk_eq_zero_iff_mem_B1 {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module O M] (π : Representation O G M) (z : ↥(Z1 π ⊤)) :
    (Submodule.Quotient.mk z : H1 π ⊤) = 0 ↔ (z : G → M) ∈ B1 π ⊤ :=
  Submodule.Quotient.mk_eq_zero ((B1 π ⊤).submoduleOf (Z1 π ⊤))

private theorem mk_mem_class_congr {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module O M] (π : Representation O G M) (z : ↥(Z1 π ⊤))
    {A A' : Set (H1 π ⊤)} (h : A = A') :
    (Submodule.Quotient.mk z : H1 π ⊤) ∈ A ↔ (Submodule.Quotient.mk z : H1 π ⊤) ∈ A' :=
  Set.ext_iff.1 h _

set_option maxHeartbeats 8000000 in
theorem topCore_of_typings : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P →
    GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)),
    Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  intro l _ P AI hT H hSA hSB hSC K LL hA lam hlam h5 t h w η typ U V _ _ _ _ _ _ _ _ _ _ _ ρ T₀ χ hyp X _ _ _
  -- Supply the canonical modules directly for the field and lattice constructions.
  let : Module ↥(OL LL) ↥LL.1 := Algebra.toModule
  let : Module ℚ_[l] ↥LL.1 := Algebra.toModule
  let : Module ↥(OL LL) ↥(OL LL) := Semiring.toModule
  let : Module ↥(OL LL) ↥T₀.T := Submodule.module T₀.T
  let T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := LocLat.mk V ρ hyp.2.2.1 T₀
  have hcard := GlobalTheory.T.card_hodgeTate_jumps_crystalline_eq_dim P AI hT H K LL hA V ρ U hyp.2.2.2.1 hyp.2.2.2.2.1
  obtain ⟨r, D, ε, hHyp, hDt, hcount, hchi⟩ := GlobalTheory.T.exists_numerical_galoisData_localSituation P H K LL hA lam hlam h5 t h w η typ U T χ hyp hcard
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hHyp.1⟩
  let S : TopSit P := ⟨K, LL, _, r, (H.W K 1 LL hA.2.2).emb, D, ⟨lam, T, χ 1, ε⟩, hHyp⟩
  let : Module S.O S.O := Semiring.toModule
  have hkill : ∃ a : ℕ, ∀ x : X, S.Γ.lam ^ a • x = 0 := by
    obtain ⟨_, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    exact GlobalTheory.T.exists_pow_smul_eq_zero_of_finite_of_not_isUnit (↥(OL LL)) lam hlam.not_isUnit X
  have hCl := GlobalTheory.AdmClosure.admissible_closed S
  obtain ⟨hL0, hLc⟩ := GlobalTheory.AdmClasses.admissibleLocalSituation_admissible_classes S hCl (StdAdm.stdAdm S (CrysRules.crysCalc AI hT S) hCl)
  have hpoly : tableLineDegreeTwo.resPoly ρ χ t = tableLineDegreeTwo.resPoly S.Γ.T₀.ρ S.Γ.chi S.D.t := by
    funext g
    change tableLineDegreeTwo.resPoly ρ χ t g = tableLineDegreeTwo.resPoly ρ S.Γ.chi D.t g
    rw [hDt]
    unfold tableLineDegreeTwo.resPoly
    congr 1
    refine Finset.prod_congr rfl fun c hc => ?_
    rw [hchi c hc]
  have hadmCoc (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (L : Lattice (O := S.O) T'.ρ) :
      letI : Module S.O ↥L.T := Submodule.module L.T
      ∀ (z : S.G → ↥L.T ⊗[S.O] X)
      (hz : z ∈ Z1 (twCoef (latRep L) S.Γ.χ₁ X) ⊤),
      tableLineDegreeTwo.IsAdmCoc (P.PD K) (H.W K 1 LL hA.2.2).emb lam (tableLineDegreeTwo.jTil U w t) (tableLineDegreeTwo.resPoly ρ χ t) L X (χ 1) z ↔
      ∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (latRep L) S.Γ.χ₁ ha ⟨z, hz⟩) := by
    intro z hz
    have hcongr := congrArg (fun p =>
      tableLineDegreeTwo.IsAdmCoc (P.PD K) (H.W K 1 LL hA.2.2).emb lam
        (tableLineDegreeTwo.jTil U w t) p L X (χ 1) z) hpoly
    refine (iff_of_eq hcongr).trans ?_
    exact exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha =>
      GlobalTheory.T.admissible_quotientExtension_iff_admissible_ext S (tableLineDegreeTwo.jTil U w t) hcount T' L X z hz a ha

  have ext_iff : ∀ (c : ℕ) {Mc : Type} [AddCommGroup Mc] [Module S.O Mc] (Wc : Representation S.O S.G Mc)
      (e : S.O ≃ₗ[S.O] Mc), (∀ g x, e (S.Γ.Wchi c g x) = Wc g (e x)) →
      ∀ (z₀ : S.G → S.O ⊗[S.O] X) (z : S.G → Mc ⊗[S.O] X), (∀ g, z g = LinearEquiv.rTensor X e (z₀ g)) →
      ∀ (hz₀ : z₀ ∈ Z1 (twCoef (S.Γ.Wchi c) S.Γ.χ₁ X) ⊤) (hz : z ∈ Z1 (twCoef Wc S.Γ.χ₁ X) ⊤),
      ((∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea Wc S.Γ.χ₁ ha ⟨z, hz⟩)) ↔
        (∃ a₀ : ℕ, ∀ a ≥ a₀, ∀ ha : (∀ x : X, S.Γ.lam ^ a • x = 0), S.admitted (Ea (S.Γ.Wchi c) S.Γ.χ₁ ha ⟨z₀, hz₀⟩))) := by
    intro c Mc _ _ Wc e he z₀ z hzz hz₀ hz
    refine exists_congr fun a₀ => forall_congr' fun a => forall_congr' fun _ => forall_congr' fun ha => ?_
    exact (admissibleExtension_iff_equivariantCoefIso (P.PD S.K) S.emb S.Γ S.D.t S.D.Ut (S.Γ.Wchi c) Wc e he S.Γ.χ₁ X z₀ z hzz hz₀ hz ha).symm
  have charClass (c : ℕ) (hc : c ∈ Finset.Icc 1 t)
      (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c)))) :
      letI : Module ↥(OL LL) ↥Lc.T := Submodule.module Lc.T
      let π := twCoef (S.Γ.Wchi c) S.Γ.χ₁ X
      ∀ (z : ↥(GK K) → ↥Lc.T ⊗[↥(OL LL)] X), tableLineDegreeTwo.IsCoc Lc X (χ 1) z →
        ∃ z₀ : ↥(Z1 π ⊤),
          (tableLineDegreeTwo.IsAdmCoc (P.PD K) (H.W K 1 LL hA.2.2).emb lam
              (tableLineDegreeTwo.jTil U w t) (tableLineDegreeTwo.resPoly ρ χ t) Lc X (χ 1) z ↔
            (Submodule.Quotient.mk z₀ : H1 π ⊤) ∈ S.cls (S.Γ.Wchi c) X) ∧
          ((z₀ : S.G → S.O ⊗[S.O] X) ∈ B1 π ⊤ ↔ tableLineDegreeTwo.IsCob Lc X (χ 1) z) ∧
          ((Submodule.Quotient.mk z₀ : H1 π ⊤) ∈ (unr π (IK K) : Set (H1 π ⊤)) ↔
            tableLineDegreeTwo.IsUnr Lc X (χ 1) (IK K) z) := by
    intro π z hz
    let : Module ↥(OL LL) ↥Lc.T := Submodule.module Lc.T
    have hχc : S.Γ.chi c = χ c := hchi c hc
    refine (GlobalTheory.T.exists_equiv_stableLattice_integralCharacter LL (χ c) Lc).elim fun e he => ?_
    have he' : ∀ g x, e (S.Γ.Wchi c g x) = latRep Lc g (e x) := fun g x =>
      (congrArg (fun θ : S.G →* S.Oˣ => e (Formalism.GaloisCohomology.scalRep S.O θ g x)) hχc).trans (he g x)
    let eX := LinearEquiv.rTensor X e
    let z₀ : S.G → S.O ⊗[S.O] X := fun g => eX.symm (z g)
    have hzz : ∀ g, z g = eX (z₀ g) := fun g => (eX.apply_symm_apply (z g)).symm
    have htransport := GlobalTheory.T.equivariantIso_transport_cocycles_extensions
      (S.Γ.Wchi c) (latRep Lc) e he' (χ 1) X z₀ z hzz
    have hact := GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff Lc X (χ 1)
    have hz' := (hact.2 z).1 hz
    have hz₀ := htransport.1.2 hz'
    let cocycle : ↥(Z1 π ⊤) := ⟨z₀, hz₀⟩
    have hcont := (hyp.2.2.2.2.2 c hc).2.1
    let Tc : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
      LocLat.mk ↥LL.1 (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c))) (fun x => hcont.mul continuous_const) Lc
    have hc' := Finset.mem_Icc.1 hc
    have hct : c ≤ D.t := hDt.symm ▸ hc'.2
    have hclass := GlobalTheory.T.cocycle_class_admissible S (S.Γ.Wchi c) X hkill
      ((hLc c hc'.1 hct) X).2.1 cocycle
    refine ⟨cocycle, (hadmCoc Tc Lc z hz').trans
      ((ext_iff c (latRep Lc) e he' z₀ z hzz hz₀ hz').trans hclass), ?_, ?_⟩
    · refine htransport.2.2.1.trans ((WachMod_mem_B1_iff (twCoef (latRep Lc) (χ 1) X) z).trans ?_)
      exact exists_congr fun m => forall_congr' fun g =>
        iff_of_eq (congrArg (fun y : ↥Lc.T ⊗[↥(OL LL)] X => z g = y - m) (hact.1 g m).symm)
    · refine (mk_mem_unr_iff π (IK K) cocycle).trans ((htransport.2.2.2 (IK K)).trans ?_)
      exact exists_congr fun m => forall_congr' fun g => forall_congr' fun _ =>
        iff_of_eq (congrArg (fun y : ↥Lc.T ⊗[↥(OL LL)] X => z g = y - m) (hact.1 g m).symm)

  refine ⟨?_, ?_, ?_⟩
  · intro ρ' T₀' hρ' hTT z hz
    let π := twCoef (latRep T₀) (χ 1) X
    have hz' : z ∈ Z1 π ⊤ := ((GlobalTheory.T.twistedAction_eq_twistedCoefficients_cocycle_iff T₀ X (χ 1)).2 z).1 hz
    let cocycle : ↥(Z1 π ⊤) := ⟨z, hz'⟩
    have hclass := GlobalTheory.T.cocycle_class_admissible S S.Γ.W₀ X hkill (hL0 X).2.1 cocycle
    have hA' := ((hSA K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2).2.2.2.2 X).2
    have hmem := mk_mem_class_congr π cocycle hA'
    have hdual := GlobalTheory.T.period_data_dual_exact (P.PD K) T₀ ρ' T₀' X (χ 1) hρ' hTT z hz'
    exact (hadmCoc T T₀ z hz').trans (hclass.trans (hmem.trans hdual))
  · intro c hc Lc z hz
    have hc' := Finset.mem_Icc.1 hc
    have hc1 : c ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨(Nat.le_succ 1).trans hc'.1, hc'.2⟩
    have hct : c ≤ D.t := hDt.symm ▸ hc'.2
    refine (charClass c hc1 Lc z hz).elim fun z₀ hclass => ?_
    have hB' := hSB K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp c hc'.1 hct X
    let π := twCoef (S.Γ.Wchi c) S.Γ.χ₁ X
    have hmem := mk_mem_class_congr π z₀ hB'
    exact hclass.1.trans (hmem.trans (Iff.trans Set.mem_singleton_iff
      ((mk_eq_zero_iff_mem_B1 π z₀).trans hclass.2.1)))
  · intro L₁ z hz
    have h1 : 1 ∈ Finset.Icc 1 t := Finset.mem_Icc.2 ⟨le_rfl, hyp.1⟩
    refine (charClass 1 h1 L₁ z hz).elim fun z₀ hclass => ?_
    have hC' := hSC K LL _ r (H.W K 1 LL hA.2.2).emb D S.Γ hHyp.1 hHyp.2.1 hHyp.2.2.1 hHyp.2.2.2.1
      hHyp.2.2.2.2 X
    have heq := hC'.trans
      (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.homModInertia_eq_unr S.Γ X (IK K))
    exact hclass.1.trans ((mk_mem_class_congr (twCoef (S.Γ.Wchi 1) S.Γ.χ₁ X) z₀ heq).trans hclass.2.2)

end GlobalTheory.TopDict
