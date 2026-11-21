import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChoiceSideOfTwisted
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParahoricOfScalarActionOnRamifiedParahoricFor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceEqOfAutomorphismMapsParahoric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdditiveCharacterEqOfCommonUnipotentLevelEigenve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterSplitPlaceComponentUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsClassTrivialStabiliserAtTypePlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankAlgebraicModularFormsComplexification
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlacesAllStatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadPlacesSubOfAdmissibleTwistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideReadHeckeOfAdmissibleTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceOfAdmissibleTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JointEtaOfAdmissibleTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellWeightOfAdmissibleTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisCharacterAntiRamifiedExactly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosedContinuumRingEquivComplexExtending
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardPadicAlgClPadicComplexEqComplex

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LevCmp

section Glue

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def compHom (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    GAf L n →* GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
  (Matrix.GeneralLinearGroup.map (compAt L v)).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem compHom_eq_one_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : GAf L n) :
    compHom v x = 1 ↔ (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem compHom_eq_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n) :
    compHom v x = compHom v y ↔
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem mem_of_agree {J J' : Subgroup (GAf L n)} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    {S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (hS : S.Finite) (hJ : NG.IsProdLevel J)
    (hO : NG.HypOutside J χ S) (hO' : NG.HypOutside J' χ' S)
    (hloc : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩)
    (κ : GAf L n) (hκ : κ ∈ J) : ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by

  have hone : ∀ u κ, TrivOutside {u} κ → ∀ hκ : κ ∈ J, ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro u κ hu hκ
    by_cases huS : u ∈ S
    · obtain ⟨h1, h2⟩ := hloc u huS κ hu
      exact ⟨h1.mp hκ, h2 hκ (h1.mp hκ)⟩
    · have ht : TrivOutside Sᶜ κ := by
        intro v hv
        apply hu v
        rintro rfl
        exact huS (not_not.mp hv)
      obtain ⟨a1, a2⟩ := hO κ ht
      obtain ⟨b1, b2⟩ := hO' κ ht
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∀ κ (hκ : κ ∈ J),
      TrivOutside (Sᶜ ∪ (T : Set _)) κ → ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty =>
      intro κ hκ ht
      have ht' : TrivOutside Sᶜ κ := by
        intro v hv
        exact ht v (by simpa using hv)
      obtain ⟨a1, a2⟩ := hO κ ht'
      obtain ⟨b1, b2⟩ := hO' κ ht'
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
    | insert u T huT ih =>
      intro κ hκ ht
      obtain ⟨κu, hκu, hu, hcomp⟩ := hJ κ hκ u
      have hκ1 : κ * κu⁻¹ ∈ J := J.mul_mem hκ (J.inv_mem hκu)
      have ht1 : TrivOutside (Sᶜ ∪ (T : Set _)) (κ * κu⁻¹) := by
        intro v hv
        rw [← compHom_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]
        by_cases hvu : v = u
        · subst hvu
          exact ((compHom_eq_iff v κ κu).mpr hcomp.symm)
        · have e1 : compHom v κ = 1 := by
            rw [compHom_eq_one_iff]
            apply ht v
            simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, not_or] at hv ⊢
            exact ⟨hv.1, hvu, hv.2⟩
          have e2 : compHom v κu = 1 := by
            rw [compHom_eq_one_iff]
            exact hu v (by simpa using hvu)
          rw [e1, e2]
      obtain ⟨h1', e1⟩ := ih (κ * κu⁻¹) hκ1 ht1
      obtain ⟨h2', e2⟩ := hone u κu hu hκu
      have hprod : κ = κ * κu⁻¹ * κu := by group
      have h' : κ ∈ J' := by
        rw [hprod]; exact J'.mul_mem h1' h2'
      refine ⟨h', ?_⟩
      have s1 : (⟨κ, hκ⟩ : J) = ⟨κ * κu⁻¹, hκ1⟩ * ⟨κu, hκu⟩ := Subtype.ext hprod
      have s2 : (⟨κ, h'⟩ : J') = ⟨κ * κu⁻¹, h1'⟩ * ⟨κu, h2'⟩ := Subtype.ext hprod
      rw [s1, s2, map_mul, map_mul, e1, e2]
  apply key hS.toFinset κ hκ
  intro v hv
  exfalso
  apply hv
  by_cases h : v ∈ S
  · right; simpa using h
  · left; exact h

theorem levEq_of_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  intro L _ _ _ n J J' χ χ' S hS hJ hJ' hO hO' hloc
  have hloc' : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J' ↔ κ ∈ J) ∧ ∀ (h : κ ∈ J') (h' : κ ∈ J), χ' ⟨κ, h⟩ = χ ⟨κ, h'⟩ :=
    fun u hu κ hκ => ⟨(hloc u hu κ hκ).1.symm, fun h h' => ((hloc u hu κ hκ).2 h' h).symm⟩
  refine ⟨le_antisymm (fun κ hκ => (mem_of_agree hS hJ hO hO' hloc κ hκ).1)
    (fun κ hκ => (mem_of_agree hS hJ' hO' hO hloc' κ hκ).1), fun κ h h' => ?_⟩
  obtain ⟨h'', e⟩ := mem_of_agree hS hJ hO hO' hloc κ h
  exact e

end Glue

end GlobalTheory.LevCmp

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productLevel_eq_of_local_agreement : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  atlas_forward_decl GlobalTheory.LevCmp.levEq_of_agree
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ParaUnit

theorem val_det_block {K Γ ι : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Fintype ι] [DecidableEq ι]
    (v : Valuation K Γ) (p : ι → Prop) [DecidablePred p] (A B : Matrix ι ι K)
    (hA : ∀ a b, v (A a b) ≤ 1) (hB : ∀ a b, v (B a b) ≤ 1) (hAB : A * B = 1)
    (hlow : ∀ a b, p a → ¬ p b → v (A a b) < 1) :
    v (Matrix.of fun a b : {x // p x} => A a.1 b.1).det = 1 := by
  let O := v.valuationSubring
  let A' : Matrix ι ι O := Matrix.of fun a b => ⟨A a b, hA a b⟩
  let B' : Matrix ι ι O := Matrix.of fun a b => ⟨B a b, hB a b⟩
  have hAB' : A' * B' = 1 := by
    ext a b
    have := congrFun (congrFun hAB a) b
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.one_apply] at this ⊢
    rw [AddSubmonoidClass.coe_finsetSum, apply_ite (fun x : O => (x : K))]
    simpa [A', B'] using this
  let f := IsLocalRing.residue O
  have hf : ∀ a b, p a → ¬ p b → f (A' a b) = 0 := by
    intro a b ha hb
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact hlow a b ha hb
  let A₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => A' a.1 b.1
  let B₁ : Matrix {x // p x} {x // p x} O := Matrix.of fun a b => B' a.1 b.1
  have h1 : f.mapMatrix A₁ * f.mapMatrix B₁ = 1 := by
    ext a b
    have h := congrArg f (congrFun (congrFun hAB' a.1) b.1)
    rw [Matrix.mul_apply, map_sum, ← Fintype.sum_subtype_add_sum_subtype p] at h
    rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {x // ¬ p x}))
      (fun c _ => by rw [map_mul, hf a.1 c.1 a.2 c.2, zero_mul]), add_zero] at h
    rw [Matrix.mul_apply]
    simp only [map_mul] at h
    refine Eq.trans h ?_
    simp only [Matrix.one_apply, Subtype.ext_iff]
    split_ifs <;> simp
  have h2 : f A₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, ← RingHom.map_det, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have h3 : ((A₁.det : O) : K) = (Matrix.of fun a b : {x // p x} => A a.1 b.1).det := by
    have := RingHom.map_det O.subtype A₁
    exact this
  rw [← h3]
  refine le_antisymm A₁.det.2 (not_lt.1 fun hlt => h2 ?_)
  rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact hlt

theorem detDD_unit_supDiag_int : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  intro L _ _ _ n r s h hp
  have key : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring →
      ∀ a b, Valued.v (g.val a b) ≤ 1 := by
    rintro g ⟨x, rfl⟩ a b
    exact (x.val a b).2
  have hA := key h hp.1
  have hB := key h⁻¹ (inv_mem hp.1)
  refine ⟨?_, ?_⟩
  · exact val_det_block Valued.v (fun x : Fin n => r ≤ x.val) h.val (h⁻¹).val hA hB (by simp)
      (fun a b ha hb => hp.2 a b ha (not_le.1 hb))
  · unfold NG.supDiag
    refine Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun b _ => ?_
    split_ifs
    · exact hA a b
    · simp

end GlobalTheory.ParaUnit
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (r : ℕ) (s : SplitPlace L) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), NG.ParaRT s r h → Valued.v (NG.detDD s r h) = 1 ∧ Valued.v (NG.supDiag s r h) ≤ 1 := by
  atlas_forward_decl GlobalTheory.ParaUnit.detDD_unit_supDiag_int
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ClassForm

theorem double_coset_unique {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {J : Subgroup (GAf L n)} {g : GAf L n}
    (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1)
    {γ γ' : GQ L n} {κ κ' : J} (h : (γ : GAf L n) * g * κ = (γ' : GAf L n) * g * κ') : γ = γ' ∧ κ = κ' := by
  have key : g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by
    calc g⁻¹ * ((γ' : GAf L n)⁻¹ * γ) * g
        = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ : GAf L n) * g * κ) * (κ : GAf L n)⁻¹ := by group
      _ = g⁻¹ * (γ' : GAf L n)⁻¹ * ((γ' : GAf L n) * g * κ') * (κ : GAf L n)⁻¹ := by rw [h]
      _ = (κ' : GAf L n) * (κ : GAf L n)⁻¹ := by group
  have hmem : (γ' : GAf L n)⁻¹ * γ ∈ GQ L n := (GQ L n).mul_mem ((GQ L n).inv_mem γ'.2) γ.2
  have h1 := hg _ hmem (key ▸ J.mul_mem κ'.2 (J.inv_mem κ.2))
  have hγ : (γ : GAf L n) = γ' := by
    rw [inv_mul_eq_one] at h1; exact h1.symm
  refine ⟨Subtype.ext hγ, Subtype.ext ?_⟩
  rw [hγ, mul_assoc, mul_assoc] at h
  exact (mul_left_cancel (mul_left_cancel h))

open Classical in

noncomputable def cosetForm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) : W :=
  if h : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2 then ((χ h.choose.2 : Kˣ) : K) • ρ h.choose.1 w else 0

theorem cosetForm_apply {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (hg : ∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) (w : W) (γ : GQ L n) (κ : J) :
    cosetForm ρ J χ g w ((γ : GAf L n) * g * κ) = ((χ κ : Kˣ) : K) • ρ γ w := by
  have hex : ∃ p : GQ L n × J, (γ : GAf L n) * g * κ = (p.1 : GAf L n) * g * p.2 := ⟨(γ, κ), rfl⟩
  unfold cosetForm
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := double_coset_unique hg hex.choose_spec
  rw [← h1, ← h2]

theorem cosetForm_not {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] {W : Type}
    [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ)
    (g : GAf L n) (w : W) (x : GAf L n) (hx : ¬ ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2) :
    cosetForm ρ J χ g w x = 0 := by
  unfold cosetForm; rw [dif_neg hx]

theorem exists_form_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  intro L _ _ _ n K _ W _ _ _ ρ J χ g hg
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine ⟨cosetForm ρ J χ g w, ⟨fun δ x => ?_, fun μ x => ?_⟩, fun h0 => hw ?_⟩
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (δ : GAf L n) * ((γ : GAf L n) * g * κ) = ((δ * γ : GQ L n) : GAf L n) * g * κ := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_smul, map_mul, Module.End.mul_apply]
    · have hx' : ¬ ∃ p : GQ L n × J, (δ : GAf L n) * x = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(δ⁻¹ * γ, κ), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] at hp ⊢
        rw [← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', map_zero]
  · by_cases hx : ∃ p : GQ L n × J, x = (p.1 : GAf L n) * g * p.2
    · obtain ⟨⟨γ, κ⟩, rfl⟩ := hx
      have e : (γ : GAf L n) * g * κ * μ = (γ : GAf L n) * g * ((κ * μ : J) : GAf L n) := by
        simp [mul_assoc]
      rw [e, cosetForm_apply ρ J χ g hg, cosetForm_apply ρ J χ g hg, map_mul, Units.val_mul, mul_comm, mul_smul]
    · have hx' : ¬ ∃ p : GQ L n × J, x * μ = (p.1 : GAf L n) * g * p.2 := by
        rintro ⟨⟨γ, κ⟩, hp⟩
        refine hx ⟨(γ, κ * μ⁻¹), ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hp ⊢
        rw [← mul_assoc, ← hp]; group
      rw [cosetForm_not ρ J χ g w _ hx, cosetForm_not ρ J χ g w _ hx', smul_zero]
  · have := congrFun h0 g
    have e := cosetForm_apply ρ J χ g hg w 1 1
    simp only [OneMemClass.coe_one, one_mul, mul_one, map_one, Units.val_one, one_smul] at e
    rw [e, Module.End.one_apply] at this
    simpa using this

end GlobalTheory.ClassForm
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_algebraicModularForm_of_trivial_stabiliser : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] [Nontrivial W] (ρ : Representation K (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (g : GAf L n), (∀ γ ∈ GQ L n, g⁻¹ * γ * g ∈ J → γ = 1) → ∃ f ∈ NX.TypeSpF L n K ρ J χ, f ≠ 0 := by
  atlas_forward_decl GlobalTheory.ClassForm.exists_form_of_trivial_stabiliser
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevShapeBound

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eq_of_compAt (s : SplitPlace L) {x y : AL L}
    (h : compAt L s.v x = compAt L s.v y) : s.proj x = s.proj y := by
  have key : ∀ z : AL L, s.proj z =
      (Algebra.TensorProduct.lift s.i (AlgHom.id _ (s.v.adicCompletion (maximalRealSubfield L)))
        (fun _ _ => Commute.all _ _)) (compAt L s.v z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  rw [key, key, h]

theorem loc_eq_of_comp (s : SplitPlace L) {x y : GAf L n}
    (h : (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v)) :
    s.loc n x = s.loc n y := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  exact proj_eq_of_compAt s hij

end Gen

theorem bound : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  intro D η J hG hS κ hκ
  obtain ⟨hprod, hpara, huni, hhyp⟩ := hS

  have hloc : ∀ w, ∃ κ' ∈ J, κ' ∈ Umax D.host.E D.R.nV ∧
      (κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) =
        (κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)).map (compAt D.host.E w) := by
    intro w
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ w
    refine ⟨κ', hκ', ?_, heq⟩
    by_cases hg : w ∈ gPl D
    · obtain ⟨k, v, s, hsv, hsw⟩ := hG.2.1 w hg
      subst hsv
      have hu := (huni k v s hsw κ' htr).1 hκ'
      exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hu.1.1
    · by_cases hq : w ∈ qPl D η
      · obtain ⟨s, hsv, hs⟩ := hpara w hq
        subst hsv
        have hp := (hs κ' htr).1 hκ'
        exact (GlobalTheory.HeckeStdFacts.loc_mem_GLint_iff s htr).1 hp.1
      · refine (hhyp κ' ?_).1 hκ'
        intro u hu
        apply htr u
        rintro rfl
        simp only [Set.mem_compl_iff, not_not, Set.mem_union] at hu
        rcases hu with h | h
        · exact hg h
        · exact hq h
  refine ⟨?_, ?_⟩
  · intro i j
    apply GlobalTheory.FormInner.mem_ALint_of_comp
    intro w
    obtain ⟨κ', -, hU, heq⟩ := hloc w
    refine ⟨(κ'.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (AL D.host.E)) i j, hU i j, ?_⟩
    have := congrFun (congrFun heq i) j
    simpa only [Matrix.map_apply] using this
  · intro k v s hsw
    obtain ⟨κ', hκ', htr, heq⟩ := hprod κ hκ s.v
    have hu := (huni k v s hsw κ' htr).1 hκ'
    rwa [loc_eq_of_comp s heq] at hu

end GlobalTheory.LevShapeBound

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces : ∀ (D : D7) (η : HChar D.host.E) (J : Subgroup (GAf D.host.E D.R.nV)), GPlaces D → GrpShape D η J → ∀ κ ∈ J, κ ∈ Umax D.host.E D.R.nV ∧ ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → NG.UniRT s D.R.r (s.loc _ κ) := by
  atlas_forward_decl GlobalTheory.LevShapeBound.bound
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem overPl_subsingleton {L : Type} [Field L] (w : HeightOneSpectrum (𝓞 L)) :
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)) | NG.OverPl w v}.Subsingleton := by
  intro v hv v' hv'
  exact HeightOneSpectrum.ext (hv.symm.trans hv')

theorem placesOver_finite_of_ne_zero (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem gPl_union_qPl_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  intro D η
  have hS : (⋃ k : Fin 2, placesOver D.host.E (D.host.g k)).Finite :=
    Set.finite_iUnion fun k => placesOver_finite_of_ne_zero _ _ (D.host.g_prime k).ne_zero
  have hR : {w | ¬ η.UnrAt w}.Finite := GlobalTheory.Mem.UnrAe.finite_ramified η
  refine Set.Finite.union ?_ ?_
  · refine (hS.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨w, hw, k, hk⟩
    exact Set.mem_biUnion (Set.mem_iUnion.2 ⟨k, hk⟩) hw
  · refine (hR.biUnion fun w _ => (overPl_subsingleton w).finite).subset ?_
    rintro v ⟨_, w, hw, hu⟩
    exact Set.mem_biUnion (x := w) hu hw

end GlobalTheory.LevCmp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_union_ramifiedPlaces_finite : ∀ (D : D7) (η : HChar D.host.E), (gPl D ∪ qPl D η).Finite := by
  atlas_forward_decl GlobalTheory.LevCmp.gPl_union_qPl_finite
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevProd

open GlobalTheory.MtInProd
open Formalism.L2.NX (locM InLevG InParah inParah_one)
open Classical

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem proj_eA (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    s.proj (eA L v) = if s.v = v then 1 else 0 := by
  show s.i 1 * (idemF (L := L) v) s.v = _
  rw [map_one, one_mul, idemF_apply]

theorem locM_cut (s : SplitPlace L) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n) :
    locM s (cutGA (eA_mul v) (conj_eA v) κ) = if s.v = v then locM s κ else 1 := by
  show ((cutGA (eA_mul v) (conj_eA v) κ).1 : Matrix (Fin n) (Fin n) (AL L)).map s.proj = _
  rw [cutGA_val, map_cutMat, proj_eA]
  split_ifs
  · rw [cutMat_one_left]; rfl
  · rw [cutMat_zero_left]

theorem inLevG_one (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (r : ℕ) :
    InLevG v r (1 : Matrix (Fin n) (Fin n) (v.adicCompletion (maximalRealSubfield L))) := by
  refine ⟨inParah_one v r, fun a b _ _ => ⟨fun hba => ?_, fun hab => ?_⟩⟩
  · have h : a ≠ b := fun e => by subst e; exact lt_irrefl _ hba
    rw [Matrix.one_apply_ne h, map_zero]
    exact WithZero.zero_lt_coe _
  · subst hab
    rw [Matrix.one_apply_eq, sub_self, map_zero]
    exact WithZero.zero_lt_coe _

end Gen

theorem main : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  intro D X i b k Q ψ hA j κ hκ v
  obtain ⟨hU, hG, hQ, hD⟩ := ((cell X b hA j).J_mem κ).1 hκ
  refine ⟨cutGA (eA_mul v) (conj_eA v) κ, ((cell X b hA j).J_mem _).2 ⟨cutGA_mem_Umax _ _ (eA_mem v) hU, fun kv => ?_,
    fun P hP => ?_, fun P hP => ?_⟩, triv_cut_eA v κ, cut_eA_at v κ⟩
  · rw [locM_cut]; split_ifs
    · exact hG kv
    · exact inLevG_one _ _
  · rw [locM_cut]; split_ifs
    · exact hQ P hP
    · exact inParah_one _ _
  · rw [locM_cut]; split_ifs
    · exact hD P hP
    · exact inParah_one _ _

end GlobalTheory.LevProd

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProductLevel_definiteFormsRealisationAtTwist : ∀ (D : D7) (X : NExpTied D) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m), NG.IsProdLevel (cell X b hA j).J := by
  atlas_forward_decl GlobalTheory.LevProd.main
end

section
section
noncomputable section

namespace GlobalTheory.LowAvoid

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

def lowPre (P : Pre) : Finset ℕ := by
  classical
  exact if h : ∃ X : Stages, X.B.toPre = P then lowAll h.choose.toD7 else ∅

theorem lowAll_congr {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : lowAll s.toD7 = lowAll s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem lowAll_eq_lowPre (s : Stages) : lowAll s.toD7 = lowPre s.B.toPre := by
  have h : ∃ X : Stages, X.B.toPre = s.B.toPre := ⟨s, rfl⟩
  simp only [lowPre, dif_pos h]
  exact lowAll_congr h.choose_spec.symm

theorem prime_of_mem_lowAll (D : D7) {p : ℕ} (hp : p ∈ lowAll D) : p.Prime := by
  simp only [lowAll, lowPr, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with ((rfl | rfl | hp | hp) | rfl | rfl | rfl | rfl)
  · exact Nat.prime_two
  · exact (Formalism.L2.Host.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  · exact Nat.prime_of_mem_primeFactors hp
  · exact Nat.prime_of_mem_primeFactors hp
  · exact D.host.g_prime 0
  · exact D.host.g_prime 1
  · exact D.host.pde_prime
  · exact D.host.pde'_prime

theorem eq_of_mem_placesOver {E : Type} [Field E] [NumberField E] (u : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (hu : (Ideal.absNorm u.asIdeal).Prime) (h : u ∈ placesOver E p) : Ideal.absNorm u.asIdeal = p := by
  by_contra e
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∈ u.asIdeal := Ideal.absNorm_mem _
  obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ((p : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast ((Nat.coprime_primes hu hp).2 e)
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ (show ((p : ℕ) : 𝓞 E) ∈ u.asIdeal from h))))

theorem conductors_avoid_lowAll :
    AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  refine evG_all fun K => ?_
  refine large₂.imp (p := fun B _ T => T.Avoids fun _ => lowPre B.toPre)
    ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun B _ _ _ _ => lowPre B, fun _ _ _ _ _ => ∅, by simp, by simp,
      fun _ _ _ _ _ _ h => h⟩ ?_
  intro B f T _ hA _ _ _ w _ P x v u hu p hp hup
  have hl : lowAll (Dof x) = lowPre B.toPre := lowAll_eq_lowPre (w.st x.o.Z)
  obtain ⟨-, h1, -, -⟩ := (T.psi_tw v).2.2.2 u fun h => ((T.psi_is v).ram u).1 h hu
  have e : Ideal.absNorm u.asIdeal = p := eq_of_mem_placesOver u (prime_of_mem_lowAll _ hp) h1 hup
  exact hA v u hu (by rw [e, ← hl]; exact hp)

end GlobalTheory.LowAvoid

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistConductors_avoid_excludedPrimes : AllSt fun _ _ _ T _ _ x => ∀ v, ∀ u ∈ T.Q v, ∀ p ∈ lowAll (Dof x), u ∉ placesOver (Dof x).host.E p := by
  atlas_forward_decl GlobalTheory.LowAvoid.conductors_avoid_lowAll
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem galOf_of_orderDvd : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  intro hGAR D χ n hn hχ hz
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  have h1 : ∀ x, χ.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar D.host.E => ξ.1 x) hχ
  have hko : IsOpen (χ.1.ker : Set (Ideles D.host.E)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow χ.1 χ.2.1 hn h1
  have hkc : IsClosed (χ.1.ker : Set (Ideles D.host.E)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ χ.1.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact χ.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing D.host.E) (FiniteAdeleRing (𝓞 D.host.E) D.host.E))) χ.1.ker : Subgroup _) : Set (InfiniteAdeleRing D.host.E)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art ha.quot.surjective
  let c : Gab D.host.E D.nd.Om →* ℂˣ := (QuotientGroup.lift art.ker χ.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, c (art x) = χ.1 x := fun x => by
    show QuotientGroup.lift art.ker χ.1 hle (e.symm (art x)) = χ.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous c := by
    rw [ha.quot.isQuotientMap.continuous_iff]
    have : (c ∘ art) = χ.1 := funext hc
    rw [this]; exact χ.2.1
  let r : G D.host.E D.nd.Om →* ℂˣ := c.comp (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
  have hrc : Continuous r := hcc.comp continuous_quot_mk
  have hrn : ∀ g, r g ^ n = 1 := fun g => by
    obtain ⟨x, hx⟩ := ha.quot.surjective (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om g)
    show c _ ^ n = 1
    rw [← hx, hc, h1]
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hrc hn hrn
  obtain ⟨z, hz⟩ := hz
  obtain ⟨ψ, hψ⟩ := GlobalTheory.TwistChoice.exists_char_descent D.what₂.embLL hn hz r hrn
  have hψr : (Units.map D.what₂.embLL.toMonoidHom).comp ψ = r := MonoidHom.ext fun g => Units.ext (hψ g)
  have hker : ψ.ker = r.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    rw [← hψr, MonoidHom.comp_apply]
    constructor
    · intro h; rw [h, map_one]
    · intro h
      apply Units.ext
      apply D.what₂.embLL.injective
      have := congrArg Units.val h
      simpa using this
  refine ⟨ψ, ⟨by rw [hker]; exact hro, art, ha, ?_⟩, fun g => ?_⟩
  · rw [hψr]
    intro x σ hσ
    show χ.1 x = c (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om σ)
    rw [← hσ, hc]
  · apply Units.ext
    apply D.what₂.embLL.injective
    have := congrArg Units.val (hrn g)
    rw [← hψr] at this
    simpa using this

end GlobalTheory.LevCmp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (χ : HChar D.host.E) (n : ℕ), 0 < n → χ.OrderDvd n → (∃ z : D.what₂.LL, IsPrimitiveRoot z n) → ∃ ψ₀, GalOf D χ ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1 := by
  atlas_forward_decl GlobalTheory.LevCmp.galOf_of_orderDvd
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwistDescent

variable {D : D7} {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl}

abbrev rd (ρ : Reading i k b v) : D.ntw.Ok i k →+* FractionRing ρ.Oe :=
  (algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap (D.ntw.Ok i k) ρ.Oe)

theorem rd_injective (ρ : Reading i k b v) : Function.Injective (rd ρ) :=
  (IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj

theorem eq_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g g' : G D.host.E D.nd.Om) : χ g = χ g' ↔ ψ₀ g = ψ₀ g' := by
  constructor
  · intro he
    apply Units.ext
    apply ρ.emb.injective
    rw [h g, h g', he]
  · intro he
    apply Units.ext
    apply rd_injective ρ
    rw [← h g, ← h g', he]

theorem one_iff_of_reads {ρ : Reading i k b v} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (g : G D.host.E D.nd.Om) : χ g = 1 ↔ ψ₀ g = 1 := by
  simpa using eq_iff_of_reads h g 1

theorem twOK_of_reads {ρ : Reading i k b v} {Q : Finset (PlE D.host)} {χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))
    (hs : ∀ u ∈ Q, IsSplitPl D.host u) (hd : Disjoint Q (D.ntw.S0 i))
    (ho : IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om))) (ha : AntiHom D.ntw.cc ψ₀)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hr : RamExactly ψ₀ (↑Q : Set (PlE D.host)))
    (ht : BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i)) : IntegralHeckeForms.TwOK i k Q χ := by
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads h g
  refine ⟨hs, hd, hker ▸ ho, fun g g' hg => ?_, fun g => ?_, fun w A hA => ?_, fun w hw A hA σ hσ => ?_⟩
  · rw [← map_inv, eq_iff_of_reads h, map_inv]
    exact ha g g' hg
  · have h1 : χ g ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, one_iff_of_reads h, map_pow]
      exact hp g
    have h2 : ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨a, -, h3⟩ := (D.ntw.zk_prim i k).eq_pow_of_pow_eq_one h2
    refine Subgroup.mem_zpowers_iff.2 ⟨(a : ℤ), ?_⟩
    rw [zpow_natCast]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact h3)
  · rw [← hr w A hA]
    simp only [ne_eq, one_iff_of_reads h]
  · exact (one_iff_of_reads h σ).2 (ht w hw A hA σ hσ)

theorem exists_reads {ρ : Reading i k b v} (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)
    (hp : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) :
    ∃ χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ, (∀ g, χ g ∈ Subgroup.zpowers (D.ntw.zk i k)) ∧
      ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = rd ρ ((χ g : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) := by
  have hz : IsPrimitiveRoot (rd ρ (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) :=
    (D.ntw.zk_prim i k).map_of_injective (rd_injective ρ)
  have hx : ∀ g, ∃ a : ℕ, rd ρ (((D.ntw.zk i k) ^ a : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) =
      ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) := fun g => by
    have h1 : (ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL)) ^ (D.ntw.l i ^ k) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hp g, Units.val_one, map_one]
    obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one h1
    exact ⟨a, by rw [Units.val_pow_eq_pow_val, map_pow]; exact ha⟩
  choose a ha using hx
  let χ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ := MonoidHom.mk' (fun g => D.ntw.zk i k ^ a g) fun g g' => by
    apply Units.ext
    apply rd_injective ρ
    rw [ha (g * g'), map_mul ψ₀, Units.val_mul, map_mul ρ.emb, Units.val_mul, map_mul (rd ρ), ha, ha]
  refine ⟨χ, fun g => ⟨(a g : ℤ), by simp [χ]⟩, fun g => (ha g).symm⟩

theorem exists_pulls_twOK : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v) (Q : Finset (PlE D.host)) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∀ u ∈ Q, IsSplitPl D.host u) → Disjoint Q (D.ntw.S0 i) → IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc ψ₀ → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → RamExactly ψ₀ (↑Q : Set (PlE D.host)) → BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i) → (∃ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀) ∧ ∀ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀ → IntegralHeckeForms.TwOK i k Q (ψ.comp (D.ntw.art i Q)) := by
  intro D i k b v ρ Q ψ₀ hs hd ho ha hp hr ht
  refine ⟨?_, fun ψ hψ => twOK_of_reads (ρ := ρ) (fun g => hψ g) hs hd ho ha hp hr ht⟩
  obtain ⟨χ, hv, hχ⟩ := exists_reads (ρ := ρ) ψ₀ hp
  have hfin : IsOfFinOrder (D.ntw.zk i k) := isOfFinOrder_iff_pow_eq_one.2
    ⟨_, pow_pos (D.ntw.lPrime i).out.pos k, (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one⟩
  haveI : Finite (Subgroup.zpowers (D.ntw.zk i k)) := (finite_zpowers.2 hfin).to_subtype
  have hker : (χ.ker : Set (G D.host.E D.nd.Om)) = ψ₀.ker := Set.ext fun g => by
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    exact one_iff_of_reads hχ g
  obtain ⟨f, hf⟩ := D.ntw.art_univ i Q
    (fun u hu hl => Finset.disjoint_left.1 hd hu (D.ntw.twistExcludedPlaces_contains_residueChar i hl)) (Subgroup.zpowers (D.ntw.zk i k))
    (by
      rintro ⟨x, n, rfl⟩
      refine ⟨k, Subtype.ext ?_⟩
      change (D.ntw.zk i k ^ n) ^ (D.ntw.l i ^ k) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        (IsPrimitiveRoot.coe_units_iff.mp (D.ntw.zk_prim i k)).pow_eq_one, one_zpow])
    (χ.codRestrict _ hv) (by rw [MonoidHom.ker_codRestrict, hker]; exact ho)
    (fun g g' h => Subtype.ext (by
      change χ g' = (χ g)⁻¹
      rw [← map_inv, eq_iff_of_reads hχ, map_inv]
      exact ha g g' h))
    (fun u hu A hA σ hσ => Subtype.ext (by
      change χ σ = 1
      rw [one_iff_of_reads hχ]
      by_contra hne
      exact hu ((hr u A hA).1 ⟨σ, hσ, hne⟩)))
  refine ⟨(Subgroup.zpowers (D.ntw.zk i k)).subtype.comp f, fun g => ?_⟩
  have h1 : f (D.ntw.art i Q g) = χ.codRestrict _ hv g := by rw [← hf]; rfl
  change ρ.emb _ = rd ρ (((f (D.ntw.art i Q g) : Subgroup.zpowers (D.ntw.zk i k)) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)
  rw [h1]
  exact hχ g

end GlobalTheory.TwistDescent
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringClassGroup_descent_of_coeffFieldTwist : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v) (Q : Finset (PlE D.host)) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∀ u ∈ Q, IsSplitPl D.host u) → Disjoint Q (D.ntw.S0 i) → IsOpen (ψ₀.ker : Set (G D.host.E D.nd.Om)) → AntiHom D.ntw.cc ψ₀ → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → RamExactly ψ₀ (↑Q : Set (PlE D.host)) → BlochKatoReduction.Gen.TrivAbove ψ₀ (D.ntw.l i) → (∃ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀) ∧ ∀ ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ, ρ.Pulls ψ ψ₀ → IntegralHeckeForms.TwOK i k Q (ψ.comp (D.ntw.art i Q)) := by
  atlas_forward_decl GlobalTheory.TwistDescent.exists_pulls_twOK
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem pulls_eq_zpow : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b b' : Bool) (v v' : D.what₂.places.Pl) (ρ : Reading i k b v) (ρ' : Reading i k b' v') (Q : Finset (PlE D.host)) (ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → ρ.Pulls ψ ψ₀ → ρ'.Pulls ψ' ψ₀ → ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ ψ' = ψ ^ a := by
  intro D i k b b' v v' ρ ρ' Q ψ ψ' ψ₀ ⟨z, hz⟩ hpow hρ hρ'
  have hl := (D.ntw.lPrime i).out
  let ι : D.ntw.Ok i k →+* FractionRing ρ.Oe := (algebraMap ρ.Oe (FractionRing ρ.Oe)).comp (algebraMap _ ρ.Oe)
  let ι' : D.ntw.Ok i k →+* FractionRing ρ'.Oe := (algebraMap ρ'.Oe (FractionRing ρ'.Oe)).comp (algebraMap _ ρ'.Oe)
  have hι : Function.Injective ι := (IsFractionRing.injective ρ.Oe (FractionRing ρ.Oe)).comp ρ.inj
  have hι' : Function.Injective ι' := (IsFractionRing.injective ρ'.Oe (FractionRing ρ'.Oe)).comp ρ'.inj
  have e1 : ∀ g, ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    fun g => (hρ g).symm
  have e1' : ∀ g, ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) = ρ'.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
    fun g => (hρ' g).symm
  have hp : ∀ g, ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) ^ (D.ntw.l i ^ k) = 1 := fun g => by
    rw [← Units.val_pow_eq_pow_val, hpow g, Units.val_one]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, by simp, ?_⟩
    ext x
    obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q x
    have h1 : ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = 1 := by simpa using hp g
    have h2 := e1 g
    have h2' := e1' g
    rw [h1, map_one, ← map_one ι] at h2
    rw [h1, map_one, ← map_one ι'] at h2'
    rw [hι' h2', zpow_one, hι h2]
  · have hN : 0 < D.ntw.l i ^ k := pow_pos hl.pos k
    haveI : NeZero (D.ntw.l i ^ k) := ⟨hN.ne'⟩
    have hζ := D.ntw.zk_prim i k
    have he : IsPrimitiveRoot (ρ.emb z) (D.ntw.l i ^ k) := hz.map_of_injective ρ.emb.injective
    have he' : IsPrimitiveRoot (ρ'.emb z) (D.ntw.l i ^ k) := hz.map_of_injective ρ'.emb.injective
    have hζe : IsPrimitiveRoot (ι (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) := hζ.map_of_injective hι
    have hζe' : IsPrimitiveRoot (ι' (D.ntw.zk i k : D.ntw.Ok i k)) (D.ntw.l i ^ k) := hζ.map_of_injective hι'
    obtain ⟨c, -, hc⟩ := he.eq_pow_of_pow_eq_one hζe.pow_eq_one
    obtain ⟨a, -, ha⟩ := hζe'.eq_pow_of_pow_eq_one he'.pow_eq_one
    have hcc : c.Coprime (D.ntw.l i ^ k) := (he.pow_iff_coprime hN c).1 (hc ▸ hζe)
    have hac : a.Coprime (D.ntw.l i ^ k) := (hζe'.pow_iff_coprime hN a).1 (ha ▸ he')
    refine ⟨((c * a : ℕ) : ℤ), ?_, ?_⟩
    · rw [Int.natAbs_natCast]
      exact (Nat.Coprime.mul hcc hac).coprime_dvd_right (dvd_pow_self _ hk.ne')
    · ext x
      obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q x
      obtain ⟨n, -, hn⟩ := hz.eq_pow_of_pow_eq_one (hp g)
      have k1 : ι ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) ^ (c * a) =
          ι ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a)) := by
        rw [e1 g, ← hn, map_pow, map_pow, ← hc, ← pow_mul, ← pow_mul]
        ring_nf
      have k2 : ι' ((ψ' (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k) =
          ι' ((D.ntw.zk i k : D.ntw.Ok i k) ^ (n * a)) := by
        rw [e1' g, ← hn, map_pow, map_pow, ← ha, ← pow_mul]
        ring_nf
      rw [← map_pow] at k1
      rw [hι' k2, zpow_natCast, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hι k1]

end GlobalTheory.LevCmp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringClassGroup_descents_differ_by_power_prime_to_l : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b b' : Bool) (v v' : D.what₂.places.Pl) (ρ : Reading i k b v) (ρ' : Reading i k b' v') (Q : Finset (PlE D.host)) (ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → ρ.Pulls ψ ψ₀ → ρ'.Pulls ψ' ψ₀ → ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ ψ' = ψ ^ a := by
  atlas_forward_decl GlobalTheory.LevCmp.pulls_eq_zpow
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp

theorem mem_range_map_iff_of_isLocalHom {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] (f : A →+* B) [IsLocalHom f] (hf : Function.Injective f) (t : FractionRing A) :
    IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t ∈ (algebraMap B (FractionRing B)).range ↔
      t ∈ (algebraMap A (FractionRing A)).range := by
  have hmap : ∀ a : A, IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf (algebraMap A _ a) =
      algebraMap B _ (f a) := fun a => by simp [IsFractionRing.map]
  constructor
  · rintro ⟨c, hc⟩
    by_cases ht : t = 0
    · exact ⟨0, by rw [ht, map_zero]⟩
    rcases ValuationRing.isInteger_or_isInteger A t with ⟨a, ha⟩ | ⟨m, hm⟩
    · exact ⟨a, ha⟩
    · have h1 : IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t *
          IsFractionRing.map (K := FractionRing A) (L := FractionRing B) hf t⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      rw [← hc, ← hm, hmap, ← map_mul] at h1
      have h2 : c * f m = 1 := IsFractionRing.injective B (FractionRing B) (by rw [h1, map_one])
      have hu : IsUnit m := (isUnit_map_iff f m).1 (IsUnit.of_mul_eq_one_right c h2)
      refine ⟨((hu.unit⁻¹ : Aˣ) : A), ?_⟩
      rw [← inv_inv t, ← hm]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul]
      simp
  · rintro ⟨a, rfl⟩
    exact ⟨f a, (hmap a).symm⟩

end GlobalTheory.LevCmp

namespace GlobalTheory.LevCmp

theorem reading_sidePl_emb : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  intro D i k b v ρ
  haveI := GlobalTheory.TwistChoice.isLocalHom_phiK i k
  haveI := ρ.loc
  have hinj : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp (BlochKatoReduction.Gen.phiK D.ntw i k)) :=
    ρ.inj.comp ((D.ntw.Ok_inj i k).comp (D.ntw.O_inj i))
  have hmap : ∀ a : D.ntw.O0 i, IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
      (algebraMap _ _ a) = algebraMap ρ.Oe _ (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k a)) := fun a => by
    simp [IsFractionRing.map]
  have key : ∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) =
      IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) hinj
        (GlobalTheory.TwistChoice.sideEmb i b x) := by
    intro x
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have hz0 : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
    have hside : GlobalTheory.TwistChoice.sideEmb i b x * algebraMap _ (FractionRing (D.ntw.O0 i)) z =
        algebraMap _ (FractionRing (D.ntw.O0 i)) y := by
      rw [← hyz, div_mul_cancel₀ _ hz0]
    have h1 := ρ.emb_side x y z hside
    have hz' : algebraMap ρ.Oe (FractionRing ρ.Oe) (algebraMap _ ρ.Oe (BlochKatoReduction.Gen.phiK D.ntw i k z)) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _), ← RingHom.comp_apply,
        map_eq_zero_iff _ hinj]
      exact nonZeroDivisors.ne_zero hz
    rw [← hyz, map_div₀, hmap, hmap, eq_div_iff hz']
    exact h1
  have hside : ∀ x : ↥D.LL0, GlobalTheory.TwistChoice.sideEmb i b x =
      (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := fun x => by
    cases b <;> rfl
  refine ⟨fun x => ?_, fun x => ?_, fun h x => ?_⟩
  · rw [ρ.emb_w, key, ← hside]
    exact mem_range_map_iff_of_isLocalHom _ hinj _
  · rw [key]
    obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 i) (GlobalTheory.TwistChoice.sideEmb i b x)
    have e : GlobalTheory.SeriesTie.sideEmb D.ntw i b x = IsFractionRing.map (K := FractionRing (D.ntw.O0 i))
        (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i) (GlobalTheory.TwistChoice.sideEmb i b x) := by
      cases b <;> rfl
    rw [e, ← hyz]
    simp [map_div₀, IsFractionRing.map, NX.toKk, BlochKatoReduction.Gen.phiK]
  · rw [key, ← hside]
    rfl

end GlobalTheory.LevCmp
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), GlobalTheory.HeightCounting.SidePl D v i b ∧ (∀ x : ↥D.LL0, ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj (NX.toKk D i k (GlobalTheory.SeriesTie.sideEmb D.ntw i b x))) ∧ ∀ (h : Function.Injective ((algebraMap (D.ntw.Ok i k) ρ.Oe).comp ((algebraMap (D.ntw.O i) (D.ntw.Ok i k)).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))))) (x : ↥D.LL0), ρ.emb (x : D.what₂.LL) = IsFractionRing.map (K := FractionRing (D.ntw.O0 i)) (L := FractionRing ρ.Oe) h (if b then D.ntw.emb0 i x else D.ntw.emb0b i x) := by
  atlas_forward_decl GlobalTheory.LevCmp.reading_sidePl_emb
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.ReadingEmb

theorem exists_ringHom_complex_extending (A : Type) [Field A] (hA : Cardinal.mk A ≤ Cardinal.continuum)
    (K : Type) [Field K] [NumberField K] (i : K →+* A) (s : K →+* ℂ) :
    ∃ ι : A →+* ℂ, ∀ x, ι (i x) = s x := by
  haveI : CharZero A := (RingHom.charZero_iff i.injective).1 inferInstance
  let B := FractionRing (MvPolynomial ℝ A)
  have hB : Cardinal.mk B = Cardinal.continuum := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hA,
      max_eq_left Cardinal.aleph0_le_continuum]
  let C := AlgebraicClosure B
  have hC : Cardinal.mk C = Cardinal.continuum := by
    refine le_antisymm ((Algebra.IsAlgebraic.cardinalMk_le_max B C).trans
      (max_le hB.le Cardinal.aleph0_le_continuum)) ?_
    rw [← hB]
    exact Cardinal.mk_le_of_injective (algebraMap B C).injective
  let j : A →+* C := (algebraMap B C).comp ((algebraMap (MvPolynomial ℝ A) B).comp MvPolynomial.C)
  haveI : CharZero C := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e, he⟩ := GlobalTheory.algClosed_continuum_ringEquiv_complex_extending C hC K (j.comp i) s
  exact ⟨e.toRingHom.comp j, fun x => he x⟩

theorem mk_le_of_finite (R S : Type) [CommRing R] [AddCommGroup S] [Module R S] [Module.Finite R S]
    (h : Cardinal.mk R ≤ Cardinal.continuum) : Cardinal.mk S ≤ Cardinal.continuum := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R S
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_fin]
  calc Cardinal.mk R ^ (n : Cardinal) ≤ Cardinal.continuum ^ (n : Cardinal) := Cardinal.power_le_power_right h
    _ ≤ Cardinal.continuum ^ Cardinal.aleph0 :=
        Cardinal.power_le_power_left Cardinal.continuum_ne_zero (Cardinal.natCast_le_aleph0)
    _ = Cardinal.continuum := Cardinal.continuum_power_aleph0

theorem exists_complex_emb : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  intro D F i k b v ρ
  haveI := D.ntw.lPrime i
  have h1 : Cardinal.mk (D.ntw.Ok i k) ≤ Cardinal.continuum := by
    have hinj : Function.Injective (fun x : D.ntw.Ok i k => ((F.eOk i k x : _) : ℂ_[D.ntw.l i])) :=
      Subtype.val_injective.comp (F.eOk i k).injective
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [(GlobalTheory.PadicCard.card_padicAlgCl_padicComplex (D.ntw.l i)).2, Cardinal.mk_complex]
  haveI := ρ.fin
  have h2 : Cardinal.mk ρ.Oe ≤ Cardinal.continuum := mk_le_of_finite (D.ntw.Ok i k) ρ.Oe h1
  exact exists_ringHom_complex_extending (FractionRing ρ.Oe) (by rw [Cardinal.mk_fractionRing]; exact h2)
    D.what₂.LL ρ.emb D.what₂.embLL

end GlobalTheory.ReadingEmb
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField : ∀ (D : D7) (F : TwFrameC D) (i : D.ntw.Tw) (k : ℕ) (b : Bool) (v : D.what₂.places.Pl) (ρ : Reading i k b v), ∃ ι : FractionRing ρ.Oe →+* ℂ, ∀ x, ι (ρ.emb x) = D.what₂.embLL x := by
  atlas_forward_decl GlobalTheory.ReadingEmb.exists_complex_emb
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.LevCmp

variable {D : D7}

theorem grpShape_of {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} {χ : J →* ℂˣ} (h1 : NG.IsProdLevel J)
    (h2 : ParaShape D η J χ)
    (h3 : ∀ k v (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∃ ψ₀ ξ, NG.LevelUni J χ s D.R.r ψ₀ ξ)
    (h4 : NG.HypOutside J χ (gPl D ∪ qPl D η)) : GrpShape D η J :=
  ⟨h1, fun v hv => let ⟨s, _, a, _, c⟩ := h2 v hv; ⟨s, a, c.mem⟩, fun k v s hs => let ⟨_, _, c⟩ := h3 k v s hs; c.mem,
    fun κ hκ => (h4 κ hκ).1⟩

theorem exists_form {η : HChar D.host.E} {J : Subgroup (GAf D.host.E D.R.nV)} (hG : GPlaces D) (h : GrpShape D η J)
    (K : Type) [Field K] (W : Type) [AddCommGroup W] [Module K W] (ρ : Representation K (GQ D.host.E D.R.nV) W)
    (hρ : ρ.IsIrreducible) (χ : J →* Kˣ) : ∃ f ∈ NX.TypeSpF D.host.E D.R.nV K ρ J χ, f ≠ 0 := by
  obtain ⟨k, ⟨v⟩⟩ := hG.2.2
  obtain ⟨h1, s, hs⟩ := hG.1 k v
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_class_trivial_stabiliser_at_typePlace D k s (hs ▸ h1)
  haveI : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have := hρ
    have h2 : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
    exact h2 (Subrepresentation.ext (Subsingleton.elim _ _))
  exact GlobalTheory.T.exists_ne_zero_algebraicModularForm_of_trivial_stabiliser _ _ K W ρ J χ g fun γ hγ hm =>
    hg γ hγ (GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces D η J hG h _ hm).1 ((GlobalTheory.T.expectedShapeLevel_integral_and_unipotent_at_typePlaces D η J hG h _ hm).2 k v s hs)

theorem para_rigid {L : Type} [Field L] [NumberField L] [IsCMField L] {n r : ℕ} {s : SplitPlace L} {V : Type} [AddCommGroup V]
    [Module ℂ V] {F : GAf L n → V} {J : Subgroup (GAf L n)} {χ χ' : J →* ℂˣ}
    {ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ} (hF : F ≠ 0) (h : NG.LevelPara J χ s r ξ)
    (hr : ∃ a : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield L)) = 1 ∧ ξ a ≠ 1)
    (h1 : ∀ κ, χ' κ = 1 ↔ χ κ = 1) (hE : ∀ κ : J, Eig F κ (χ' κ : ℂˣ)) :
    ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → (∃ c, Eig F κ c) → NG.ParaRT s r (s.loc n κ) := by
  obtain ⟨a, ha, ha'⟩ := hr
  refine GlobalTheory.T.mem_parahoric_of_scalar_action_on_ramifiedParahoricForm L n r s V F J χ' a hF ha h.mem hE (fun κ hκ ht hd => (h1 _).2 ?_) fun κ hκ ht hd e => ha' ?_
  · rw [h.chr κ hκ ht 1 hd.symm, map_one]
  · rw [← h.chr κ hκ ht a hd.symm]
    exact (h1 _).1 e

theorem cx_eq_one {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K] (e : K →+* ℂ)
    {J : Subgroup (GAf L n)} (χ : J →* Kˣ) (κ : J) : cx e χ κ = 1 ↔ χ κ = 1 := by
  rw [← Units.val_inj, cx_apply, Units.val_one, map_eq_one_iff e e.injective, Units.val_eq_one]

theorem levEq {η : HChar D.host.E} {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (he : SideRead i b k e) (hG : GPlaces D)
    (hram : ∀ (s : SplitPlace D.host.E) ξ, s.v ∈ qPl D η → NG.IsCompAt η s ξ →
      ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ,
        Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1)
    (m1 : NG.IsProdLevel m.J) (m2 : ParaShape D η m.J m.χ)
    (m3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ)
    (m4 : NG.HypOutside m.J m.χ (gPl D ∪ qPl D η)) (x0 : NX.badV D i Q ⊆ gPl D ∪ qPl D η)
    (x2 : ParaShape D η (cell X b hA j).J (cx e (cell X b hA j).χ))
    (x3 : ∀ kk v (s : SplitPlace D.host.E), s.w = D.naut.plGw kk v → ∃ ψ₀ ξ, NG.IsPsi0 s ψ₀ ∧ NG.IsCompAt η s ξ ∧
      ∀ e, SideRead i b k e → NG.LevelUni (cell X b hA j).J (cx e (cell X b hA j).χ) s D.R.r ψ₀ ξ)
    (hJ : Joint η m X b hA j) : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ) := by
  have x1 := GlobalTheory.T.isProductLevel_definiteFormsRealisationAtTwist D X i b k Q ψ hA j
  have x4 : NG.HypOutside (cell X b hA j).J (cx e (cell X b hA j).χ) (gPl D ∪ qPl D η) := fun κ hκ => by
    have h := (cell X b hA j).hyp κ fun v hv => hκ v fun h => hv fun h' => h (x0 h')
    exact ⟨h.1, fun h' => (cx_eq_one _ _ _).2 (h.2 h')⟩
  have gm := grpShape_of m1 m2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := m3 k v s hs; ⟨a, c, d⟩) m4
  have gx := grpShape_of x1 x2 (fun k v s hs => let ⟨a, c, _, _, d⟩ := x3 k v s hs; ⟨a, c, d e he⟩) x4
  obtain ⟨θ, J₁, e', V, _, _, ω, hθ, he', hω, j1, j2, j3⟩ := hJ
  obtain ⟨f, hf, hf0⟩ := exists_form hG gm ℂ _ m.wt.ρ m.wt.irr m.χ
  obtain ⟨f', hf', hf0'⟩ := exists_form hG gx _ _ (cell X b hA j).ρ (cell X b hA j).irr (cell X b hA j).χ
  obtain ⟨y, rfl⟩ : f ∈ LinearMap.range m.real := by
    rw [m.real_range]
    obtain ⟨N, hN, h⟩ := m.J_open
    refine ⟨⟨hf.1, N, hN, fun κ hκ g => ?_⟩, fun κ => funext fun g => hf.2 κ g⟩
    obtain ⟨h1, h2⟩ := h κ hκ
    have := hf.2 ⟨κ, h1⟩ g
    rwa [h2, Units.val_one, one_smul] at this
  obtain ⟨y', hy'⟩ := (cell X b hA j).real.surjective ⟨f', hf'⟩
  set F' : GAf D.host.E D.R.nV → V := fun g => ω (((cell X b hA j).real y').1 g) with hF'
  have hF0 : F' ≠ 0 := fun h => hf0' (funext fun g => hω (by
    have := congrFun h g
    rw [hF'] at this
    simp only [hy'] at this
    exact this.trans (map_zero ω).symm))
  have E1 : ∀ κ : m.J, Eig (m.real y) κ (m.χ κ : ℂˣ) := fun κ g => hf.2 κ g
  have E2 : ∀ κ : (cell X b hA j).J, Eig F' κ (cx e' (cell X b hA j).χ κ : ℂˣ) := fun κ g => by
    have := ((cell X b hA j).real y').2.2 κ g
    simp only [hF', this, map_smulₛₗ, cx_apply]
  have hr0 : 2 ≤ D.R.r := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; unfold Ranks.r; omega
  have hr1 : D.R.r < D.R.nV := by have := D.R.rank_add_five_le; unfold Ranks.nV; omega
  refine GlobalTheory.T.productLevel_eq_of_local_agreement _ _ _ _ _ _ _ (GlobalTheory.T.typePlaces_union_ramifiedPlaces_finite D η) m1 x1 m4 x4 fun u hu => ?_
  rcases hu with hu | hu
  · obtain ⟨kk, v, s, rfl, hs⟩ := hG.2.1 u hu
    obtain ⟨p, ξ, a1, a2, a3⟩ := m3 kk v s hs
    obtain ⟨p', ξ', b1, b2, b3⟩ := x3 kk v s hs
    obtain rfl := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique _ η s ξ ξ' a2 b2
    have hg := D.host.g_prime kk
    have hab : s.Above (D.host.g kk) := by
      have h1 : ((D.host.g kk : ℕ) : 𝓞 D.host.E) ∈ s.w.asIdeal := hs ▸ (hG.1 kk v).1
      show _ ∈ s.v.asIdeal
      rw [← s.w_under]
      show algebraMap _ (𝓞 D.host.E) _ ∈ s.w.asIdeal
      rwa [map_natCast]
    have key := GlobalTheory.T.additiveCharacter_eq_of_common_unipotentLevel_eigenvector _ _ _ s (D.host.g kk) (D.host.g kk - 1) θ _ _ (m.real y) F' _ _ _ _ p p' ξ ξ hg hab
      ((Nat.coprime_self_sub_left hg.one_le).2 (Nat.coprime_one_left _)) hr0 hr1.le hθ hf0 hF0 a1 b1 a3 (b3 e' he') E1 E2
      fun κ hκ hU => let ⟨c, c', h1, h2, h3⟩ := j3 κ (j2 kk v s hs κ hκ hU); ⟨c, c', h1 y, h2 y', h3 kk v s hs hκ⟩
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans ((b3 e he).mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, u2⟩ := GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral _ _ _ s _ ((a3.mem κ hκ).1 h).1
    have hne : NG.detDD s D.R.r (s.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    apply Units.ext
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, (b3 e he).chr κ h' hκ (Units.mk0 _ hne) rfl, key _ u2]
  · obtain ⟨s, ξ, rfl, a2, a3⟩ := m2 u hu
    obtain ⟨s', ξ', b1, b2, b3⟩ := x2 _ hu
    obtain ⟨s₁, c1, c2⟩ := j1 _ hu
    have hU : ∀ κ, TrivOutside {s.v} κ → NG.ParaRT s₁ D.R.r (s₁.loc _ κ) → κ ∈ Umax D.host.E D.R.nV := fun κ hκ hP =>
      (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s₁ (c1 ▸ hκ)).1 hP.1
    have hs : s' = s := GlobalTheory.T.splitPlace_eq_of_automorphism_maps_parahoric _ _ _ s s' s₁ θ (by omega) hr1 b1 c1 hθ fun κ hκ hP => by
      obtain ⟨c, c', h1, h2, -⟩ := j3 κ (c2 κ (c1 ▸ hκ) hP)
      have h3 := (hθ.1 κ).2 (hU κ hκ hP)
      have h4 := (hθ.2 _ κ).2 hκ
      exact ⟨para_rigid hf0 a3 (hram s ξ hu a2) (fun _ => Iff.rfl) E1 _ h3 h4 ⟨c, h1 y⟩,
        para_rigid hF0 b3 (hram s' ξ' (b1 ▸ hu) b2) (fun κ => (cx_eq_one _ _ _).trans (cx_eq_one _ _ _).symm) E2 _ h3
          (b1 ▸ h4) ⟨c', h2 y'⟩⟩
    subst hs
    obtain rfl := GlobalTheory.T.heckeCharacter_splitPlaceComponent_unique _ η s' ξ ξ' a2 b2
    refine fun κ hκ => ⟨(a3.mem κ hκ).trans (b3.mem κ hκ).symm, fun h h' => ?_⟩
    obtain ⟨u1, -⟩ := GlobalTheory.T.upperParahoric_lowerDet_unit_and_superdiag_integral _ _ _ s' _ ((a3.mem κ hκ).1 h)
    have hne : NG.detDD s' D.R.r (s'.loc _ κ) ≠ 0 := fun h0 => by simp [h0] at u1
    rw [a3.chr κ h hκ (Units.mk0 _ hne) rfl, b3.chr κ h' hκ (Units.mk0 _ hne) rfl]

theorem unpack {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (h : GlobalTheory.TwistChoice.HasReading p b w ψ₀) {i : D.ntw.Tw} {Q : Finset (PlE D.host)} {k : ℕ} (h1 : p.1 = i) (h2 : p.2.1 = Q)
    (h3 : p.2.2.1 = k) : ∃ (ρ : Reading i k b w) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ), ρ.Pulls ψ ψ₀ ∧ twPack D i b Q k ψ = p := by
  obtain ⟨i', Q', k', φ⟩ := p
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  obtain ⟨ρ, hρ⟩ := h
  exact ⟨ρ, _, hρ, congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) (psiAt_psiAt b φ)⟩

theorem pack_pow {i i' : D.ntw.Tw} {k k' : ℕ} {b b' : Bool} {v v' : D.what₂.places.Pl} (ρ : Reading i k b v) (ρ' : Reading i' k' b' v')
    {Q Q' : Finset (PlE D.host)} {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ' : D.ntw.RCG i' Q' →* (D.ntw.Ok i' k')ˣ}
    {ψ₀ ψ₀' : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h1 : i' = i) (h2 : Q' = Q) (h3 : k' = k) (h4 : ψ₀' = ψ₀)
    (hz : ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) (ho : ∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) (hp : ρ.Pulls ψ ψ₀)
    (hp' : ρ'.Pulls ψ' ψ₀') :
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ twPack D i' b' Q' k' ψ' = GlobalTheory.HeightCounting.twPackPow D a (twPack D i b Q k ψ) := by
  subst h1 h2 h3 h4
  obtain ⟨a, ha, rfl⟩ := GlobalTheory.T.ringClassGroup_descents_differ_by_power_prime_to_l D _ _ b b' v v' ρ ρ' _ ψ ψ' _ hz ho hp hp'
  refine ⟨if b = b' then a else -a, by split_ifs <;> simpa using ha, ?_⟩
  refine congrArg (fun ψ => (⟨i', Q', k', ψ⟩ : TwPack D)) ?_
  cases b <;> cases b'
  · exact (inv_zpow ψ a).symm
  · exact ((inv_zpow' ψ (-a)).trans (congrArg (ψ ^ ·) (neg_neg a))).symm
  · exact (zpow_neg ψ a).symm
  · rfl

theorem exists_data (hG : IsGalois ℚ ↥D.LL0) (s : D.what₂.places.Pl → D.ntw.Tw) (Q : D.what₂.places.Pl → Finset (PlE D.host))
    (k : D.what₂.places.Pl → ℕ) (ψ₀ : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ))
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v) (c2 : ∀ v, Q (D.what₂.places.conj v) = Q v)
    (c3 : ∀ v, k (D.what₂.places.conj v) = k v) (c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v)
    (hex : ∀ v b (ρ : Reading (s v) (k v) b v), ∃ ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ, ρ.Pulls ψ (ψ₀ v)) :
    ∃ (b : D.what₂.places.Pl → Bool) (ρ : ∀ v, Reading (s v) (k v) (b v) v)
      (ψ : ∀ v, D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), (∀ v, ReadsAt (s v) (b v) v) ∧ (∀ v, (ρ v).Pulls (ψ v) (ψ₀ v)) ∧
      (∀ v, D.what₂.places.conj v ≠ v → b (D.what₂.places.conj v) = !b v) ∧
      ∀ v, twPack D (s (D.what₂.places.conj v)) (b (D.what₂.places.conj v)) (Q (D.what₂.places.conj v)) (k (D.what₂.places.conj v))
        (ψ (D.what₂.places.conj v)) = twPack D (s v) (b v) (Q v) (k v) (ψ v) := by
  classical
  choose b₀ hb using hs
  have h0 : ∀ v, ∃ p : TwPack D, GlobalTheory.TwistChoice.HasReading p (b₀ v) v (ψ₀ v) ∧ p.1 = s v ∧ p.2.1 = Q v ∧ p.2.2.1 = k v := fun v => by
    obtain ⟨ρ⟩ := (hb v).nonempty_reading (k v)
    obtain ⟨ψ, hψ⟩ := hex v _ ρ
    refine ⟨twPack D (s v) (b₀ v) (Q v) (k v) ψ, ⟨ρ, ?_⟩, rfl, rfl, rfl⟩
    show ρ.Pulls (BlochKatoReduction.Gen.psiAt (b₀ v) (BlochKatoReduction.Gen.psiAt (b₀ v) ψ)) _
    rwa [psiAt_psiAt]
  choose p hp using h0
  obtain ⟨o, ho⟩ := GlobalTheory.TwistChoice.exists_orbitRep (D := D)
  let b : D.what₂.places.Pl → Bool := fun w => if o w = w then b₀ w else !b₀ (D.what₂.places.conj w)
  have h1 : ∀ v, ReadsAt (s v) (b v) v ∧ ∃ (ρ : Reading (s v) (k v) (b v) v)
      (ψ : D.ntw.RCG (s v) (Q v) →* (D.ntw.Ok (s v) (k v))ˣ), ρ.Pulls ψ (ψ₀ v) ∧ twPack D (s v) (b v) (Q v) (k v) ψ = p (o v) := fun v => by
    by_cases h2 : o v = v
    · have e : b v = b₀ v := if_pos h2
      rw [e, h2]
      exact ⟨hb v, unpack (hp v).1 (hp v).2.1 (hp v).2.2.1 (hp v).2.2.2⟩
    · have e : b v = !b₀ (D.what₂.places.conj v) := if_neg h2
      have h3 := (hb (D.what₂.places.conj v)).conj hG
      have h4 := (hp (D.what₂.places.conj v)).1.conj hG
      rw [D.what₂.places.conj_conj] at h3 h4
      rw [c1] at h3
      rw [c4] at h4
      rw [e, (ho v).1.resolve_left h2]
      exact ⟨h3, unpack h4 ((hp _).2.1.trans (c1 v)) ((hp _).2.2.1.trans (c2 v)) ((hp _).2.2.2.trans (c3 v))⟩
  choose hr ρ ψ h2 h3 using h1
  refine ⟨b, ρ, ψ, hr, h2, fun w hne => ?_, fun v => by rw [h3, h3, (ho v).2]⟩
  simp only [b, (ho w).2, D.what₂.places.conj_conj]
  rcases (ho w).1 with h | h
  · rw [if_neg (by rw [h]; exact hne.symm), if_pos h]
  · rw [if_pos h, if_neg (by rw [h]; exact hne), Bool.not_not]

abbrev kMap {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) : NX.Kk D i k →+* FractionRing ρ.Oe :=
  IsFractionRing.map (K := FractionRing (D.ntw.Ok i k)) (L := FractionRing ρ.Oe) ρ.inj

theorem reads_of_pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {v : D.what₂.places.Pl} (ρ : Reading i k b v) {Q : Finset (PlE D.host)}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} {χ : HChar D.host.E} (hp : ρ.Pulls ψ ψ₀)
    (hg : GalOf D χ ψ₀) {ι : FractionRing ρ.Oe →+* ℂ} (hι : ∀ x, ι (ρ.emb x) = D.what₂.embLL x) :
    SideRead i b k (ι.comp (kMap ρ)) ∧ ReadsHecke (ι.comp (kMap ρ)) (ψ.comp (D.ntw.art i Q)) χ := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [RingHom.comp_apply, ← (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D i k b v ρ).2.1 x, hι]
    rfl
  · obtain ⟨-, art, ha, h⟩ := hg
    refine ⟨art, ha, fun x σ e => (h x σ e).trans (Units.ext ?_)⟩
    show D.what₂.embLL (ψ₀ σ : D.what₂.LLˣ) = ι (kMap ρ (algebraMap _ _ ((ψ (D.ntw.art i Q σ) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k)))
    rw [← hι, hp σ]
    simp [IsFractionRing.map]

theorem rank_of_levEq {μ : D.what₂.Tup} {j' : ℕ} (m : MtReal D μ j') (X : NExpTied D) {i : D.ntw.Tw} (b : Bool) {k : ℕ}
    {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hA : NX.AdmTw D i k Q ψ) (j : Fin D.R.m)
    (e : NX.Kk D i k →+* ℂ) (h : LevEq m.J m.χ (cell X b hA j).J (cx e (cell X b hA j).χ)) (hw : CellWt m X b hA j e) :
    Module.finrank D.what₂.LL (D.what₂.MtL μ j') = Module.finrank (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
  haveI : FiniteDimensional (NX.Kk D i k) (D.nexp.MtV i (j.1 + 1) b k Q ψ) := by
    obtain ⟨S, hS⟩ := D.nexp.MtLat_fg i (j.1 + 1) b k Q ψ
    refine ⟨S, ?_⟩
    rw [← D.nexp.MtLat_span i (j.1 + 1) b k Q ψ, ← hS, Submodule.span_span_of_tower]
  have h1 := GlobalTheory.T.finrank_algebraicModularForms_complexification _ _ _ e _ _ _ _ _ (cell X b hA j).χ hw (cell X b hA j).J_open
    (Module.Finite.equiv (cell X b hA j).real)
  rw [(cell X b hA j).real.finrank_eq, ← h1]
  have h2 : NG.TypeSp m.wt.ρ (cell X b hA j).J (cx e (cell X b hA j).χ) = NG.TypeSp m.wt.ρ m.J m.χ := by
    obtain ⟨h3, h4⟩ := h
    ext f
    refine and_congr_right fun _ => ⟨fun H κ => ?_, fun H κ => ?_⟩
    · rw [h4 κ.1 κ.2 (h3 ▸ κ.2)]
      exact H ⟨κ.1, h3 ▸ κ.2⟩
    · rw [← h4 κ.1 (h3.symm ▸ κ.2) κ.2]
      exact H ⟨κ.1, h3.symm ▸ κ.2⟩
  rw [h2, ← m.real_range, LinearMap.finrank_range_of_inj m.real_inj]
  obtain ⟨h3, h4⟩ := D.what₂.jMt_basis μ j' (Module.Free.chooseBasis _ _)
  rw [Module.finrank_eq_nat_card_basis (Module.Free.chooseBasis _ _),
    Module.finrank_eq_nat_card_basis (Module.Basis.mk h3 h4.ge)]

theorem exists_choice (hP : PrN) (hG : IsGalois ℚ ↥D.LL0) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (M : MtFam D) (X : NExpTied D)
    (F : TwFrameC D) (xi : D.what₂.Tup → HChar D.host.E) (χ : D.what₂.places.Pl → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (k : D.what₂.places.Pl → ℕ) (s : D.what₂.places.Pl → D.ntw.Tw)
    (hs : ∀ v, ∃ b, ReadsAt (s v) b v) (c1 : ∀ v, s (D.what₂.places.conj v) = s v)
    (htp : ∀ C : NChoice D, C.Q = Q → ∃ tp : TupTied D cf C, tp.xi = xi ∧ tp.psi = χ)
    (h1 : ∀ v, IsPsi (H := D.host) (D.what₂.places.resChar v) (Q v) (χ v))
    (h2 : ∀ v, (χ v).OrderDvd (D.what₂.places.resChar v ^ k v))
    (h3 : ∀ v, ∃ z : D.what₂.LL, IsPrimitiveRoot z (D.what₂.places.resChar v ^ k v))
    (h4 : ∀ v, ¬ TwistedAt D v → Q v = ∅) (h5 : ∀ v, Disjoint (Q v) (D.ntw.S0 (s v)))
    (h6 : ∀ v v', (∀ x ∈ D.LL0, 0 ≤ D.what₂.places.val v x ↔ 0 ≤ D.what₂.places.val v' x) → k v = k v' ∧ χ v = χ v')
    (h7 : ∀ v, χ (D.what₂.places.conj v) = χ v ∧ k (D.what₂.places.conj v) = k v)
    (h8 : ∀ v b (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok (s v) (k v))ˣ) (hA : NX.AdmTw D (s v) (k v) (Q v) ψ) (j : Fin D.R.m),
      TwistedAt D v → D.ntw.l (s v) = D.what₂.places.resChar v → IntegralHeckeForms.TwOK (s v) (k v) (Q v) ψ → ∀ e, SideRead (s v) b (k v) e →
      ReadsHecke e ψ (χ v) →
      LevEq (mtAt M v j).J (mtAt M v j).χ (cell X b hA j).J (cx e (cell X b hA j).χ) ∧ CellWt (mtAt M v j) X b hA j e) :
    ∃ (C : NChoice D) (tp : TupTied D cf C), tp.xi = xi ∧ tp.psi = χ ∧ C.Q = Q ∧ C.k' = k ∧ ChoiceSide D cf M X C tp ∧
      (∀ v, IntegralHeckeForms.TwOK (C.twI v) (C.k' v) (C.Q v) ((C.psi' v).comp (D.ntw.art (C.twI v) (C.Q v)))) ∧ C.twI = s := by
  classical
  have hl : ∀ v, D.ntw.l (s v) = D.what₂.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  have hQ : ∀ v v', χ v = χ v' → Q v = Q v' := fun v v' e => Finset.ext fun u =>
    not_iff_not.1 (((h1 v).ram u).symm.trans (e ▸ (h1 v').ram u))
  let g : HChar D.host.E → ℕ → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) := fun c n =>
    @Classical.epsilon _ ⟨1⟩ fun ψ₀ => GalOf D c ψ₀ ∧ ∀ g, ψ₀ g ^ n = 1
  let ψ₀ := fun v => g (χ v) (D.ntw.l (s v) ^ k v)
  have hψ : ∀ v, GalOf D (χ v) (ψ₀ v) ∧ ∀ g, ψ₀ v g ^ (D.ntw.l (s v) ^ k v) = 1 := fun v =>
    Classical.epsilon_spec (GlobalTheory.T.exists_galoisCharacter_of_finiteOrder_heckeCharacter hP.what₂.art D (χ v) _ (pow_pos (D.ntw.lPrime _).out.pos _) (hl v ▸ h2 v) (hl v ▸ h3 v))
  have c4 : ∀ v, ψ₀ (D.what₂.places.conj v) = ψ₀ v := fun v => by simp only [ψ₀, c1, (h7 v).1, (h7 v).2]
  have hd := fun v b (ρ : Reading (s v) (k v) b v) =>
    let ⟨a1, a2, a3⟩ := GlobalTheory.T.galois_character_anti_ramified_exactly hP D _ (Q v) (χ v) (ψ₀ v) (D.ntw.lPrime (s v)).out (hl v ▸ h1 v) (hψ v).1
    GlobalTheory.T.exists_ringClassGroup_descent_of_coeffFieldTwist D (s v) (k v) b v ρ (Q v) (ψ₀ v) (h1 v).split (h5 v) (hψ v).1.1 a1 (hψ v).2 a2 a3
  obtain ⟨b, ρ, ψ, hr, hp, hb, hc⟩ := exists_data hG s Q k ψ₀ hs c1 (fun v => hQ _ _ (h7 v).1) (fun v => (h7 v).2) c4
    fun v b ρ => (hd v b ρ).1
  have hok := fun v => (hd v _ (ρ v)).2 _ (hp v)
  choose ι hι using fun v => GlobalTheory.T.exists_complexEmbedding_readingFractionRing_over_coeffField D F (s v) (k v) (b v) v (ρ v)
  have hlev := fun v hA j (hv : TwistedAt D v) =>
    let ⟨a1, a2⟩ := reads_of_pulls (ρ v) (hp v) (hψ v).1 (hι v)
    h8 v (b v) _ hA j hv (hl v) (hok v) _ a1 a2
  have hrk : ∀ v, TwistedAt D v → GlobalTheory.TwistChoice.RankEq (s v) (b v) (Q v) (k v) (ψ v) v := fun v hv j j1 j2 => by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨a1, a2⟩ := hlev v (GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v)) ⟨j, j2⟩ hv
    exact rank_of_levEq _ X _ _ ⟨j, j2⟩ _ a1 a2
  let C := GlobalTheory.TwistChoice.choiceOf s b Q k ψ hr ρ hrk
  obtain ⟨tp, t1, t2⟩ := htp C rfl
  refine ⟨C, tp, t1, t2, rfl, rfl, ⟨⟨fun a => hE.elim a, fun a => hE.elim a, fun a => hE.elim a,
    ⟨ψ₀, c4, hp, fun a => hE.elim a⟩, fun v x y z _ hx => (ρ v).emb_side x y z hx⟩,
    ⟨c1, fun v _ => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1, fun v _ x => (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).2.2 _ x, fun v _ => hb v,
      fun v v' _ _ e => ?_, fun v _ => hc v⟩, h4, fun v _ => GlobalTheory.MtRead.admissible_twist_of_twisting_character (hok v), ?_, ?_⟩, hok, rfl⟩
  · have e' : s v' = s v := e
    have key : k v' = k v ∧ χ v' = χ v := by
      have a1 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v)).1
      have a2 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ (ρ v')).1
      have a3 := (GlobalTheory.T.twistReading_induces_sideEmbedding_fixedField D _ _ _ _ ((ρ v').conj hG)).1
      rw [e'] at a2 a3
      by_cases hbb : b v' = b v
      · rw [hbb] at a2
        exact h6 _ _ fun x hx => (a2 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
      · have : (!b v') = b v := by revert hbb; cases b v <;> cases b v' <;> simp
        rw [this] at a3
        have a4 := h6 _ _ fun x hx => (a3 ⟨x, hx⟩).trans (a1 ⟨x, hx⟩).symm
        exact ⟨(h7 v').2.symm.trans a4.1, (h7 v').1.symm.trans a4.2⟩
    exact pack_pow (ρ v) (ρ v') e' (hQ _ _ key.2) key.1 (by simp only [ψ₀, e', key.1, key.2]) (hl v ▸ h3 v) (hψ v).2 (hp v) (hp v')
  · intro v _ u hu _ A σ hA hσ y hy
    obtain ⟨-, art, ha, h⟩ := (hψ v).1
    have a1 := h.val_eq ha (((h1 v).ram u).2 hu) hA hσ
    have a2 : y = (ψ₀ v σ : D.what₂.LLˣ) := D.what₂.embLL.injective (by rw [hy, t2, a1, inv_inv]; rfl)
    rw [a2]
    exact hp v σ
  · intro v j j1 j2 hv hA
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨⟨a1, a2⟩, -⟩ := hlev v hA ⟨j, j2⟩ hv
    exact ⟨ι v, hι v, a1, fun κ h h' => congrArg Units.val (a2 κ h h')⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

theorem muIsW (x : St P) : V4.MuIsW (w.st x.o.Z) f T P.Wt w.I.xi where
  inj := w.ok.xi_inj
  range := w.xi_range
  mu0 := w.l.xi0
  star := by
    show w.I.xi w.I.muStar = f.del
    rw [w.ok.xi_star, w.C_eq]
  star' := by
    show w.I.xi w.I.muStar' = f.del'
    rw [w.ok.xi_star', w.C_eq]
  tw := P.q.mu.tw
  on := P.q.mu.on
  off := P.q.mu.off
  sub := P.sub
  supp := P.supp

theorem cfOf_eq (x : St P) : cfOf x = Fr.at (w.st x.o.Z) f :=
  congrArg (Fr.at (w.st x.o.Z)) w.C_eq

theorem exists_tp (x : St P) (C : NChoice (Dof x)) (h : C.Q = QOf P) :
    ∃ tp : TupTied (Dof x) (cfOf x) C, tp.xi = w.I.xi ∧ tp.psi = T.psi := by
  rw [cfOf_eq]
  exact (GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st x.o.Z) f T P.Wt w.I.xi (muIsW x)).2.2.2 C fun v _ =>
    (congrFun h v).trans (Model.qOf_eq v)

theorem disjoint_conductorPlaces_excludedSet {Q : Finset (PlE D.host)} {i : D.ntw.Tw} (h : OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D)))
    (h1 : ∀ u ∈ Q, u ∉ placesOver D.host.E (D.ntw.l i)) (h2 : ∀ u ∈ Q, ∀ p ∈ lowAll D, u ∉ placesOver D.host.E p) :
    Disjoint Q (D.ntw.S0 i) := Finset.disjoint_left.2 fun u hu hS => by
  obtain ⟨p, hp, h3⟩ := h u hS
  rcases Finset.mem_insert.1 hp with rfl | hp
  exacts [h1 u hu h3, h2 u hu p hp h3]

theorem choices_exist_for : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SCk hL := by
  intro hCo hCW hHM hP hS hL
  refine ((GlobalTheory.T.choice_side_of_twisted hCo hCW hHM hP hS hL).and ((GlobalTheory.T.good_places_all_states hL).and (GlobalTheory.T.twistConductors_avoid_excludedPrimes.and ((GlobalTheory.T.bad_places_sub_of_admissible_twist hP hL).and ((GlobalTheory.T.side_read_hecke_of_admissible_twist hP hL).and ((GlobalTheory.T.split_place_of_admissible_twist hP hL).and
    ((GlobalTheory.T.joint_eta_of_admissible_twist hP hL).and (GlobalTheory.T.cell_weight_of_admissible_twist hP hL)))))))).trans (StepW.of_all ?_)
  rintro K B f T w - - ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ P x l s hs c1
  have hl : ∀ v, (Dof x).ntw.l (s v) = B.places.resChar v := fun v => let ⟨_, h⟩ := hs v; h.l_eq
  obtain ⟨C, tp, b1, b2, b3, b4, b5, b6, b7⟩ := exists_choice (D := Dof x) hP B.coeffGaloisSubfield_isGalois l.a.A.bare (cfOf x) l.mt.M l.b.Bs.exp
    l.b.Bs.twF w.I.xi T.psi (QOf P) T.k s hs c1 (exists_tp x) (fun v => Model.qOf_eq (P := P) v ▸ T.psi_is v) T.psi_ord P.coh.roots
    (fun v hv => Model.qOf_off v fun h => hv ((Model.twisted_iff x v).2 h))
    (fun v => disjoint_conductorPlaces_excludedSet (l.b.rootsOfUnityRing_le_wittIntegers (s v)) (fun u hu h => T.Q_l v u (Model.qOf_eq (P := P) v ▸ hu) (hl v ▸ h))
      fun u hu => a2 P x v u (Model.qOf_eq (P := P) v ▸ hu))
    (fun v v' h => (P.coh.same v v' h).2) T.conj fun v b ψ hA j hv hl' hok e he hr => by
      have hg := TupTie.good_set f T (w.xi_range ▸ Set.mem_range_self ((Dof x).what₂.muTw v))
      exact ⟨levEq _ _ b hA j e he (a1 P x l.toLA)
        (fun s' ξ => GlobalTheory.T.exists_local_unit_character_nontrivial (Dof x) (cfOf x) j _ s' ξ hg.2.1 hg.2.2) (l.mt.mt.prod v j) (l.mt.mt.para v j) (l.mt.mt.uni v j)
        (l.mt.mt.hyp v j) (a3 P x l v _ b ψ hA j hv hl' hok) (a4 P x l v _ b ψ hA j hv hl' hok e he hr)
        (a5 P x l v _ b ψ hA j hv hl' hok) (a6 P x l v _ b ψ hA j hv hl' hok), a7 P x l v _ b ψ hA j hv hl' hok e he⟩
  obtain ⟨c, hc⟩ := a0 P x l C tp b1 b2 b3 (fun v _ => congrFun b4 v) b5 fun v _ => b6 v
  exact ⟨c, hc.trans b7⟩

end GlobalTheory.LevCmp

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.statement_c_of_casselman_wallach : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SCk hL := by
  atlas_forward_decl GlobalTheory.LevCmp.choices_exist_for
end
