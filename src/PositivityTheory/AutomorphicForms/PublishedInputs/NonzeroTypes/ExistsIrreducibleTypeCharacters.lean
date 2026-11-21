import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NzOfSteps
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NeedCProps
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.GMain
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TypeExNZ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothStabiliserSubgroup
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DeterminantVector
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PDMul
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndDetK
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndExt
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Isotypic₂
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetFiniteLength2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.P_Jmul
import Mathlib.RepresentationTheory.Maschke
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.MaschkeCompactGroup
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SubrepresentationTransport
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SmoothRepIrreducibleSubcontainingVector
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowAlgebraMap
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PKill
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamBasic
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamLevi
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamUnip
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.InPowMono
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ProductIrreducible2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PProdRc
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarInertia
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SphericalUnramified
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Subquotient2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PSumList
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.UnramifiedTwist
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PUntwistRc
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.MemKCOfRedEq
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.StepV0Stable
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTpow
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Iwahori₂
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PLamMul
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Tensor2
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PExGrp
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.LeviEigenvectorMembership
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PJinv
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PNonint
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.IsClosedUnipRad
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.JacquetKernel
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTzInj
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.SupportProduct

section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

theorem gEmb (e1 : TensorProductVectors) (e2 : LeviSubgroupRestriction) (e3 : ParabolicInductionKernel) (e4 : InducedDeterminantTwist)
    (e5 : InductionExtension) : GEmb := by
  intro k _ _ _ _ n G V _ _ π hπ
  obtain ⟨X, instA, instM, σ, -, -, hdet, ⟨e⟩⟩ := hπ
  let _ := instA
  let _ := instM
  obtain ⟨v, hv0, hv⟩ := e1 k G.s G.d X σ G.μ hdet
  choose F hF using fun φ : ↥G.V0sp => e5 e2 e3 k n G X σ v hv φ.1 φ.2
  have hadd : ∀ φ ψ, F (φ + ψ) = F φ + F ψ := fun φ ψ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (φ + ψ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      have h3 := hF ψ ⟨κ, hκ⟩
      change _ = (F φ).1.1 κ + (F ψ).1.1 κ
      rw [h1, h2, h3, ← add_smul]
      rfl
  have hsmul : ∀ (c : ℂ) φ, F (c • φ) = c • F φ := fun c φ =>
    e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun κ hκ => by
      have h1 := hF (c • φ) ⟨κ, hκ⟩
      have h2 := hF φ ⟨κ, hκ⟩
      change _ = c • (F φ).1.1 κ
      rw [h1, h2, smul_smul]
      rfl
  let f0 : ↥G.V0sp →ₗ[ℂ] IndSp G.e (piTensor σ) :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  refine ⟨e.symm.toLinearEquiv.toLinearMap ∘ₗ f0, fun φ ψ h => ?_, fun κ φ φ' hφ' => ?_⟩
  · have h' : F φ = F ψ := e.symm.toLinearEquiv.injective h
    refine Subtype.ext (funext fun κ => ?_)
    have h2 := congrArg (fun F : IndSp G.e (piTensor σ) => F.1.1 (κ : GL (Fin n) k)) h'
    simp only [hF] at h2
    exact smul_left_injective ℂ hv0 h2
  · have key : F φ' = parInd G.e (piTensor σ) (κ : GL (Fin n) k) (F φ) :=
      e4 k G.s n G.d G.hd _ (piTensor σ) _ _ fun x hx => by
        rw [hF φ' ⟨x, hx⟩, parInd_apply, hF φ ⟨x * κ, mul_mem hx κ.2⟩, hφ']
        rfl
    change e.symm.toLinearEquiv (F φ') = π κ (e.symm.toLinearEquiv (F φ))
    rw [key, Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.toLinearEquiv_apply]
    exact Representation.IntertwiningMap.isIntertwining _ _ e.symm.toIntertwiningMap (κ : GL (Fin n) k) (F φ)

end UpperTheory.TNZ
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

theorem artinTransferDecomposition_holds : ArtinTransferDecompositionCharacter := by
  unfold ArtinTransferDecompositionCharacter
  intro E Ω _ _ _ _ _ A w h a ha n χ hχ
  have hs : ∀ i, GlobalTheory.WeilDeligne.IsSmooth ((χ i).comp (Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h))) := by
    intro i
    have hc : Continuous fun σ : ReciprocityTheory.Gal.Ine A =>
        Subgroup.inclusion (GlobalTheory.WeilDeligne.Weil_le_Dec h) (GlobalTheory.WeilDeligne.ineIncl h σ) :=
      continuous_subtype_val.subtype_mk _
    exact (hχ i).preimage hc
  choose μ hμ hμe using fun i => ha.factor _ (hs i)
  exact ⟨μ, hμ, fun i σ => DFunLike.congr_fun (hμe i) σ⟩

end UpperTheory.NonzeroTypeTheory
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace LocalArtinBlockProduct

theorem prod_blocks {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (G : Grp k n) {M : Type*} [CommMonoid M] (f : Fin G.s → M) :
    ∏ i, f (G.bl i) = ∏ b, f b ^ G.d b := by
  calc ∏ i, f (G.bl i) = ∏ p : (Σ a, Fin (G.d a)), f (G.bl (G.e p)) := (G.e.prod_comp (fun i => f (G.bl i))).symm
    _ = ∏ p : (Σ a, Fin (G.d a)), f p.1 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      show f ((G.e.symm (G.e p)).1) = f p.1
      rw [Equiv.symm_apply_apply]
    _ = ∏ b, f b ^ G.d b := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun b _ => ?_
      show ∏ _y : Fin (G.d b), f b = f b ^ G.d b
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem exists_unit (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    ∃ u, unitIncl (w.adicCompletion E) u = a (ineIncl h t) := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact valuation_eq_one_iff.mp (ord_eq_zero_iff.mp h0)

end LocalArtinBlockProduct

theorem localArtinCharacterProduct_holds : LocalArtinCharacterProduct := by
  intro E Ω _ _ _ _ _ A w h a ha n χ ho μ hμ G σ hG s
  obtain ⟨u, hu⟩ := LocalArtinBlockProduct.exists_unit ha s
  have key : ∀ i, ((χ i (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h s)) : ℂˣ) : ℂ) =
      ((G.chi (σ.symm i) (a (ineIncl h s)) : ℂˣ) : ℂ) := by
    intro i
    have e := DFunLike.congr_fun (hG (σ.symm i)) u
    simp only [MonoidHom.comp_apply, Equiv.apply_symm_apply] at e
    rw [hμ i, ← hu, e]
  simp only [xOf, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd, MonoidHom.comp_apply]
  rw [Finset.prod_congr rfl fun i _ => by rw [key i]]
  rw [Equiv.prod_comp σ.symm (fun j => X - C ((G.chi j (a (ineIncl h s)) : ℂˣ) : ℂ))]
  exact LocalArtinBlockProduct.prod_blocks G (fun b => X - C ((G.μ b (a (ineIncl h s)) : ℂˣ) : ℂ))

end UpperTheory.NonzeroTypeTheory
end
end

section
noncomputable section

open GlobalTheory.PRep

namespace UpperTheory.NonzeroTypeTheory

namespace TranslationCoordinates

variable {K : Type} [Group K] (W : Submodule ℂ (K → ℂ))
  (hW : ∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W)

def rW : Representation ℂ K W := sub (rightReg ℂ K ℂ) W (fun k φ hφ => hW φ hφ k)

def coord {m : ℕ} (c : W ≃ₗ[ℂ] (Fin m → ℂ)) : Representation ℂ K (Fin m → ℂ) where
  toFun k := c.toLinearMap ∘ₗ rW W hW k ∘ₗ c.symm.toLinearMap
  map_one' := by ext v i; simp
  map_mul' a b := by ext v i; simp [map_mul]

end TranslationCoordinates

theorem finiteDimensionalTranslation_holds : FiniteDimensionalTranslationCoordinates := by
  intro K _ _ W hfin hW hsm
  have := hfin
  let c := (Module.finBasis ℂ W).equivFun
  let V0 := TranslationCoordinates.coord W hW c
  let e : (Fin (Module.finrank ℂ W) → ℂ) →ₗ[ℂ] (K → ℂ) := W.subtype ∘ₗ c.symm.toLinearMap
  have he : ∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v) := by
    intro k v
    simp [e, V0, TranslationCoordinates.coord, TranslationCoordinates.rW, sub]
  have hinj : Function.Injective e := W.injective_subtype.comp c.symm.injective
  refine ⟨_, V0, e, hinj, ?_, he, ?_⟩
  · ext φ
    constructor
    · rintro ⟨v, rfl⟩
      simp [e]
    · intro hφ
      exact ⟨c ⟨φ, hφ⟩, by simp [e]⟩
  · intro v
    have hset : {g : K | V0 g v = v} = {g : K | rightReg ℂ K ℂ g (e v) = e v} := by
      ext g
      simp only [Set.mem_ofPred_eq]
      rw [← he]
      exact hinj.eq_iff.symm
    rw [hset]
    exact hsm _ (by simp [e])

end UpperTheory.NonzeroTypeTheory
end
end

section
noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace TwistedSphericalEquivalence

theorem isTwSphProd_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) k) V} {ρ' : Representation ℂ (GL (Fin n) k) W} (e : ρ.Equiv ρ')
    {s : ℕ} {d : Fin s → ℕ} {hd : ∑ a, d a = n} {η : Fin s → kˣ →* ℂˣ}
    (h : UpperTheory.TNZ.IsTwSphProd ρ' d hd η) : UpperTheory.TNZ.IsTwSphProd ρ d hd η := by
  obtain ⟨X, i1, i2, σ, hs, hi, hv, ⟨φ⟩⟩ := h
  exact ⟨X, i1, i2, σ, hs, hi, hv, ⟨Representation.Equiv.trans e φ⟩⟩

end TwistedSphericalEquivalence

theorem twistedSphericalRepresentative_holds : TwistedSphericalRepresentative := by
  intro k _ _ _ _ n V _ _ ρ h1 h2 s d hd η
  have e := GlobalTheory.LocGL.IrrGL.equivOf ρ h1 h2
  exact ⟨fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv e h, fun h => TwistedSphericalEquivalence.isTwSphProd_of_equiv (Representation.Equiv.symm e) h⟩

end UpperTheory.NonzeroTypeTheory
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

namespace DistinctCharacterUnits

theorem exists_unit_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {μ ν : kˣ →* ℂˣ} (hne : res μ ≠ res ν) : ∃ u : 𝒪[k]ˣ, μ (unitIncl k u) ≠ ν (unitIncl k u) := by
  by_contra hh
  push Not at hh
  exact hne (MonoidHom.ext hh)

end DistinctCharacterUnits

theorem distinctOnInertia_holds : DistinctOnUnitsDistinctOnInertia := by
  intro hA E Ω _ _ _ _ _ A w h a ha n G b c hbc
  obtain ⟨u, hu⟩ := DistinctCharacterUnits.exists_unit_ne (G.dist b c hbc)
  obtain ⟨t, ht⟩ := (hA E Ω A w h a ha).2 (unitIncl _ u) (valuation_eq_one_iff.mpr ⟨u, rfl⟩)
  exact ⟨t, by rw [ht]; exact hu⟩

end UpperTheory.NonzeroTypeTheory
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace P_artinIne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ}

theorem val_ine (ha : IsLocalArtin h a) (t : Ine (F := E) A) :
    valuation (w.adicCompletion E) ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
  have h0 := ha.ord_eq (ineIncl h t)
  rw [deg_ineIncl, neg_zero] at h0
  exact ord_eq_zero_iff.mp h0

theorem exists_ine (ha : IsLocalArtin h a) (u : (w.adicCompletion E)ˣ)
    (hu : valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1) :
    ∃ t : Ine (F := E) A, a (ineIncl h t) = u := by
  obtain ⟨σ, hσ⟩ := ha.surj u
  have h0 := ha.ord_eq σ
  rw [hσ, ord_eq_zero hu] at h0
  have hd : deg σ = 0 := by omega
  refine ⟨⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩, ?_⟩
  have e : ineIncl h ⟨(σ : G E Ω), deg_eq_zero_iff.mp hd⟩ = σ := Subtype.ext rfl
  rw [e, hσ]

end P_artinIne

theorem step_artinIne : ArtinInertiaProp := by
  intro E Ω _ _ _ _ _ A w h a ha
  exact ⟨P_artinIne.val_ine ha, P_artinIne.exists_ine ha⟩

end UpperTheory.TNZ
end
end

section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {n : ℕ} (G : Grp k n)

namespace P_DUnit

theorem isUnit_det_sub (A : GL (Fin n) 𝒪[k]) (a : Fin G.s)
    (hA : ∀ i j, G.bl j < G.bl i → (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k]) :
    IsUnit ((A : Matrix (Fin n) (Fin n) 𝒪[k]).submatrix
      (Subtype.val : {i : Fin n // G.bl i ≤ a} → Fin n) Subtype.val).det := by
  set M := (IsLocalRing.residue 𝒪[k]).mapMatrix (A : Matrix (Fin n) (Fin n) 𝒪[k]) with hM
  have hdet : IsUnit M.det := by
    rw [hM, ← RingHom.map_det]
    exact (Matrix.isUnits_det_units A).map _
  have htri := Matrix.twoBlockTriangular_det M (fun i => G.bl i ≤ a) (fun i hi j hj => by
    rw [hM, RingHom.mapMatrix_apply, Matrix.map_apply, IsLocalRing.residue_eq_zero_iff]
    exact hA i j (lt_of_le_of_lt hj (not_le.1 hi)))
  rw [htri] at hdet
  have h1 := isUnit_of_mul_isUnit_left hdet
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  exact h1.ne_zero

end P_DUnit

theorem step_DUnit : ModulusOnUnitsProp G := by
  intro hb g hg a
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.1 hg.1
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hA : ∀ i j, G.bl j < G.bl i →
      (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    intro i j hij
    obtain ⟨y, hy, hyx⟩ := hg.2 i j hij
    have hc : cc G.μ (G.bl j) (G.bl i) ≠ 0 := by
      have := hb.1 (G.bl j) (G.bl i) (ne_of_lt hij)
      omega
    have : y = (A : Matrix (Fin n) (Fin n) 𝒪[k]) i j := hinj (by rw [hyx]; rfl)
    rw [← this]
    exact Ideal.pow_le_self hc hy
  have hu := P_DUnit.isUnit_det_sub G A a hA
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, RingHom.map_det]
  rfl

end UpperTheory.TNZ.Grp
end
end

section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace JacquetImage

variable {n : ℕ} (G : Grp k n)

theorem leviEmb_mem_PO (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) : leviEmb k G.e m ∈ G.PO :=
  ⟨leviEmb_mem_KO (k := k) G.e hm, leviEmb_mem_parab k G.e m⟩

theorem lam_leviEmb (hL : LeviSubgroupRestriction) (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) :
    G.lam (leviEmb k G.e m) = G.eta m := by
  have h := hL k n G ⟨leviEmb k G.e m, leviEmb_mem_parab k G.e m⟩ (leviEmb_mem_PO G m hm).1
  rw [leviProj_leviEmb] at h
  exact h

end JacquetImage

theorem step_jacImage {n : ℕ} (G : Grp k n) : JacquetImageProp G := by
  intro hL hJ V _ _ π x hx m hm
  show (Submodule.Quotient.mk (π (leviEmb k G.e m) x) : Jacquet π (unipRad k G.e)) = _
  rw [hx _ (hJ.2 (JacquetImage.leviEmb_mem_PO G m hm)), JacquetImage.lam_leviEmb G hL m hm,
    Submodule.Quotient.mk_smul]

end UpperTheory.TNZ.Grp
end
end

section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace P_Jone

theorem inPow_zero (c : ℕ) : InPow c (0 : k) :=
  ⟨0, zero_mem _, map_zero _⟩

end P_Jone

theorem step_Jone {n : ℕ} (G : Grp k n) : G.JacquetOneProp := by
  refine ⟨⟨Subgroup.one_mem _, fun i j hij => ?_⟩, fun g hg => ⟨hg.1, fun i j hij => ?_⟩⟩
  · have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hij
    rw [Units.val_one, Matrix.one_apply_ne hne]
    exact P_Jone.inPow_zero _
  · rw [(mem_parab.1 hg.2) i j hij]
    exact P_Jone.inPow_zero _

end Grp

end UpperTheory.TNZ
end
end

section
noncomputable section

namespace UpperTheory.NonzeroTypeTheory

namespace SchurKernelSubmodule

def kerSub {K : Type} [Group K] {d : ℕ} (ξ : Representation ℂ K (Fin d → ℂ)) {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ K W) (g : (Fin d → ℂ) →ₗ[ℂ] W)
    (hint : ∀ k v, g (ξ k v) = ρ k (g v)) : Subrepresentation ξ :=
  ⟨LinearMap.ker g, fun k v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hint, hv, map_zero]⟩

end SchurKernelSubmodule

open SchurKernelSubmodule in
theorem schurInjective_holds : SchurInjectiveFromIrreducible := by
  intro K _ d ξ hξ W _ _ ρ g hg hint
  haveI : IsSimpleOrder (Subrepresentation ξ) := hξ
  rcases eq_bot_or_eq_top (kerSub ξ ρ g hint) with h | h
  · rw [← LinearMap.ker_eq_bot]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk
  · exfalso
    apply hg
    rw [← LinearMap.ker_eq_top]
    have hk := congrArg Subrepresentation.toSubmodule h
    first
      | exact hk
      | simpa [kerSub] using hk

end UpperTheory.NonzeroTypeTheory
end
end

section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace ParabolicMaximalCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem leviProj_mem_KO {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) (p : parab k (stdBlocks d hd))
    (hp : (p : GL (Fin n) k) ∈ KO k (Fin n)) (a : Fin s) :
    leviProj k (stdBlocks d hd) p a ∈ KO k (Fin (d a)) := by
  rw [GlobalTheory.StepData.mem_KO] at hp ⊢
  have hinv : ((GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p a)⁻¹ :
      GL (Fin (d a)) k) =
      GlobalTheory.SmGL.leviProj k (GlobalTheory.SmGL.stdBlocks d hd) p⁻¹ a := by
    rw [map_inv, Pi.inv_apply]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [GlobalTheory.SmGL.leviProj_apply]
    exact hp.1 _ _
  · rw [hinv, GlobalTheory.SmGL.leviProj_apply]
    exact hp.2 _ _

end ParabolicMaximalCompact

theorem step_parabKO : ParabolicInductionKernel := by
  intro k _ _ _ _ s n d hd p hp
  have h := fun a => ParabolicMaximalCompact.leviProj_mem_KO d hd p hp a
  exact ⟨h, deltaHalf_of_mem_leviK ((Subgroup.mem_pi _).2 fun a _ => h a)⟩

end UpperTheory.TNZ
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_sphOfUnr : SphericalOfUnramifiedProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d v hv hd
  obtain ⟨⟨n, c⟩, rfl⟩ := H.bij.2 v
  have hn : n = d := by rw [← hd, H.dim]
  subst hn
  exact ⟨c.rep.V, inferInstance, inferInstance, c.rep.ρ, c.rep.smooth, c.rep.irr, (H.sph ⟨n, c⟩).2 hv,
    congrArg rc (IrrGL.of_rep ⟨n, c⟩)⟩

end UpperTheory.TNZ
end
end

section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_twistRc : TwistRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d X _ _ σ hs hi η hη
  refine ⟨isSmooth_twist hs hη.detChar, isIrreducible_twist hi _, ?_⟩
  rw [← IrrGL.tw_of (hχ := hη), H.twist, H.one]

end UpperTheory.TNZ
end
end

section
noncomputable section

open ValuativeRel

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Uniformizer₂

lemma algebraMap_ne_zero {w : 𝒪[k]} (hw : w ≠ 0) : algebraMap 𝒪[k] k w ≠ 0 := by
  intro h
  apply hw
  exact Subtype.ext (by simpa using h)

end Uniformizer₂

theorem step_unif : UniformizerProp (k := k) := by
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  exact ⟨Units.mk0 _ (Uniformizer₂.algebraMap_ne_zero hw.ne_zero), w, hw, rfl⟩

end UpperTheory.TNZ.Grp
end
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel UpperTheory.TNZ

namespace UpperTheory.NonzeroTypeTheory

theorem cSteps_all
     :
    CSteps := by
  intro k _ _ _ _
  exact ⟨Grp.step_ccBasic (k := k), Grp.step_unif (k := k), Grp.step_exGrp (k := k), fun n G => ⟨Grp.step_ccBound (G := G), Grp.step_Jone (G := G), Grp.step_Jmul (G := G), Grp.step_Jinv (G := G), Grp.step_KC (G := G), Grp.step_DUnit (G := G), Grp.step_DMul (G := G), Grp.step_lamMul (G := G), Grp.step_lamBasic (G := G), Grp.step_lamUnip (G := G), Grp.step_iwahori (G := G), Grp.step_V0stable (G := G), Grp.step_V0fin (G := G), Grp.leviEigenvector_holds (G := G), Grp.step_PJ (G := G), Grp.step_kill (G := G), Grp.step_nonint (G := G), Grp.step_TzE (G := G), Grp.step_Tpow (G := G), Grp.step_jacKer (G := G), Grp.step_TzInj (G := G), Grp.step_jacImage (G := G), Grp.step_jacFin (G := G), Grp.step_subq (G := G), Grp.step_tensor (G := G), Grp.step_suppProd (G := G)⟩⟩

theorem types_nonzero_level_holds (P : GlobalTheory.Mem.LiteralAutomorphy.LitN)
     : NZ :=
  nz_of_steps P invariantComplement_holds minimalSubrepresentation_holds schurInjective_holds artinTransferDecomposition_holds localArtinCharacterProduct_holds finiteDimensionalTranslation_holds twistedSphericalRepresentative_holds distinctOnInertia_holds smoothVectorsFixed_holds
    (gMain step_detVec step_unrTwist step_sumList step_isotypic step_scalarInertia step_sphOfUnr step_sphUnr step_twistRc
      step_untwistRc step_prodRc step_cuspSupp step_prodIrr step_artinIne)
    (gEmb step_tensorVec step_lamLevi step_parabKO step_indDetK step_indExt) step_artinIne
    (fun L => need_CMain (cSteps_all ) step_lamLevi L) (need_CProps (cSteps_all ))
    (need_Grp (cSteps_all ))

end UpperTheory.NonzeroTypeTheory

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.NonzeroTypeTheory.exists_type_for_residual_rep :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∃ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), TypeFor r ι τ₀ :=
  fun P => UpperTheory.NonzeroTypeTheory.typeEx P (UpperTheory.NonzeroTypeTheory.types_nonzero_level_holds P )

end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
end
