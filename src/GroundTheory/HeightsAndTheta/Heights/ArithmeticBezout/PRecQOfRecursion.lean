import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemConePointsSpanX0
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussNormEqCoeffGaussNorm
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.AevalGenericIdealIff
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MemMinimalPrimesOfMemFundCycleSupport
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LinFormOneZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.HeightMul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerMul

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace VerticalPartGauss

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal coeffGaussNorm)
open ObjectsChow (genericIdeal)

section Places

variable {K : Type*} [Field K] [NumberField K] {σ : Type*}

end Places

section Generic

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {n : ℕ}

abbrev constUnits (n : ℕ) : Submonoid (MvPolynomial (Fin n) ℤ) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)

theorem algebraMap_eq : algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ) =
    map (Int.castRingHom ℚ) := by
  rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]

theorem genericIdeal_eq (P : Ideal (MRing (PBlk n))) :
    genericIdeal P = (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map
      (algebraMap (MvPolynomial (Fin n) ℤ) (MvPolynomial (Fin n) ℚ)) := by
  rw [algebraMap_eq]
  rfl

theorem finIdeal_isPrime {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).IsPrime := by
  have := hP.2.1.1
  unfold IndefiniteRowSideFullHecke.ArithBezout.finIdeal
  infer_instance

theorem disjoint_constUnits {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    Disjoint (constUnits n : Set (MvPolynomial (Fin n) ℤ)) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) := by
  rw [Set.disjoint_left]
  rintro _ ⟨k, hk, rfl⟩ hmem
  have hk0 : k ≠ 0 := nonZeroDivisors.ne_zero hk
  have h1 : (C k : MRing (PBlk n)) ∈ P := by
    simpa [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, Ideal.mem_comap, rename_C] using hmem
  have h2 : k ∈ P.comap (C : ℤ →+* MRing (PBlk n)) := h1
  rw [hP.2.2.1] at h2
  exact hk0 ((Submodule.mem_bot ℤ).mp h2)

theorem map_mem_genericIdeal_iff {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    (x : MvPolynomial (Fin n) ℤ) :
    map (Int.castRingHom ℚ) x ∈ genericIdeal P ↔ x ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P := by
  have h := IsLocalization.under_map_of_isPrime_disjoint (constUnits n) (MvPolynomial (Fin n) ℚ)
    (finIdeal_isPrime hP) (disjoint_constUnits hP)
  rw [genericIdeal_eq, ← algebraMap_eq]
  constructor
  · intro hx
    rw [← h]
    exact hx
  · exact Ideal.mem_map_of_mem _

theorem genericIdeal_isPrime {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    (genericIdeal P).IsPrime := by
  rw [genericIdeal_eq]
  exact IsLocalization.isPrime_of_isPrime_disjoint (constUnits n) _ _ (finIdeal_isPrime hP)
    (disjoint_constUnits hP)

def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv := fun ⟨(), _⟩ => rfl

theorem isHomogeneous_of_isMultiHomog {s : MRing (PBlk n)} {a : Unit → ℕ}
    (hs : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a) :
    (map (Int.castRingHom ℚ) (rename (blkEquiv n).symm s)).IsHomogeneous (a ()) := by
  refine IsHomogeneous.map ?_ _
  refine IsHomogeneous.rename_isHomogeneous ?_
  intro m hm
  have h := hs m (mem_support_iff.mpr hm) ()
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma, Fintype.sum_unique]
  simpa using h

theorem finIdeal_eq_span {P : Ideal (MRing (PBlk n))} {S : Set (MRing (PBlk n))}
    (hS : P = Ideal.span S) :
    IndefiniteRowSideFullHecke.ArithBezout.finIdeal P = Ideal.span (rename (blkEquiv n).symm '' S) := by
  have hre : ∀ x : MvPolynomial (Fin n) ℤ, rename (blkEquiv n).symm (rename (fun i : Fin n =>
      (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x) = x := fun x => by
    rw [rename_rename]
    exact rename_id_apply x
  have hre' : ∀ s : MRing (PBlk n), rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ()))
      (rename (blkEquiv n).symm s) = s := fun s => by
    rw [rename_rename]
    convert rename_id_apply s
    funext p
    rcases p with ⟨⟨⟩, i⟩
    rfl
  apply le_antisymm
  · intro x hx
    have hx' : rename (fun i : Fin n => (⟨(), i⟩ : Σ _ : Unit, PBlk n ())) x ∈ Ideal.span S := by
      rw [← hS]; exact hx
    have := Ideal.mem_map_of_mem (rename (blkEquiv n).symm : MRing (PBlk n) →ₐ[ℤ] _).toRingHom hx'
    rw [Ideal.map_span] at this
    simpa [hre] using this
  · rw [Ideal.span_le]
    rintro _ ⟨s, hs, rfl⟩
    change rename _ (rename (blkEquiv n).symm s) ∈ P
    rw [hre', hS]
    exact Ideal.subset_span hs

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem genericIdeal_isHomog {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsHomogIdeal (genericIdeal P) := by
  obtain ⟨S, hSh, hS⟩ := hP.2.1.2.1
  have hspan : genericIdeal P = Ideal.span ((fun s => map (Int.castRingHom ℚ)
      (rename (blkEquiv n).symm s)) '' S) := by
    rw [ObjectsChow.genericIdeal, finIdeal_eq_span hS, Ideal.map_span, ← Set.image_comp]
    rfl
  have hhom : (genericIdeal P).IsHomogeneous (homogeneousSubmodule (Fin n) ℚ) := by
    rw [hspan]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨a, ha⟩ := hSh s hs
    exact ⟨a (), (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_of_isMultiHomog ha)⟩
  intro f hf i
  have := hhom i hf
  rwa [← decomposition.decompose'_apply]

theorem genericIdeal_isRelevant {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsRelevant (genericIdeal P) := by
  obtain ⟨j, hj⟩ := (ObjectsChow.isRelevant_finIdeal_iff P).mpr hP.2.1.2.2
  refine ⟨j, fun h => hj ((map_mem_genericIdeal_iff hP (X j)).mp ?_)⟩
  rwa [map_X]

theorem isProjPrime_genericIdeal {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d) :
    IsProjPrime (genericIdeal P) :=
  ⟨genericIdeal_isPrime hP, genericIdeal_isHomog hP, genericIdeal_isRelevant hP⟩

theorem linForm_not_mem_genericIdeal {P : Ideal (MRing (PBlk n))} {d : ℕ} (hP : IsArithVar P d)
    {u : Fin n → ℤ} (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    linForm (fun j => (u j : ℚ)) ∉ genericIdeal P := by
  intro h
  have hmap : linForm (fun j => (u j : ℚ)) = map (Int.castRingHom ℚ) (linForm u) := by
    simp [linForm, map_sum]
  rw [hmap, map_mem_genericIdeal_iff hP, ObjectsChow.linForm_mem_finIdeal] at h
  exact hu h

end Generic

theorem isChowForm_genericIdeal {n e δ : ℕ} {P : Ideal (MRing (PBlk n))} (hP : IsArithVar P (e + 1))
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f)) :
    IsChowForm (genericIdeal P) (e + 1) f := by
  obtain ⟨c, hc, g, hcg, hg⟩ := ObjectsChow.ComplexChowFormToChowForm.proof n e δ P _ hP hf
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hg.1
  have hcoef := congrArg (coeff m) hcg
  rw [coeff_map, coeff_C_mul, coeff_map] at hcoef
  have hm' : ((g.coeff m : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hm
  have hcq : c = ((f.coeff m / g.coeff m : ℚ) : ℂ) := by
    rw [Rat.cast_div, eq_div_iff hm']
    simpa using hcoef.symm
  have hfq : f = C (f.coeff m / g.coeff m) * g := by
    apply map_injective (Rat.castHom ℂ) (Rat.castHom ℂ).injective
    rw [hcg, map_mul, map_C, hcq]
    rfl
  have hq : f.coeff m / g.coeff m ≠ 0 := by
    intro h
    apply hc
    rw [hcq, h, Rat.cast_zero]
  rw [hfq]
  exact ObjectsChow.isChowForm_C_mul hg hq

end VerticalPartGauss

end GroundTheory.Heights₂.Heights
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

namespace DivCycleGeneric

open MvPolynomial

section Localization

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] (S : Submonoid A)
  [IsLocalization S A']

theorem length_eq (J W : Ideal A) [W.IsPrime] (hW : Disjoint (S : Set A) W)
    [(W.map (algebraMap A A')).IsPrime] :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) =
      Module.length (Localization.AtPrime (W.map (algebraMap A A')))
        (Localization.AtPrime (W.map (algebraMap A A')) ⧸
          (J.map (algebraMap A A')).map (algebraMap A' (Localization.AtPrime (W.map (algebraMap A A'))))) := by
  set W' := W.map (algebraMap A A')
  set L := Localization.AtPrime W'
  have hc : W'.comap (algebraMap A A') = W :=
    IsLocalization.under_map_of_isPrime_disjoint S A' ‹_› hW
  have hL : IsLocalization.AtPrime L W := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S L W'
    convert this using 2 ; exact hc.symm
  let e : Localization.AtPrime W ≃ₐ[A] L := IsLocalization.algEquiv W.primeCompl _ _
  let _ : Algebra (Localization.AtPrime W) L := e.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower A (Localization.AtPrime W) L :=
    IsScalarTower.of_algebraMap_eq fun a => (e.commutes a).symm
  let g := (J : Submodule A A).toLocalizedQuotient' L W.primeCompl (Algebra.linearMap A L)
  have h1 := ((IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq
  have h2 := Module.length_eq_of_surjective (S := Localization.AtPrime W) (R := L)
    (M := L ⧸ (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L)) e.surjective
  have h3 : (J : Submodule A A).localized' L W.primeCompl (Algebra.linearMap A L) =
      (J.map (algebraMap A A')).map (algebraMap A' L) := by
    rw [Submodule.localized'_eq_span, Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map]
    rfl
  rw [h1, h2, h3]

end Localization

section Generic

variable {n : ℕ}

def blkEquiv (n : ℕ) : (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ≃ Fin n where
  toFun p := p.2
  invFun := blk n
  left_inv _ := rfl
  right_inv _ := rfl

theorem blkEquiv_apply (i : Fin n) : blkEquiv n ⟨(), i⟩ = i := rfl

def toGeneric (n : ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n) →+* MvPolynomial (Fin n) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)).comp (rename (R := ℤ) (blkEquiv n)).toRingHom

abbrev genericAlgebra (n : ℕ) :
    Algebra (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ) :=
  (toGeneric n).toAlgebra

attribute [local instance] genericAlgebra

abbrev intUnits (n : ℕ) : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))

instance isLocalization_generic (n : ℕ) : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) (R := ℤ) (S := ℚ)
  have : IsLocalization (intUnits n) (MvPolynomial (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ℚ) :=
    MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  refine IsLocalization.isLocalization_of_algEquiv (intUnits n)
    (AlgEquiv.ofRingEquiv (f := (renameEquiv ℚ (blkEquiv n)).toRingEquiv) fun x => ?_)
  show (renameEquiv ℚ (blkEquiv n)) (MvPolynomial.map (algebraMap ℤ ℚ) x) =
    MvPolynomial.map (Int.castRingHom ℚ) (rename (blkEquiv n) x)
  rw [renameEquiv_apply, map_rename, algebraMap_int_eq]

theorem algebraMap_generic :
    algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ) =
      toGeneric n := rfl

theorem genericIdeal_eq (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    genericIdeal W = W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) := by
  have h : IndefiniteRowSideFullHecke.ArithBezout.finIdeal W = W.map (renameEquiv ℤ (blkEquiv n)).toRingEquiv := by
    rw [IndefiniteRowSideFullHecke.ArithBezout.finIdeal, ← Ideal.comap_symm]
    rfl
  rw [genericIdeal, h]
  show Ideal.map _ (Ideal.map (rename (R := ℤ) (blkEquiv n)).toRingHom W) = _
  rw [Ideal.map_map, algebraMap_generic]
  rfl

theorem disjoint_iff_isHorizontal (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) :
    Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
      (W : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal, Set.disjoint_left, eq_bot_iff]
  constructor
  · intro h m hm
    rw [Ideal.mem_bot]
    by_contra h0
    exact h ⟨m, mem_nonZeroDivisors_of_ne_zero h0, rfl⟩ hm
  · rintro h _ ⟨m, hm, rfl⟩ hW
    exact nonZeroDivisors.ne_zero hm (Ideal.mem_bot.mp (h hW))

theorem algebraMap_linForm (u : Fin n → ℤ) :
    algebraMap _ (MvPolynomial (Fin n) ℚ) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) = linForm fun j => (u j : ℚ) := by
  simp [algebraMap_generic, toGeneric, IndefiniteRowSideFullHecke.ArithBezout.linForm, linForm, blkEquiv_apply,
    ReciprocityTheory.ChartRestriction.G.Geo.Xc]

theorem map_comap_horizontal (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
    (hW : W.IsPrime) (hh : ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W) :
    (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).comap (algebraMap _ (MvPolynomial (Fin n) ℚ)) = W :=
  IsLocalization.under_map_of_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ) hW
    ((disjoint_iff_isHorizontal W).mpr hh)

open Classical in

theorem proof : Statement := by
  intro n e P u _ _
  set J := P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}
  have hJ : genericIdeal P ⊔ Ideal.span {linForm fun j => (u j : ℚ)} =
      J.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, algebraMap_linForm, genericIdeal_eq]
  have hX : ∀ j : Fin n, algebraMap _ (MvPolynomial (Fin n) ℚ)
      (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) = X j := fun j => by
    simp [algebraMap_generic, toGeneric, blkEquiv_apply]
  have hsub : (↑((ReciprocityTheory.ChartRestriction.G.Geo.divCycle P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)).filter
      ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal).support :
        Set (Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))) ⊆
        {W | W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W} := by
    intro W hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff, Finsupp.filter_apply] at hW
    split_ifs at hW with hh
    · refine ⟨?_, hh⟩
      by_contra hp
      apply hW
      show (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then _ else 0) = 0
      rw [if_neg fun h => hp h.1.1.1]
    · exact absurd rfl hW
  have hinj : Set.InjOn genericIdeal {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) |
      W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsHorizontal W} := by
    intro W₁ h₁ W₂ h₂ h
    rw [genericIdeal_eq, genericIdeal_eq] at h
    have := congrArg (Ideal.comap (algebraMap (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))
      (MvPolynomial (Fin n) ℚ))) h
    rwa [map_comap_horizontal W₁ h₁.1 h₁.2, map_comap_horizontal W₂ h₂.1 h₂.2] at this
  ext W'
  rw [divCycle, fundCycle, Finsupp.onFinset_apply, hJ]
  by_cases hW' : W'.IsPrime
  · obtain ⟨W, hWp, hWd, rfl⟩ : ∃ W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)),
        W.IsPrime ∧ Disjoint (intUnits n : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)))
          (W : Set (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))) ∧
          W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) = W' := by
      rw [IsLocalization.isPrime_iff_isPrime_disjoint (intUnits n) (MvPolynomial (Fin n) ℚ)] at hW'
      exact ⟨_, hW'.1, hW'.2, IsLocalization.map_under (intUnits n) (MvPolynomial (Fin n) ℚ) W'⟩
    have hh := (disjoint_iff_isHorizontal W).mp hWd
    have hc := map_comap_horizontal W hWp hh
    conv_rhs => rw [← genericIdeal_eq W, Finsupp.mapDomain_apply' _ _ hsub hinj ⟨hWp, hh⟩]
    rw [Finsupp.filter_apply, if_pos hh]
    show _ = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) then
      ReciprocityTheory.ChartRestriction.G.Geo.multAt J W else 0
    have hmem : W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ∈
        relComps (J.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔
          W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := by
      have hrel : IsRelevant (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) ↔
          ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W := by
        have hXm : ∀ j : Fin n, X j ∈ W.map (algebraMap _ (MvPolynomial (Fin n) ℚ)) ↔
            (X ⟨(), j⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) ∈ W := fun j => by
          rw [← hX, ← Ideal.mem_comap, hc]
        simp only [IsRelevant, ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, hXm]
        exact ⟨fun ⟨j, hj⟩ k => ⟨j, by cases k; exact hj⟩, fun h => h ()⟩
      simp only [relComps, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq, hrel,
        IsLocalization.minimalPrimes_map (intUnits n) (MvPolynomial (Fin n) ℚ), Set.mem_preimage]
      rw [show Ideal.under _ (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))) = W from hc]
    have : (W.map (algebraMap _ (MvPolynomial (Fin n) ℚ))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp hWd
    by_cases hm : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u)
    · rw [if_pos (hmem.mpr hm), if_pos hm, localMult, dif_pos this, ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hWp,
        length_eq (A' := MvPolynomial (Fin n) ℚ) (intUnits n) J W hWd]
    · rw [if_neg (fun h => hm (hmem.mp h)), if_neg hm]
  · rw [if_neg fun h => hW' h.1.1.1]
    symm
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    refine Finset.sum_eq_zero fun W hW => ?_
    dsimp only
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    obtain ⟨hWp, hh⟩ := hsub hW
    apply hW'
    rw [genericIdeal_eq]
    exact IsLocalization.isPrime_of_isPrime_disjoint (intUnits n) _ W hWp ((disjoint_iff_isHorizontal W).mpr hh)

end Generic

end DivCycleGeneric

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp Xc)

theorem isMultiHomog_linForm {n : ℕ} (u : Fin n → ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (fun _ => 1) := by
  classical
  intro m hm k
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  rw [C_mul_X_eq_monomial] at hi
  have hmi := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hi)
  subst hmi
  cases k
  simp [Finsupp.single_apply]

theorem DivSuppHorizontalArithVar.proof : DivSuppHorizontalArithVar.Statement := by
  intro n d P u H hP hu hH hHor
  obtain ⟨hK, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  obtain ⟨hHmin, hHrel⟩ := hH
  have := hPp
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.dim_quot_minimal_add_one P H _ hu hHmin
  rw [hPdim] at h1
  refine ⟨hK, ⟨hHmin.1.1, ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_mem_minimalPrimes hPh
    (isMultiHomog_linForm u) hHmin, hHrel⟩, hHor,
    ReciprocityTheory.ChartRestriction.G.Geo.withBot_eq_of_add_one ?_⟩
  rw [h1, show d + 1 + Fintype.card Unit = d + Fintype.card Unit + 1 by omega]

end ObjectsChow

end GroundTheory.Heights₂.Heights
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

namespace RecQOfRecursion

open MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsHorizontal divSupp multAt geoNum charOf arInt)

variable {n : ℕ}

theorem ne_zero_of_isChowFormCycle {F : Type*} [Field F] {Z : ProjCycle F n} {k : ℕ}
    {f : MvPolynomial (Fin k × Fin n) F} (hf : IsChowFormCycle Z k f) : f ≠ 0 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hf
  exact mul_ne_zero (C_ne_zero.mpr hc)
    (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)

theorem exists_C_mul_of_isChowForm {F : Type*} [Field F] {I : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {f g : MvPolynomial (Fin k × Fin n) F} (hf : IsChowForm I k f) (hg : IsChowForm I k g) :
    ∃ r : F, r ≠ 0 ∧ g = C r * f := by
  obtain ⟨a, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨b, hb⟩ : f * a ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
  have hab : a * b = 1 := by
    apply mul_left_cancel₀ hf.1
    rw [mul_one, ← mul_assoc, ← hb]
  obtain ⟨r, hr, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := a)).mp (isUnit_iff_exists_inv.mpr ⟨b, hab⟩)
  exact ⟨r, hr.ne_zero, mul_comm _ _⟩

theorem map_genericIdeal (P : Ideal (MRing (PBlk n))) :
    (ObjectsChow.genericIdeal P).map (MvPolynomial.map (Rat.castHom ℂ)) = complexFibreIdeal P := by
  have h : (MvPolynomial.map (Rat.castHom ℂ)).comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) := by
    refine RingHom.ext fun p => ?_
    rw [RingHom.comp_apply, MvPolynomial.map_map]
    congr 1
  rw [ObjectsChow.genericIdeal, Ideal.map_map, h]
  rfl

theorem logFormNorm_eq (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S) (u : Fin n → ℤ) :
    IndefiniteRowSideFullHecke.ArithBezout.logFormNorm S hS (fun i => (u i : ℂ)) =
      ReciprocityTheory.ChartRestriction.G.Geo.logNorm (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) (IndefiniteRowSideFullHecke.ArithBezout.linForm u) := by
  funext z
  simp [IndefiniteRowSideFullHecke.ArithBezout.logFormNorm, ReciprocityTheory.ChartRestriction.G.Geo.logNorm, IndefiniteRowSideFullHecke.ArithBezout.linForm,
    ReciprocityTheory.ChartRestriction.G.Geo.Xc]

open Classical in

theorem divCycle_apply (P : Ideal (MRing (PBlk n))) (s : MRing (PBlk n)) (W : Ideal (MRing (PBlk n))) :
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W = if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0 :=
  rfl

def archData (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u) :
    ArchData ℚ n where
  normAt _ := ObjectsHeight.ofPointMatrix S hS
  conj_norm _ u := by rw [ObjectsHeight.ofPointMatrix_norm, ObjectsHeight.ofPointMatrix_norm, hconj]

theorem integral_eq (hC : ComplexFibreCycle.Statement) (hI : ConeIntegralPts.Statement)
    (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hsf : specFirst f (fun j => (u j : ℚ)) ≠ 0) :
    ∑ σ : ℚ →+* ℂ, cycleIntegral ((archData S hS hconj).normAt σ)
        (fundCycle ((ObjectsChow.genericIdeal P).map (MvPolynomial.map σ))) e
        (fsLog ((archData S hS hconj).normAt σ) fun j => σ (u j : ℚ)) =
      arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
        (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS) := by
  have hu : (fun j => (Rat.castHom ℂ) (u j : ℚ)) = fun j => (u j : ℂ) := funext fun j => by simp
  rw [Fintype.sum_subsingleton _ (Rat.castHom ℂ), hu, map_genericIdeal]
  have hW : ∀ W ∈ (fundCycle (complexFibreIdeal P)).support, linForm (fun j => (u j : ℂ)) ∉ W := by
    refine ((hC n e δ P _ hP hf).2.2 _).mp ?_
    have h : IndefiniteRowSideFullHecke.ArithBezout.specFirst (fun j => (u j : ℂ)) (map (Rat.castHom ℂ) f) =
        map (Rat.castHom ℂ) (specFirst f fun j => (u j : ℚ)) := by
      rw [ObjectsChow.specFirst_eq, ObjectsChow.map_specFirst, ← hu]
      rfl
    rw [h]
    exact fun h0 => hsf (map_injective _ (Rat.castHom ℂ).injective (by rw [h0, map_zero]))
  exact (hI n e S hS P _ hP hW).trans (by rw [logFormNorm_eq]; rfl)

theorem step (hRec : ChowHeightRecursionRat.Statement) (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    (hP : IsArithVar P (e + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) e δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P) :
    IndefiniteRowSideFullHecke.ArithBezout.chowHeight S f δ =
                              chowHt (archData S hS hconj) e δ (specFirst f fun j => (u j : ℚ)) +
                                (IndefiniteRowSideFullHecke.ArithBezout.vertPart P e (IndefiniteRowSideFullHecke.ArithBezout.linForm u) -
                                  arInt P (IndefiniteRowSideFullHecke.ArithBezout.linForm u) (IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)
                                    (fun _ : Fin e => IndefiniteRowSideFullHecke.ArithBezout.hermLine S hS)) ∧
      IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) e
        (specFirst f fun j => (u j : ℚ)) := by
  have hprime := VerticalPartGauss.isProjPrime_genericIdeal hP
  have hfA := VerticalPartGauss.isChowForm_genericIdeal hP hf
  have huA := VerticalPartGauss.linForm_not_mem_genericIdeal hP hu
  have hcyc := hSec ℚ n e (ObjectsChow.genericIdeal P) f _ hprime hfA huA
  have hcast : ∀ j, (((u j : ℤ) : 𝓞 ℚ) : ℚ) = (u j : ℚ) := fun j => by simp
  have key := hRec n e δ (archData S hS hconj) (ObjectsChow.genericIdeal P) f
    (fun j => ((u j : ℤ) : 𝓞 ℚ)) hprime hfA (ObjectsChow.isMultiHomog_of_isChowForm hf)
    (by simp only [hcast]; exact huA)
  simp only [hcast] at key
  refine ⟨?_, hcyc⟩
  rw [← ObjectsHeight.chowHt_eq_chowHeight (archData S hS hconj) S hS
      (fun _ u => ObjectsHeight.ofPointMatrix_norm S hS u), key, hV n e P u hP hu,
    integral_eq hC hI S hS hconj hP hf (ne_zero_of_isChowFormCycle hcyc), Module.finrank_self]
  simp

open Classical in

theorem horizontal (hMul : ChowHeightMul.Statement) (S : Matrix (Fin n) (Fin n) ℂ) (hS : IsUnit S)
    (hconj : ∀ u : Fin n → ℂ, IndefiniteRowSideFullHecke.ArithBezout.formNorm S (star u) = IndefiniteRowSideFullHecke.ArithBezout.formNorm S u)
    {e δ : ℕ} {P : Ideal (MRing (PBlk n))} {f : MvPolynomial (Fin (e + 1 + 1) × Fin n) ℚ} {u : Fin n → ℤ}
    {g : Ideal (MRing (PBlk n)) → MvPolynomial (Fin (e + 1) × Fin n) ℚ} {d : Ideal (MRing (PBlk n)) → ℕ}
    (hP : IsArithVar P (e + 1 + 1))
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P) (e + 1) δ
      (map (Rat.castHom ℂ) f))
    (hu : IndefiniteRowSideFullHecke.ArithBezout.linForm u ∉ P)
    (hg : ∀ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u), IsHorizontal W →
      ReciprocityTheory.ChartRestriction.G.Geo.IsChowForm (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal W) e (d W)
        (map (Rat.castHom ℂ) (g W)))
    (hcyc : IsChowFormCycle (divCycle (ObjectsChow.genericIdeal P) fun j => (u j : ℚ)) (e + 1)
      (specFirst f fun j => (u j : ℚ))) :
    chowHt (archData S hS hconj) (e + 1) δ (specFirst f fun j => (u j : ℚ)) =
      ∑ᶠ W ∈ divSupp P (IndefiniteRowSideFullHecke.ArithBezout.linForm u),
        (multAt (P ⊔ Ideal.span {IndefiniteRowSideFullHecke.ArithBezout.linForm u}) W : ℝ) *
          (if IsHorizontal W then IndefiniteRowSideFullHecke.ArithBezout.chowHeight S (g W) (d W) else 0) := by
  set s := IndefiniteRowSideFullHecke.ArithBezout.linForm u
  set Zh := (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s).filter IsHorizontal with hZh
  have hmem : ∀ W ∈ Zh.support, W ∈ divSupp P s ∧ IsHorizontal W := by
    intro W hW
    rw [hZh, Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff, divCycle_apply] at hW
    exact ⟨by_contra fun h => hW.1 (if_neg h), hW.2⟩
  have hgA : ∀ W ∈ Zh.support, IsChowForm (ObjectsChow.genericIdeal W) (e + 1) (g W) := fun W hW =>
    VerticalPartGauss.isChowForm_genericIdeal
      (ObjectsChow.DivSuppHorizontalArithVar.proof n (e + 1) P u W hP hu (hmem W hW).1 (hmem W hW).2)
      (hg W (hmem W hW).1 (hmem W hW).2)
  have hsfne := ne_zero_of_isChowFormCycle hcyc
  obtain ⟨c, hc, g', hg', hsf⟩ := hcyc
  have hD := ObjectsChow.DivCycleGeneric.proof n (e + 1) P u hP hu
  rw [hD] at hsf hg'
  have hpos : ∀ W ∈ Zh.support,
      ObjectsChow.genericIdeal W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support := by
    intro W hW
    rw [Finsupp.mem_support_iff, Finsupp.mapDomain, Finsupp.sum_apply]
    have h1 := Finset.single_le_sum (f := fun a => Finsupp.single (ObjectsChow.genericIdeal a) (Zh a)
      (ObjectsChow.genericIdeal W)) (fun _ _ => Nat.zero_le _) hW
    simp only [Finsupp.single_eq_same] at h1
    exact (lt_of_lt_of_le (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)) h1).ne'
  have hr : ∀ W ∈ Zh.support, ∃ r : ℚ, r ≠ 0 ∧ g' (ObjectsChow.genericIdeal W) = C r * g W :=
    fun W hW => exists_C_mul_of_isChowForm (hgA W hW) (hg' _ (hpos W hW))
  choose! r hr0 hr using hr
  have hsf' : specFirst f (fun j => (u j : ℚ)) =
      C (c * ∏ W ∈ Zh.support, r W ^ Zh W) * ∏ W ∈ Zh.support, g W ^ Zh W := by
    have hprod : ∏ W ∈ (Zh.mapDomain ObjectsChow.genericIdeal).support,
        g' W ^ (Zh.mapDomain ObjectsChow.genericIdeal) W =
          Zh.prod fun W m => g' (ObjectsChow.genericIdeal W) ^ m :=
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    rw [hsf, hprod, Finsupp.prod, Finset.prod_congr rfl (fun W hW =>
      show g' (ObjectsChow.genericIdeal W) ^ Zh W = C (r W ^ Zh W) * g W ^ Zh W by
        rw [hr W hW, mul_pow, map_pow]), Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]
  have hgne : ∀ W ∈ Zh.support, g W ≠ 0 := fun W hW => (hgA W hW).1
  have hgm : ∀ W ∈ Zh.support, IsMultiHomog (d W) (g W) := fun W hW =>
    ObjectsChow.isMultiHomog_of_isChowForm (hg W (hmem W hW).1 (hmem W hW).2)
  have hc' : c * ∏ W ∈ Zh.support, r W ^ Zh W ≠ 0 :=
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hr0 W hW))
  have hδ : δ = ∑ W ∈ Zh.support, Zh W * d W := by
    have h1 : IsMultiHomog δ (specFirst f fun j => (u j : ℚ)) :=
      (ObjectsChow.isMultiHomog_of_isChowForm hf).specFirst _
    have h2 : IsMultiHomog (∑ W ∈ Zh.support, Zh W * d W) (specFirst f fun j => (u j : ℚ)) := by
      rw [hsf']
      unfold IsMultiHomog
      have := (isWeightedHomogeneous_C (groupWeight (e + 1) n) (c * ∏ W ∈ Zh.support, r W ^ Zh W)).mul
        (IsWeightedHomogeneous.prod Zh.support (fun W => g W ^ Zh W)
          (fun W => Zh W • fun _ : Fin (e + 1) => d W) fun W hW => (hgm W hW).pow (Zh W))
      convert this using 1
      funext i
      simp [Finset.sum_apply]
    exact congrFun (IsWeightedHomogeneous.inj_right hsfne h1 h2) 0
  rw [hsf', hδ, chowHt_C_mul_prod hMul _ Zh.support (⇑Zh) d g hgne hc']
  simp_rw [ObjectsHeight.chowHt_eq_chowHeight (archData S hS hconj) S hS
    (fun _ u => ObjectsHeight.ofPointMatrix_norm S hS u)]
  rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
  refine (Finset.sum_subset (fun W hW => (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mpr
    (hmem W hW).1) ?_).trans (Finset.sum_congr rfl fun W hW => ?_)
  · intro W _ hW
    rw [Finsupp.mem_support_iff, not_not] at hW
    rw [hW, Nat.cast_zero, zero_mul]
  · have hWd : W ∈ divSupp P s := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).mem_toFinset.mp hW
    rw [hZh, Finsupp.filter_apply, divCycle_apply, if_pos hWd]
    split_ifs <;> simp

end RecQOfRecursion

open RecQOfRecursion in

theorem RecQOfRecursion.proof (hSec : ChowFormSection.Statement)
    (hV : ObjectsChow.VertPartEq.Statement) (hC : ComplexFibreCycle.Statement)
    (hI : ConeIntegralPts.Statement) : RecQOfRecursion.Statement := by
  intro hRec n S hS hconj
  refine ⟨fun δ P f u hP hf hu => ?_, fun e δ P f u g d hP hf hu hg => ?_⟩
  · obtain ⟨h, hcyc⟩ := step hRec hSec hV hC hI S hS hconj hP hf hu
    rw [h, chowHt_zero_groups_eq_zero _ _ (ne_zero_of_isChowFormCycle hcyc), zero_add]
  · obtain ⟨h, hcyc⟩ := step hRec hSec hV hC hI S hS hconj hP hf hu
    rw [h, horizontal (chowHeightMul_of_mahlerMul mahlerMul) S hS hconj hP hf hu hg hcyc,
      IndefiniteRowSideFullHecke.ArithBezout.vertPart, ← add_sub_assoc,
      ← finsum_mem_add_distrib (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite _ _)]
    congr 1
    refine finsum_mem_congr rfl fun W _ => ?_
    split_ifs <;> ring

end

end GroundTheory.Heights₂.Heights
end
