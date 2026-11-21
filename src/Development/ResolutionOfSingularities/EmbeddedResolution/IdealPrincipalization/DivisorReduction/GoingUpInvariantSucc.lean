import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.StrictTransformLogDerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupLogDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant

section
universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def iSupIdealSheaf {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData) :
    Y.IdealSheafData where
  ideal U := ⨆ i, (J i).ideal U
  map_ideal_basicOpen := by
    intro U f
    simp only [Ideal.map_iSup]
    exact iSup_congr fun i => (J i).map_ideal_basicOpen U f

private theorem pointwiseSup_ideal {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData)
    (U : Y.affineOpens) : (iSupIdealSheaf J).ideal U = ⨆ i, (J i).ideal U := rfl

private theorem ideal_iSup_le_iSup_ideal {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData)
    (U : Y.affineOpens) : (⨆ i, J i).ideal U ≤ ⨆ i, (J i).ideal U := by
  have h : (⨆ i, J i) ≤ iSupIdealSheaf J := by
    refine iSup_le fun i => Scheme.IdealSheafData.le_def.mpr fun V => ?_
    rw [pointwiseSup_ideal J V]
    exact le_iSup (fun i' => (J i').ideal V) i
  have h2 := Scheme.IdealSheafData.le_def.mp h U
  rwa [pointwiseSup_ideal J U] at h2

private theorem idealSheafData_mul_le_mul_left {Y : Scheme.{u}} (F : Y.IdealSheafData)
    {A B : Y.IdealSheafData} (h : A ≤ B) : F * A ≤ F * B := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  have e1 : (F * A).ideal U = F.ideal U * A.ideal U := rfl
  have e2 : (F * B).ideal U = F.ideal U * B.ideal U := rfl
  rw [e1, e2]
  exact Ideal.mul_mono le_rfl (Scheme.IdealSheafData.le_def.mp h U)

theorem logDerivIdealSheaf_iSup_le (k : Type u) [CommRing k] [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (P : Y.IdealSheafData)
    {ι : Sort v} (J : ι → Y.IdealSheafData) :
    logDerivIdealSheaf k p P (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheaf k p P (J i) := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  refine le_trans (@logDerivIdeal_mono k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) _ _
    (ideal_iSup_le_iSup_ideal J U)) ?_
  refine le_trans (@logDerivIdeal_iSup_le k _ _ _ (sectionsAlgebra k p U.1) ι (P.ideal U)
    (fun i => (J i).ideal U)) ?_
  exact iSup_le fun i =>
    Scheme.IdealSheafData.le_def.mp (le_iSup (fun i' => logDerivIdealSheaf k p P (J i')) i) U

theorem logDerivIdealSheafIterate_iSup_le (k : Type u) [CommRing k] [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (P : Y.IdealSheafData) (r : ℕ)
    {ι : Sort v} (J : ι → Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheafIterate k p P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      have h1 : logDerivIdealSheafIterate k p P (r + 1) (⨆ i, J i)
          ≤ ⨆ i, logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r (J i)) := by
        rw [logDerivIdealSheafIterate_succ]
        exact le_trans (logDerivIdealSheaf_mono k p P ih)
          (logDerivIdealSheaf_iSup_le k p P
            (fun i => logDerivIdealSheafIterate k p P r (J i)))
      refine h1.trans (iSup_le fun i => le_iSup_of_le i ?_)
      exact le_of_eq (logDerivIdealSheafIterate_succ k p P r (J i)).symm

theorem logDerivIdealSheafIterate_biSup_le (k : Type u) [CommRing k] [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (P : Y.IdealSheafData) (r n : ℕ)
    (J : ℕ → Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r (⨆ l, ⨆ _ : l ≤ n, J l) ≤
      ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p P r (J l) := by
  refine le_trans (logDerivIdealSheafIterate_iSup_le k p P r
    (fun l => ⨆ _ : l ≤ n, J l)) ?_
  refine iSup_le fun l => ?_
  refine le_trans (logDerivIdealSheafIterate_iSup_le k p P r (fun _ : l ≤ n => J l)) ?_
  exact iSup_le fun h => le_iSup_of_le l (le_iSup_of_le h le_rfl)

theorem derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
    (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (m : ℕ) (K : ℕ → X.IdealSheafData) (hK : ∀ l ≤ m, K l ≤ Z ^ (m - l))
    (hest : ∀ n < m,
      derivIdealSheafIterate k p n (K 0) ≤
        ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p H (n - l) (K l))
    (K' : ℕ → X₁.IdealSheafData)
    (hK' : ∀ l ≤ m, Blowup.exceptionalIdeal π Z ^ (m - l) * K' l = (K l).comap π)
    (n : ℕ) (hn : n < m) :
    haveI : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    derivIdealSheafIterate k (π ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (K' l) := by
  have hsm : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  show derivIdealSheafIterate k (π ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (K' l)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := hπ.1
  have hK0 : K 0 ≤ Z ^ m := by simpa using hK 0 (Nat.zero_le m)
  have hA : ∀ l : ℕ, derivIdealSheafIterate k p l (K 0) ≤ Z ^ (m - l) := fun l =>
    derivIdealSheafIterate_le_pow_of_hasStrictNormalCrossingsWith k p Z (K 0) (H :: E) hsnc m hK0 l
  obtain ⟨L, hLspec⟩ : ∃ L : ℕ → X₁.IdealSheafData, ∀ l : ℕ,
      Blowup.exceptionalIdeal π Z ^ (m - l) * L l = (derivIdealSheafIterate k p l (K 0)).comap π :=
    ⟨fun l => controlledTransform π Z (derivIdealSheafIterate k p l (K 0)) (m - l) hπ (hA l),
      fun l => exceptionalIdeal_pow_mul_controlledTransform π Z (derivIdealSheafIterate k p l (K 0)) (m - l) hπ (hA l)⟩
  have hL0 : L 0 = K' 0 := by
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul (hcart.pow (m - 0)) ?_
    rw [hLspec 0, hK' 0 (Nat.zero_le m), derivIdealSheafIterate_zero]
  have hstep : ∀ l, l ≤ n → L l ≤
      ⨆ j, ⨆ _ : j ≤ l,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j) := by
    intro l hl
    have hlm : l < m := lt_of_le_of_lt hl hn
    have key : ∀ j, j ≤ l → (logDerivIdealSheafIterate k p H (l - j) (K j)).comap π ≤
        Blowup.exceptionalIdeal π Z ^ (m - l) *
          logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j) := by
      intro j hj
      have hjm : j ≤ m := by omega
      have ha : l - j ≤ m - j := by omega
      have h3 := comap_logDerivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z H E hsnc hHZ hπ
        (K j) (m - j) (hK j hjm) (l - j) ha
      have h4 : K' j = controlledTransform π Z (K j) (m - j) hπ (hK j hjm) :=
        eq_controlledTransform_of_mul_eq_comap π Z (K j) (m - j) hπ (hK j hjm) (K' j) (hK' j hjm)
      have harith : m - j - (l - j) = m - l := by omega
      rw [h4, ← harith]
      exact h3
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul (hcart.pow (m - l)) ?_
    rw [hLspec l]
    refine le_trans (Scheme.IdealSheafData.comap_mono π (hest l hlm)) ?_
    refine le_trans (le_of_eq (comap_iSup_le_nat π l
      (fun j => logDerivIdealSheafIterate k p H (l - j) (K j)))) ?_
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_trans (key j hj) (idealSheafData_mul_le_mul_left _
      (le_iSup_of_le j (le_iSup_of_le hj le_rfl)))
  have hmain := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_strictTransform
    k p π Z H E hsnc hHZ hπ (K 0) m L (fun l _ => hLspec l) n hn.le
  rw [hL0] at hmain
  refine le_trans hmain (iSup_le fun l => iSup_le fun hl => ?_)
  refine le_trans (logDerivIdealSheafIterate_mono k (π ≫ p) (Blowup.strictTransform π Z H) (n - l)
    (hstep l hl)) ?_
  refine le_trans (logDerivIdealSheafIterate_biSup_le k (π ≫ p) (Blowup.strictTransform π Z H)
    (n - l) l
    (fun j => logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j))) ?_
  refine iSup_le fun j => iSup_le fun hj => ?_
  rw [← logDerivIdealSheafIterate_add]
  have harith3 : n - l + (l - j) = n - j := by omega
  rw [harith3]
  exact le_iSup_of_le j (le_iSup_of_le (le_trans hj hl) le_rfl)

end FunctorialResolution.EmbeddedResolution
end

section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem structureMorphism_ambientBlowupSeq_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t := by
  show (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) ≫ T.structMap =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
  rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]

theorem ker_embeddingIntoAmbient_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t < s.length) :
    Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
  ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t ht

namespace GoingUpInvariant

private theorem getElem_map_append_of_lt_length.{v, w} {α : Type v} {β : Type w} (f : α → β)
    (M : List β) (L : List α) (i : ℕ) (hi : i < L.length)
    (h : i < (L.map f ++ M).length) :
    (L.map f ++ M)[i]'h = f (L[i]'hi) := by
  rw [List.getElem_append_left (by simpa using hi), List.getElem_map]

theorem succ {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} {T : MarkedIdealWithBoundary.{u}}
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    {j : ℕ} {hj : j < T.boundary.length}
    {I₀ : T.scheme.IdealSheafData} {E₀ : List T.scheme.IdealSheafData}
    {s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups}
    {hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent} {t : ℕ}
    (hgoingUp : GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (ht : t < s.length) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr (t + 1) := by
  have hlen : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
    ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr
  have hblow : Blowup.IsBlowupAlongIdealSheaf ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) :=
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isBlowup t (by rw [hlen]; exact ht)
  have hNt1 : AlgebraicGeometry.IsNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) :=
    isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (t + 1) (by omega)
  have hnoetherian : TopologicalSpace.NoetherianSpace
      ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hLNt1 : AlgebraicGeometry.IsLocallyNoetherian
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (t + 1)) := inferInstance
  have hNs1 : AlgebraicGeometry.IsNoetherian
      ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj (t + 1)) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s (t + 1) (by omega)
  have hLNs1 : AlgebraicGeometry.IsLocallyNoetherian
      ((MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.obj (t + 1)) := inferInstance
  have hsm : AlgebraicGeometry.Smooth (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    hgoingUp.smooth_structMap
  have hsncZ : HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) :=
    hgoingUp.hasStrictNormalCrossingsWith_center_boundary hlift ht
  have hsncCons : HasStrictNormalCrossingsWith (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ::
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) :=
    hgoingUp.hasStrictNormalCrossingsWith_center_ker_cons hlift ht
  have hkerle : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t :=
    ker_embeddingIntoAmbient_le_center hres hno T j hj I₀ E₀ s hpr t
  have hkersucc : Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) =
      Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
        (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) :=
    ker_embeddingIntoAmbient_succ hres hno T j hj I₀ E₀ s hpr t ht
  have hps : ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1) =
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t :=
    structureMorphism_ambientBlowupSeq_succ hres hno T j hj I₀ E₀ s hpr t
  have hsmc : AlgebraicGeometry.Smooth
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
        ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) :=
    smooth_comp_of_isBlowupAlongIdealSheaf hsncZ hblow
  have hsmsucc : AlgebraicGeometry.Smooth
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := by
    rw [hps]; exact hsmc
  have hsncSucc : InStrictNormalCrossingPosition (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)) := by
    rw [hps, BlowupSequenceData.boundary_succ]
    exact inStrictNormalCrossingPosition_strictTransform_append
      (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) hblow hgoingUp.snc_bdry hsncZ
  have hidxt : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length := hgoingUp.idx_lt
  have hidx : j < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length := by
    have h1 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).length = E₀.length + t :=
      BlowupSequenceData.boundary_length _ _ _
    have h2 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).length
        = E₀.length + (t + 1) := BlowupSequenceData.boundary_length _ _ _
    omega
  have hmaplen : j < (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).map
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))).length := by
    rw [List.length_map]; exact hidxt
  have hj2 : j < ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).map
        (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))) ++
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]).length := by
    rw [List.length_append]
    omega
  have hget : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1))[j]'hidx =
      Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)) := by
    rw [hkersucc, ← hgoingUp.bdry_getElem]
    refine (List.getElem_of_eq
      (BlowupSequenceData.boundary_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) E₀ t) hidx).trans ?_
    exact getElem_map_append_of_lt_length
      (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
      [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)]
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j hidxt hj2
  have hcen : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
    rw [ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t]
    exact Blowup.comap_map_of_isClosedImmersion
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)
  have hA : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).eraseIdx j =
      List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t))
        (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) ++
        [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)] := by
    rw [BlowupSequenceData.boundary_succ, List.eraseIdx_append_of_lt_length hmaplen, List.eraseIdx_map]
  have hB := map_comap_strictTransform_append_exceptionalIdeal
    (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))
    (s.transitionMapSucc t)
    (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t) hkersucc
    (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j) hsncCons hkerle hblow
  have hbdrysucc : List.map
      (fun D => D.comap (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1)))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (t + 1)).eraseIdx j) =
      s.boundary (t + 1) := by
    rw [hA, hB, hgoingUp.comap_eraseIdx, hcen]
    exact (s.boundary_succ t ht).symm
  have hKle : ∀ l, l ≤ T.mult →
      ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ≤
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t ^ (T.mult - l) :=
    fun l hl => hgoingUp.ambientDerivIdeal_le_center_pow hbal hm hV hlift ht l hl
  have hK' : ∀ l, l ≤ T.mult →
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t) ^ (T.mult - l) *
          ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1) =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) := fun l hl =>
    BlowupSequenceData.pow_exceptionalIdeal_mul_controlledTransform_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
      (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t
      (hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl)
  refine ⟨?_, hidx, ?_, hbdrysucc, hsncSucc, hget, hsmsucc⟩
  · intro l hl i hi
    by_cases hit : i < t
    · exact hgoingUp.divDeriv l hl i hit
    · have hie : i = t := by omega
      rw [hie]
      exact hgoingUp.exists_pow_mul_eq_comap_ambientDerivIdeal hbal hm hV hlift ht l hl
  · intro hsmooth instFt n hn
    have hsmS : AlgebraicGeometry.Smooth
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := hsmooth
    have hftS : AlgebraicGeometry.LocallyOfFiniteType
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) := instFt
    have hest : ∀ m, m < T.mult →
        derivIdealSheafIterate T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) m
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 t) ≤
          ⨆ l ≤ m, logDerivIdealSheafIterate T.base
            (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
            (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)) (m - l)
            (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) := by
      intro m hm'
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact hgoingUp.deriv_le m hm'
    have key := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
      T.base (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
      (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t).eraseIdx j)
      hsncCons hkerle hblow T.mult
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t) hKle hest
      (fun l => ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) hK' n hn
    have h0 : derivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) n
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult (t + 1)) =
        derivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) n
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr 0 (t + 1)) := by
      rw [ambientDerivIdeal_order_zero_eq_controlledTransform]
      exact derivIdealSheafIterate_congr
        (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
          ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t) hps n _
    have h1 : (⨆ l ≤ n, logDerivIdealSheafIterate T.base
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t)
            (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t))) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1))) =
        ⨆ l ≤ n, logDerivIdealSheafIterate T.base
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1))
          (Scheme.Hom.ker (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1))) (n - l)
          (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l (t + 1)) := by
      rw [hkersucc]
      exact iSup_congr fun l => iSup_congr fun _ =>
        logDerivIdealSheafIterate_congr
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr t)
          (ambientBlowupSeqStructureMorphism hres hno T j hj I₀ E₀ s hpr (t + 1)) hps.symm _ _ _
    exact le_trans (le_of_eq h0) (le_trans key (le_of_eq h1))

end GoingUpInvariant

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
