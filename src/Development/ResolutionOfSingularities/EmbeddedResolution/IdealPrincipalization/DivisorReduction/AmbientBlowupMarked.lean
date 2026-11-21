import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantSucc

section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_affineOpen_ideal_eq_top_of_not_mem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (y : ↥X) (hy : y ∉ I.support) :
    ∃ V : X.affineOpens, y ∈ V.1 ∧ I.ideal V = ⊤ := by
  obtain ⟨U, hyU, -⟩ :=
    Scheme.exists_affineOpens_mem_le (X := X) (x := y) (U := ⊤) trivial
  have hny := hy
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hyU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hny
  push Not at hny
  obtain ⟨s, hs, hys⟩ := hny
  refine ⟨X.affineBasicOpen s, hys, ?_⟩
  let _ : Algebra Γ(X, U.1) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
  have hloc : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  have hunit : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s) :=
    IsLocalization.map_units (M := Submonoid.powers s) Γ(X, X.basicOpen s)
      ⟨s, Submonoid.mem_powers s⟩
  have hmem : algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s ∈ I.ideal (X.affineBasicOpen s) := by
    rw [← I.map_ideal_basicOpen U s]
    exact Ideal.mem_map_of_mem _ hs
  exact Ideal.eq_top_of_isUnit_mem _ hmem hunit

theorem not_mem_support_of_mem_support_of_pow_mul {X : Scheme.{u}}
    (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) {x : ↥X} (hx : x ∈ Z.support) :
    x ∉ I₀.support := by
  intro hx0
  have hZ : stalkIdeal Z x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx
  have hI0 : stalkIdeal I₀ x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal I₀ x).mp hx0
  have hIle : stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (m + 1) := by
    rw [hfac, stalkIdeal_mul, stalkIdeal_pow, pow_succ]
    exact Ideal.mul_mono (Ideal.pow_right_mono hZ m) hI0
  have h1 := (le_orderAt_iff I x (m + 1)).mpr hIle
  have h3 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans h1 (hord x)
  have h4 : m + 1 ≤ m := by exact_mod_cast h3
  omega

theorem isDerivBalanced_of_pow_mul (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) (hbal : IsDerivBalanced k p I m) :
    IsDerivBalanced k p I₀ m := by
  refine (isDerivBalanced_iff k p I₀ m).mpr ?_
  intro i hi
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hyZ : y ∈ Z.support
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support I₀ y
      (not_mem_support_of_mem_support_of_pow_mul Z I I₀ m hfac hord hyZ)
    refine ⟨V, hyV, ?_⟩
    have htop : (I₀ ^ (m - i)).ideal V = ⊤ := by
      rw [Scheme.IdealSheafData.ideal_pow]
      show I₀.ideal V ^ (m - i) = ⊤
      rw [hV, ← Ideal.one_eq_top, one_pow]
    rw [htop]
    exact le_top
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support Z y hyZ
    refine ⟨V, hyV, ?_⟩
    have hIV : I.ideal V = I₀.ideal V := by
      rw [hfac, Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow]
      show Z.ideal V ^ m * I₀.ideal V = I₀.ideal V
      rw [hV, ← Ideal.one_eq_top, one_pow, one_mul]
    have hder : (derivIdealSheafIterate k p i I).ideal V
        = (derivIdealSheafIterate k p i I₀).ideal V := by
      rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal, hIV]
    have hb : ((derivIdealSheafIterate k p i I).ideal V) ^ m ≤ (I.ideal V) ^ (m - i) := by
      have hb0 := Scheme.IdealSheafData.le_def.mp ((isDerivBalanced_iff k p I m).mp hbal i hi) V
      rwa [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow] at hb0
    rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
    show ((derivIdealSheafIterate k p i I₀).ideal V) ^ m ≤ (I₀.ideal V) ^ (m - i)
    rw [← hIV, ← hder]
    exact hb

end FunctorialResolution.EmbeddedResolution
end

section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

theorem IsMarked.of_comap_isoObjZero_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {d : BlowupSequenceData X} {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
    {I I' : X.IdealSheafData} {E E' : List X.IdealSheafData}
    (hI : I.comap d.isoZero.hom = I'.comap d.isoZero.hom)
    (hE : List.map (fun D => D.comap d.isoZero.hom) E =
      List.map (fun D => D.comap d.isoZero.hom) E')
    (h : d.IsMarked p I m E) : d.IsMarked p I' m E' := by
  have hIc : ∀ t : ℕ, d.controlledTransform I m t = d.controlledTransform I' m t := fun t =>
    d.controlledTransform_congr I I' (by rw [d.projectionToBase_zero]; exact hI) m t
  have hEc : ∀ t : ℕ, d.boundaryFrom E t = d.boundaryFrom E' t := fun t =>
    d.boundary_congr E E' (by simp only [d.projectionToBase_zero]; exact hE) t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [← hIc i]
    exact h.divisible i hi
  · intro i hi
    rw [← hIc i]
    exact h.center_order i hi
  · exact h.center_smooth
  · intro i hi
    rw [← hEc i]
    exact h.center_snc i hi

end BlowupSequenceData

namespace DivisorReduction

theorem goingUpInvariant_of_le (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j)
    (t : ℕ) (ht : t ≤ s.length) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t := by
  induction t with
  | zero => exact goingUpInvariant_zero hres hno T j hj I₀ E₀ s hpr hE₀ hjE hget htrunc
  | succ n ih =>
      exact GoingUpInvariant.succ (ih (Nat.le_of_succ_le ht)) hbal hm hV hlift (Nat.lt_of_succ_le ht)

theorem isMarked_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).IsMarked T.structMap I₀ T.mult E₀ := by
  have hlen : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
    ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      (i + 1) hi).exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i (Nat.lt_succ_self i)
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).support_center_subset_orderAtLeastLocus hbal hm hV hi
  · intro i hi
    rw [hlen] at hi
    exact smooth_ambientBlowupSeq_center_comp hres hno T j hj I₀ E₀ s hpr i hi
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).hasStrictNormalCrossingsWith_center_boundary hlift hi

theorem comap_controlledTransform_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j)
    (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
    t ht).comap_controlledTransform ht

private theorem lowerIdealWithoutBlowup_eq_ideal (T : MarkedIdealWithBoundary.{u}) :
    lowerIdealWithoutBlowup T = T.ideal :=
  Scheme.IdealSheafData.comap_id T.ideal

theorem isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) [AlgebraicGeometry.IsNoetherian T.scheme]
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : containedComponentsIdeal T j hj = ⊤)
    (hVlow : (restrictToDivisor T j hj).IsAdmissible)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := isMarked_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc
  exact BlowupSequenceData.IsMarked.of_comap_isoObjZero_eq (by simp only [hideal]) (by simp only [hbdry]) main

theorem comap_controlledTransform_of_containedComponentsIdeal_eq_top
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) [AlgebraicGeometry.IsNoetherian T.scheme]
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : containedComponentsIdeal T j hj = ⊤)
    (hVlow : (restrictToDivisor T j hj).IsAdmissible)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
        T.ideal T.mult t).comap
      (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) = s.ideal t := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := comap_controlledTransform_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc t ht
  have hc := BlowupSequenceData.controlledTransform_congr
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr)
    (lowerIdealWithoutBlowup T) T.ideal (by simp only [hideal]) T.mult t
  rw [← hc]
  exact main

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
