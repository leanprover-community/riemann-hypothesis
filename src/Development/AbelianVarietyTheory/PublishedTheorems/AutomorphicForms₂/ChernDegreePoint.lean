import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.Published.ArDegreeModel


variable {F : Type} [Field F] (Y : Var F) (σ : F →+* ℂ)


def fs : Weight Y.str σ Y.O1 :=
  Weight.fsBasis Y.str σ Y.isLineBundle_twistingSheafOne Y.coordSec Y.basePointFree_coordSys 1 (by simp)



theorem unique_pt (h : Y.dim = 0) : Nonempty (CxPts Y.str σ) ∧ Subsingleton (CxPts Y.str σ) := by
  have : Etale Y.str := (Etale.iff_smoothOfRelativeDimension_zero _).2 (h ▸ Y.smooth_str)
  let q := Limits.pullback.snd Y.str (spMap σ)
  have : IsIntegral (Limits.pullback Y.str (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := Y.str) _ _ _ (IsPullback.of_hasPullback _ _)
  have hs (s : Sp ℂ ⟶ Limits.pullback Y.str (spMap σ)) (hs : s ≫ q = 𝟙 _) : IsIso q := by
    have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
    have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
    have : Etale (s ≫ q) := by rw [hs]; infer_instance
    have : Etale s := Etale.of_comp s q
    have : Mono s := (SplitMono.mk q hs).mono
    have : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
    have : IsIso s := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (Opens.ext
      (IsClopen.eq_univ ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩ (Set.range_nonempty _)))
    have : IsIso (s ≫ q) := by rw [hs]; infer_instance
    exact IsIso.of_isIso_comp_left s _
  have : JacobsonSpace (Limits.pullback Y.str (spMap σ) :) := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (X := (Limits.pullback Y.str (spMap σ) :)) Set.univ_nonempty
    isOpen_univ.isLocallyClosed
  have := hs _ (pointOfClosedPoint_comp q c hc)
  refine ⟨⟨⟨inv q ≫ Limits.pullback.fst _ _, by rw [Category.assoc, Limits.pullback.condition]; simp [q]⟩⟩,
    ⟨fun a b => Subtype.ext ?_⟩⟩
  have e : Limits.pullback.lift a.1 (𝟙 _) (by simpa using a.2) = Limits.pullback.lift b.1 (𝟙 _) (by simpa using b.2) :=
    (cancel_mono q).1 ((Limits.pullback.lift_snd _ _ _).trans (Limits.pullback.lift_snd _ _ _).symm)
  exact (Limits.pullback.lift_fst _ _ _).symm.trans
    ((congrArg (· ≫ Limits.pullback.fst _ _) e).trans (Limits.pullback.lift_fst _ _ _))

theorem chernDegree_point (Δ : (proj F 0).Dv) (L : LB (proj F 0).X) (φ : Weight (proj F 0).str σ L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn 0 Set.univ (fun _ => 1) ∧
      φ.chernInt 0 Set.univ (fun _ => 1) = ((proj F 0).inter (fun _ => Δ) : ℝ) := by
  obtain ⟨⟨y⟩, _⟩ := unique_pt (proj F 0) σ rfl
  have : SmoothOfRelativeDimension 0 (proj F 0).str := (proj F 0).smooth_str
  have := CxPts.secondCountableTopology_of_isProjOver σ (proj F 0).isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth (proj F 0).str 0 σ
  obtain ⟨a, ha⟩ := R.cover y
  have hm (ε : ℤˣ) : φ.chernPart 0 ε Set.univ = ENNReal.ofReal (ε : ℤ) := by
    rw [Weight.chernPart_apply h ε (R.chart a) MeasurableSet.univ fun z _ => Subsingleton.elim y z ▸ ha]
    simp only [AlgChart.chernDens_zero, mul_one]
    rw [show (R.chart a).e '' Set.univ = Set.univ from
      Set.eq_univ_of_forall fun v => ⟨y, trivial, Subsingleton.elim _ _⟩]
    have hv : (MeasureTheory.volume : MeasureTheory.Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
      have := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
      rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
        (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩] at this
    simp [hv]
  have hf (ε : ℤˣ) : MeasureTheory.IsFiniteMeasure (φ.chernPart 0 ε) := ⟨by rw [hm]; exact ENNReal.ofReal_lt_top⟩
  have hi : (proj F 0).inter (fun _ => Δ) = 1 :=
    (congrArg _ (funext fun i : Fin 0 => i.elim0)).trans (inter_projHyp F 0)
  refine ⟨⟨MeasureTheory.integrableOn_univ.2 (MeasureTheory.integrable_const _),
    MeasureTheory.integrableOn_univ.2 (MeasureTheory.integrable_const _)⟩, ?_⟩
  rw [hi, Weight.chernInt]
  simp [MeasureTheory.Measure.real, hm, ENNReal.toReal_ofReal']



end GlobalTheory.Published.ArDegreeModel
