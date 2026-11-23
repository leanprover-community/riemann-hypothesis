module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section
namespace GlobalTheory.SnMass.SkewVol

open NumberField.InfinitePlace

def cxPlaceEquiv (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    {w : InfinitePlace E // IsComplex w} ≃ InfinitePlace E :=
  Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w

def mixedCoords (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    mixedEmbedding.mixedSpace E ≃ₗ[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)) where
  toFun x := (fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).re,
    fun w => (x.2 ⟨w, IsTotallyComplex.isComplex w⟩).im)
  invFun y := (fun w => absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)),
    fun w => ⟨y.1 w.1, y.2 w.1⟩)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp
  left_inv x := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · exact absurd w.2 (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1))
    · apply Complex.ext <;> rfl
  right_inv y := rfl

private theorem measurePreserving_mixedSpace_snd (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    MeasurePreserving (Prod.snd : mixedEmbedding.mixedSpace E → ({w : InfinitePlace E // IsComplex w} → ℂ))
      volume volume := by
  have : IsEmpty {w : InfinitePlace E // IsReal w} :=
    ⟨fun w => not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1) w.2⟩
  have h : (volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)) = Measure.dirac 0 := by
    rw [MeasureTheory.volume_pi, Measure.pi_of_empty]
    congr 1
    exact Subsingleton.elim _ _
  refine ⟨measurable_snd, ?_⟩
  show Measure.map Prod.snd ((volume : Measure ({w : InfinitePlace E // IsReal w} → ℝ)).prod volume) = volume
  rw [h, Measure.map_snd_prod]
  simp

theorem measurePreserving_mixedCoords (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] :
    MeasurePreserving (mixedCoords E) volume volume := by
  have h2 := measurePreserving_piCongrLeft (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (cxPlaceEquiv E)
  have h3 := measurePreserving_pi (fun _ : InfinitePlace E => (volume : Measure ℂ))
    (fun _ => (volume : Measure (ℝ × ℝ))) (fun _ => Complex.volume_preserving_equiv_real_prod)
  have h4 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)
    (fun _ => (volume : Measure ℝ)) (fun _ => (volume : Measure ℝ))
  have key := h4.comp (h3.comp (h2.comp (measurePreserving_mixedSpace_snd E)))
  have e : (⇑(mixedCoords E)) = ⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (InfinitePlace E)) ∘
      (fun a i => Complex.measurableEquivRealProd (a i)) ∘
        ⇑(MeasurableEquiv.piCongrLeft (fun _ => ℂ) (cxPlaceEquiv E)) ∘ Prod.snd := by
    funext x
    ext w <;> rfl
  rw [e]
  exact key

theorem mixedCoords_mixedEmbedding (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (x : E) : mixedCoords E (mixedEmbedding E x) = (reV x, imV x) := by
  ext w <;> simp [mixedCoords, reV, imV, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem mixedSpace_reIm_coords : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E →
    ∃ e : mixedEmbedding.mixedSpace E ≃L[ℝ] ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ)),
      MeasurePreserving e volume volume ∧ ∀ x : E, e (mixedEmbedding E x) = (reV x, imV x) := by
  intro E _ _ hE
  have := hE
  exact ⟨(mixedCoords E).toContinuousLinearEquiv, by
    simpa using measurePreserving_mixedCoords E, fun x => by
    simpa using mixedCoords_mixedEmbedding E x⟩

end GlobalTheory.SnMass.SkewVol
