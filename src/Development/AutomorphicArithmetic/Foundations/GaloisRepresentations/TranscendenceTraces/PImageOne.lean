module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imageOne_of :
    ImageOne := by
  intro Z P S k b _ _ _
  have hk : IsFinite k := IsFinite.of_comp k b
  have ht : IsFinite k.toImage := by
    have : IsFinite (k.toImage ≫ k.imageι) := by rw [k.toImage_imageι]; exact hk
    exact IsFinite.of_comp k.toImage k.imageι
  have hs : Surjective k.toImage :=
     surjective_of_isDominant_of_isClosed_range k.toImage k.toImage.isClosedMap.isClosed_range
  have e : k.toImage ≫ (k.imageι ≫ b) = k ≫ b := k.toImage_imageι_assoc b
  have huc : UniversallyClosed (k.imageι ≫ b) := by
    have : UniversallyClosed (k.toImage ≫ (k.imageι ≫ b)) := by rw [e]; infer_instance
    exact UniversallyClosed.of_comp_surjective k.toImage _
  have hqf : LocallyQuasiFinite (k.imageι ≫ b) := by
    refine .of_finite_preimage_singleton _ fun s => ?_
    refine (((k ≫ b).finite_preimage_singleton s).image k.toImage).subset ?_
    intro y hy
    obtain ⟨x, rfl⟩ := k.toImage.surjective y
    refine ⟨x, ?_, rfl⟩
    have : (k ≫ b) x = (k.imageι ≫ b) (k.toImage x) := by
      rw [← e, Scheme.Hom.comp_apply]
    exact this.trans hy
  have : IsProper (k.imageι ≫ b) := ⟨⟩
  exact ⟨IsFinite.of_isProper_of_locallyQuasiFinite _, ht⟩
