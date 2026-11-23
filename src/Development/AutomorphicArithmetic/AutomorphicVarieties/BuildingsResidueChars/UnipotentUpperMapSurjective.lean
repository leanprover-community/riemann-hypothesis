module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

@[expose] public section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

theorem UpperTheory.unipotent_upper_map_surjective :
    ∀ {S R : Type} [CommRing S] [CommRing R] (f : S →+* R), Function.Surjective f → ∀ (n : ℕ) (x : GL (Fin n) R), x ∈ unipB R (Fin n) →
        ∃ y ∈ unipB S (Fin n), GeneralLinearGroup.map (n := Fin n) f y = x := by
  intro S R _ _ f hf n x hx
  obtain ⟨hlow, hdiag⟩ := (mem_unipB R).1 hx
  let A : Matrix (Fin n) (Fin n) S := fun i j =>
    if i < j then Function.surjInv hf ((x : Matrix (Fin n) (Fin n) R) i j) else if i = j then 1 else 0
  have hA : A.BlockTriangular id := by
    intro i j hij
    have h1 : ¬ i < j := not_lt.2 (le_of_lt hij)
    have h2 : i ≠ j := ne_of_gt hij
    simp [A, h1, h2]
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular hA]
    exact Finset.prod_eq_one fun i _ => by simp [A]
  have hunit : IsUnit A.det := by simp [hdet, isUnit_one]
  have hcoe : ((GeneralLinearGroup.mk'' A hunit : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) = A := rfl
  refine ⟨GeneralLinearGroup.mk'' A hunit, (mem_unipB S).2 ⟨fun i j hji => ?_, fun i => ?_⟩, ?_⟩
  · rw [hcoe]
    exact hA hji
  · rw [hcoe]
    simp [A]
  · apply Units.ext
    ext i j
    have hmap : ((GeneralLinearGroup.map (n := Fin n) f (GeneralLinearGroup.mk'' A hunit) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = f (A i j) := rfl
    rw [hmap]
    rcases lt_trichotomy i j with h | h | h
    · simp only [A, if_pos h]
      exact Function.surjInv_eq hf _
    · subst h
      simp [A, hdiag]
    · have h1 : ¬ i < j := not_lt.2 (le_of_lt h)
      have h2 : i ≠ j := ne_of_gt h
      simp [A, h1, h2, hlow i j h]
