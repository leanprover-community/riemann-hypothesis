module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private theorem UpperTheory.preimage_whiskerRight_comp_over {S : Scheme.{0}} {A B C G : Over S} (f : A ⟶ B) (g : B ⟶ C)
    (W : (C ⊗ G).left.Opens) :
    ((f ≫ g) ▷ G).left ⁻¹ᵁ W = (f ▷ G).left ⁻¹ᵁ ((g ▷ G).left ⁻¹ᵁ W) := by
  simp

theorem UpperTheory.clopRep_unique :
    ∀ {S : Scheme.{0}} (G Y Y' : Over S) (U : (Y ⊗ G).left.Opens) (U' : (Y' ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → UpperTheory.RepresentationRank.Rep G Y' U' → Nonempty (Y ≅ Y') := by
  intro S G Y Y' U U' hU hU'
  obtain ⟨φ, hφ, -⟩ := hU'.2 Y U hU.1
  obtain ⟨ψ, hψ, -⟩ := hU.2 Y' U' hU'.1
  have hid : ∀ {Z : Over S} (W : (Z ⊗ G).left.Opens), ((𝟙 Z) ▷ G).left ⁻¹ᵁ W = W := by
    intro Z W
    simp
  have e1 : φ ≫ ψ = 𝟙 Y := by
    obtain ⟨y, -, huniq⟩ := hU.2 Y U hU.1
    have a := huniq (φ ≫ ψ) (by
      show ((φ ≫ ψ) ▷ G).left ⁻¹ᵁ U = U
      rw [UpperTheory.preimage_whiskerRight_comp_over, hψ, hφ])
    have b := huniq (𝟙 Y) (hid U)
    rw [a, b]
  have e2 : ψ ≫ φ = 𝟙 Y' := by
    obtain ⟨y, -, huniq⟩ := hU'.2 Y' U' hU'.1
    have a := huniq (ψ ≫ φ) (by
      show ((ψ ≫ φ) ▷ G).left ⁻¹ᵁ U' = U'
      rw [UpperTheory.preimage_whiskerRight_comp_over, hφ, hψ])
    have b := huniq (𝟙 Y') (hid U')
    rw [a, b]
  exact ⟨⟨φ, ψ, e1, e2⟩⟩
