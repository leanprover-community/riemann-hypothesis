module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalCoordinatesExtendProjectiveSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_rationalCoordinates_extend_projectiveSpace : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (N : ℕ) (U : Y.Opens)
    (φ : U.toScheme ⟶ PSpace F N), φ ≫ PSpace.str F N = U.ι ≫ p → (U : Set Y).Nonempty →
    ∃ (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)), w i₀ = 1 ∧
      (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        (∀ y' : Y', ∃ k, GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
          (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k))) →
        ∃ g : Y' ⟶ PSpace F N, g ≫ PSpace.str F N = s ≫ p ∧ (s ⁻¹ᵁ U).ι ≫ g = (s ∣_ U) ≫ φ := by
  first | exact @GlobalTheory.ProjSpace.exists_ratCoords_extend | exact GlobalTheory.ProjSpace.exists_ratCoords_extend | (intros; apply GlobalTheory.ProjSpace.exists_ratCoords_extend <;> assumption)
