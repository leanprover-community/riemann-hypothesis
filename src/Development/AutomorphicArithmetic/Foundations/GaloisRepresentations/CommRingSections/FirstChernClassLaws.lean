module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.IsCovPr
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.Monotonicity.Lemmas
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

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh

namespace UpperTheory.Gal.DifferentialFormSections

structure IsDiv {K : Type} [CommRing K] {W E : Sch K} (i : E ⟶ W) (L : Coc W) (s : ∀ j : L.ι, Sec W (L.U j)) : Prop where
  closed : IsClosedImmersion i.left
  ker : ∀ j, RingHom.ker (secMap i (le_refl (i.left ⁻¹ᵁ L.U j))).toRingHom = Ideal.span {s j}
  nzd : ∀ j, s j ∈ nonZeroDivisors (Sec W (L.U j))
  rel : ∀ j : Fin 2 → L.ι, secRes W (inter_le (X := W.left.toTopCat) L.U j 0) (s (j 0)) =
    (L.g j).val * secRes W (inter_le (X := W.left.toTopCat) L.U j 1) (s (j 1))

end UpperTheory.Gal.DifferentialFormSections
