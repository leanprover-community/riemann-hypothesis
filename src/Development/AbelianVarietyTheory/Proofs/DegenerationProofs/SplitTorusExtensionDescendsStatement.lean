module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.splitTorus_extension_descends_alt : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [GrpObj B₀] (X : Type) [AddCommGroup X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap β) φG → IsGrpPullback B B₀ (spMap β) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) (q₀ : G₀ ⟶ B₀) (i₀ : splitTorus (Sp k) X ⟶ G₀), φG ≫ q₀.left = q.left ≫ φ → GlobalTheory.SplitTorus.bcMap (spMap β) X ≫ i₀.left = i.left ≫ φG → IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → IsMonHom q₀ ∧ Flat q₀.left ∧ Surjective q₀.left ∧ QuasiCompact q₀.left ∧ IsMonHom i₀ ∧ IsPullback i₀ (toUnit _) q₀ (η[B₀] : 𝟙_ _ ⟶ B₀) := by
  first | exact @GlobalTheory.splitTorus_extension_descends | exact GlobalTheory.splitTorus_extension_descends | (intros; apply GlobalTheory.splitTorus_extension_descends <;> assumption)
