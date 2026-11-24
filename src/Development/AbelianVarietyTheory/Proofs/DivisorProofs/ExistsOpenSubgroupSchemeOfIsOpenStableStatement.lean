module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupSchemeOfIsOpenStable
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_openSubgroupScheme_of_isOpen_stable : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (Z : Set G.left), IsOpen Z → (∀ s : S, (η[G]).left s ∈ Z) → (∀ w : (G ⊗ G).left, (fst G G).left w ∈ Z → (snd G G).left w ∈ Z → (μ[G]).left w ∈ Z) → (∀ y ∈ Z, (ι[G]).left y ∈ Z) → ∃ (G₀ : Over S) (_ : GrpObj G₀) (j : G₀ ⟶ G), IsMonHom j ∧ IsOpenImmersion j.left ∧ Set.range j.left = Z := by
  first | exact @GlobalTheory.OpenSubgroup.exists_open_subgroup | exact GlobalTheory.OpenSubgroup.exists_open_subgroup | (intros; apply GlobalTheory.OpenSubgroup.exists_open_subgroup <;> assumption)
