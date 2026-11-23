module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupSchemeMorphismDescends
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
theorem _root_.GlobalTheory.T.group_structure_descends_along_pullback : ∀ (k K : Type) [Field k] [Field K] (β : k →+* K) (B : Over (Sp K)) [GrpObj B] (B₀ : Over (Sp k)) (φ : B.left ⟶ B₀.left), IsAbelianScheme B → IsPullback φ B.hom B₀.hom (spMap β) → ∀ (m : B₀ ⊗ B₀ ⟶ B₀) (i : B₀ ⟶ B₀) (e : 𝟙_ (Over (Sp k)) ⟶ B₀) (φ₂ : (B ⊗ B).left ⟶ (B₀ ⊗ B₀).left), φ₂ ≫ (fst B₀ B₀).left = (fst B B).left ≫ φ → φ₂ ≫ (snd B₀ B₀).left = (snd B B).left ≫ φ → φ₂ ≫ m.left = (μ[B]).left ≫ φ → φ ≫ i.left = (ι[B]).left ≫ φ → spMap β ≫ e.left = (η[B]).left ≫ φ → ∃ _ : GrpObj B₀, IsAbelianScheme B₀ ∧ IsGrpPullback B B₀ (spMap β) φ := by
  first | exact @GlobalTheory.isAbelianScheme_descends_subfield | exact GlobalTheory.isAbelianScheme_descends_subfield | (intros; apply GlobalTheory.isAbelianScheme_descends_subfield <;> assumption)
