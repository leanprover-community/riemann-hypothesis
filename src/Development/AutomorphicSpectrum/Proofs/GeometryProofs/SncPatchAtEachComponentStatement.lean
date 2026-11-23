module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchAtEachComponent
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

theorem _root_.GlobalTheory.T.snc_patch_at_each_component : ∀ (F : Type) [Field F] [NumberField F] (W : Scheme.{0}) (sW : W ⟶ Sp F) (e : ℕ) (T : Set W) (Ω : Type) [Field Ω] [CharZero Ω] [Algebra F Ω] (ξ' : Sp Ω ⟶ W), IsCptGen ξ' → ξ' ≫ sW = spMap (algebraMap F Ω) → SmoothOfRelativeDimension e sW → ResK.HasSncCoords sW e T → (∀ p q : Cpt ξ', regAt ξ' p = regAt ξ' q → p = q) → ∀ p' : Cpt ξ', ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A), IsSncPatch (Set.range (regAt ξ')) (regAt ξ' '' {p | p.1 ∈ T}) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ' p') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Patch.exists_patch | exact GlobalTheory.CompanionTheory.Ar.SncBase.Patch.exists_patch | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Patch.exists_patch <;> assumption)
