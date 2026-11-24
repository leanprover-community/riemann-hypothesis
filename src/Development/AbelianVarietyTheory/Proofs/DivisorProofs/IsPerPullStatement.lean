module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPerPull
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isPer_of_isPull1_of_isPer : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (g' : ℕ) (L' : LB A'.left) (u' : HolUnif A' L' g') (φ : A' ⟶ A) (M : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : φ.left ≫ str A = str A' ≫ spMap (RingHom.id ℂ)), (∀ w, u.ex (M w) = u'.ex w ≫ φ) → ∀ (hM : ∀ l : u'.Λ, M l ∈ u.Λ) x x' q, IsPull1 h x x' → IsPer u.ex u.Λ x q → IsPer u'.ex u'.Λ x' fun l => q ⟨M l, hM l⟩ := by
  first | exact @GlobalTheory.CechPer.Nat.isPer_pull | exact GlobalTheory.CechPer.Nat.isPer_pull | (intros; apply GlobalTheory.CechPer.Nat.isPer_pull <;> assumption)
