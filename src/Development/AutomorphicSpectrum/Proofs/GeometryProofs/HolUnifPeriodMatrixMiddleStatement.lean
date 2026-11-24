module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsAbLift
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolUnifPeriodMatrixMiddle
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem _root_.GlobalTheory.T.hol_unif_period_matrix_middle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (g n : ℕ) (M : LieModel t.G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : Flat.FamExp t.G M B ψ) (b : Fin n → ℂ) (P : AbPart t (spMap (ψ b))) (A : Over (Sp ℂ)) (_ : GrpObj A) (φ : A.left ⟶ P.tB.G.left) (g' : ℕ) (u : HolUnif A (P.tB.PP.L.pull φ) g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ) (ℓ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), b ∈ B → IsGrpPullback A P.tB.G (𝟙 _) φ → u.IsAH Hm χ → IsPrincipal P.tB → GlobalTheory.CompanionTheory.Ar.QuotLoc.IsAbLift e b P φ u ℓ → ∀ (N : ℕ) (ζ : ℂˣ) (y y' : Fin g → ℂ), 0 < N → y ∈ e.per b → y' ∈ e.per b → GlobalTheory.UU.CubWeil t.cub N (e.ex b ((N : ℂ)⁻¹ • y)) (e.ex b ((N : ℂ)⁻¹ • y')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((ℓ y ⬝ᵥ Hm *ᵥ star (ℓ y')).im : ℝ) : ℂ) / N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.Pair.cubWeil_eq_exp_riemann <;> assumption)
