module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPureBCId
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaFixesComplexFibrePureEndomorphismTorsion
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.inertia_fixes_complex_fibre_pure_endomorphism_torsion : GlobalTheory.Published.FormalAlgebraisation → GlobalTheory.Published.GrothendieckMessing → ∀ (N : IntermediateField ℚ ℂ) [NumberField N] (P : Out.PolAV (Sp (𝓞 N))) (W : P.A ⟶ P.A) [IsMonHom W] (r s : 𝓞 N), IsPureBC P.A W r s → ∀ q : ℕ, q.Prime → ∀ 𝔮 : Ideal (𝓞 N), 𝔮.IsMaximal → (q : 𝓞 N) ∈ 𝔮 → r - s ∉ 𝔮 → ∀ τ : ℂ ≃+* ℂ, (∀ x : 𝓞 N, ∃ y : 𝓞 N, ((y : N) : ℂ) = τ ((x : N) : ℂ) ∧ y - x ∈ 𝔮) → ∀ (A : Over (Sp ℂ)) [GrpObj A] (ψ : A.left ⟶ P.A.left), IsGrpPullback A P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ → ∃ io : A.left ⟶ A.left, IsGrpPullback A A (spMap (τ : ℂ →+* ℂ)) io ∧ ∀ n : ℕ, ¬ q ∣ n → ∀ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ P.A, y ^ n = 1 → ∀ x : Sp ℂ ⟶ A.left, x ≫ A.hom = 𝟙 _ → x ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left → x ≫ io = spMap (τ : ℂ →+* ℂ) ≫ x := by
  first | exact @GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | exact GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia | (intros; apply GlobalTheory.InertiaTransfer.exists_isGrpPullback_of_inertia <;> assumption)
