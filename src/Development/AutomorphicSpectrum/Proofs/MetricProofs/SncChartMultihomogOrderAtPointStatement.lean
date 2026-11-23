module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPoint
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries

@[expose] public section

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem _root_.GlobalTheory.T.snc_chart_multihomog_order_at_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → IsMultiHomog f a → (∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D) → ∃ (u : (locRing (SncRes.ideal P p) (renPt (affCoord p z)))ˣ) (mm : Fin e → ℕ), (∀ i, i ∉ Jf → mm i = 0) ∧ algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (bind₁ (SncRes.lift p) f) = u * ∏ i ∈ Jf, algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r i) ^ mm i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial <;> assumption)
