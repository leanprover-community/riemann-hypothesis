module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreDenseAffineChartPrimes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

open AlgebraicGeometry CategoryTheory Limits

theorem _root_.GlobalTheory.T.mem_closure_annihilator_primes_inter_fibre : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens) (U : X.Opens) (V : T.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : U ≤ p ⁻¹ᵁ V),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) →
    ∀ q : PrimeSpectrum Γ(X, U), q ∈ closure ({P : PrimeSpectrum Γ(X, U) | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (p.appLE V U e).hom ⁻¹' {PrimeSpectrum.comap (p.appLE V U e).hom q}) := by
  first | exact @GlobalTheory.fibre_dense_affine_chart_primes | exact GlobalTheory.fibre_dense_affine_chart_primes | (intros; apply GlobalTheory.fibre_dense_affine_chart_primes <;> assumption)
