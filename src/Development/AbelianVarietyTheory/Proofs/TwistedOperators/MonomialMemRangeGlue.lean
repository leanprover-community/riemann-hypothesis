module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.MonomialRangeMembership

open MvPolynomial

theorem monomial_mem_range_glue {D : Formalism.BasicNotions.D7} {a b : ℕ}
    (m : Formalism.IndefR.Datum.FVar D b a →₀ ℕ) :
    (monomial m (1 : ℂ) : Formalism.IndefR.Links.PolF D b a) ∈
      Set.range (GlobalTheory.Chain.RealIt.glue (D := D) (a := a) (b := b)) := by
  refine ⟨fun τ => ∏ s : Fin b × Fin a, X s ^ m (τ, s), ?_⟩
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  unfold GlobalTheory.Chain.RealIt.glue
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [map_prod, map_pow, rename_X]

theorem span_range_glue : ∀ {D : Formalism.BasicNotions.D7} {a b : Nat}, @Eq (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.span Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing) (@Set.range (Formalism.IndefR.Links.PolF D b a) (@Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.R D) (Formalism.BasicNotions.D7.what₂ D) → GlobalTheory.Chain.RealIt.LPol b a) (@GlobalTheory.Chain.RealIt.glue D a b))) (@Top.top (@Submodule Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing)) (@Submodule.instTop Complex (Formalism.IndefR.Links.PolF D b a) Complex.instSemiring (@AddMonoidAlgebra.instAddCommMonoid Complex (@Finsupp (Formalism.IndefR.Datum.FVar D b a) Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass)) (@CommSemiring.toSemiring Complex Complex.instCommSemiring)) (@MvPolynomial.instModuleSelf (Formalism.IndefR.Datum.FVar D b a) Complex Complex.commRing))) := by
  intro D a b
  rw [eq_top_iff, ← (basisMonomials (Formalism.IndefR.Datum.FVar D b a) ℂ).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  rw [coe_basisMonomials]
  exact monomial_mem_range_glue m

end GlobalTheory.MonomialRangeMembership
