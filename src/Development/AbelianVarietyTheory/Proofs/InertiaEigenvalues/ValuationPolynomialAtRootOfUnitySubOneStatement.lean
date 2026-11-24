module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationPolynomialAtRootOfUnitySubOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section


theorem _root_.GlobalTheory.T.valuation_polynomial_at_root_of_unity_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (l : ℕ), l.Prime → (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (h : Polynomial O) (w : ℕ), h.coeff w ≠ 0 → ∃ (BB : Finset ℕ) (c : ℕ → ℝ), BB.card ≤ w + (IsDiscreteValuationRing.addVal O (h.coeff w)).toNat ∧ ∀ k, 1 ≤ k → k ∉ BB → c k ≤ Formalism.MainNotions.BlochKatoReduction.Gen.nval O l (h.coeff w) + w / (Nat.totient (l ^ k) : ℝ) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → Polynomial.aeval (ζ - 1) h ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) h) = c k := by
  first | exact @GlobalTheory.PolyCycloValue.value_at_root_sub_one | exact GlobalTheory.PolyCycloValue.value_at_root_sub_one | (intros; apply GlobalTheory.PolyCycloValue.value_at_root_sub_one <;> assumption)
