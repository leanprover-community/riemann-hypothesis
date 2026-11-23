module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
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

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem eval₂_residue_ne_zero_and_inv_mem_of_isUnit :
    ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (hQ : IsLocModel cL Q)
  (S : Place cL) (ψ : S.ring →+* K) (F : Place cK), S.Contains Q → (∀ a, ψ (S.const a) = cK a) →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  ∀ (m : ℕ) (z : Fin m → Q) (zs : Fin m → S.ring), (∀ i, (zs i : L) = z i) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → IsUnit (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P)) →
  ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P ≠ 0 ∧
    (MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P)⁻¹ ∈ F.ring := by
  intro L K _ _ cL cK Q hQ S ψ F hSQ hc hF m z zs hz hu P hP
  let j : Q →+* S.ring := Q.subtype.codRestrict S.ring fun q => hSQ q q.2
  have h1 : (ψ.comp j).comp (cL.codRestrict Q hQ.const_mem) = cK := RingHom.ext fun a => hc a
  have h2 : (fun i => (ψ.comp j) (z i)) = fun i => ψ (zs i) :=
    funext fun i => congrArg ψ (Subtype.ext (hz i).symm)
  have h3 : (ψ.comp j) (MvPolynomial.eval₂ (cL.codRestrict Q hQ.const_mem) z P) =
      MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P := by
    rw [MvPolynomial.hom_eval₂, h1, h2]
  obtain ⟨q, hq⟩ := (hu P hP).exists_right_inv
  have h4 : MvPolynomial.eval₂ cK (fun i => ψ (zs i)) P * (ψ.comp j) q = 1 := by
    rw [← h3, ← map_mul, hq, map_one]
  refine ⟨left_ne_zero_of_mul_eq_one h4, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right h4]
  exact (hF _).2 ⟨j q, q.2, rfl⟩

end GlobalTheory.FieldPair
