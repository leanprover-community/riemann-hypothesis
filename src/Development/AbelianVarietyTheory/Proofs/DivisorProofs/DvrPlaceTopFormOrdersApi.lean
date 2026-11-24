module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.FieldPair


open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
theorem _root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis {k K : Type} [Field k] [CharZero k]
    [Field K] (c : k →+* K) {n : ℕ} {x : Fin n → K} (hx : _root_.GlobalTheory.FieldPair.TrBasis c x) :
    _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) := by
  letI : Algebra k K := c.toAlgebra
  have hb : IsTranscendenceBasis k x := hx
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K :=
    hb.isAlgebraic_field
  haveI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨b, hbx⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hb.1
  exact _root_.GlobalTheory.TopForm.isFreeGen_dForm x b (fun i => by rw [hbx i])


open CategoryTheory AlgebraicGeometry TopologicalSpace in
open scoped TensorProduct in
theorem _root_.GlobalTheory.FieldPair.formOrd_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K]
    (c : k →+* K) (n : ℕ) (x : Fin n → K), _root_.GlobalTheory.FieldPair.TrBasis c x →
  _root_.GlobalTheory.TopForm.IsFreeGen K (_root_.GlobalTheory.TopForm.dForm c x) ∧
  ∀ E : _root_.GlobalTheory.FieldPair.Place c,
    (∃ ω : _root_.GlobalTheory.TopForm.Forms E.const n, _root_.GlobalTheory.TopForm.IsFreeGen E.ring ω) ∧
    (∀ η : _root_.GlobalTheory.TopForm.Forms c n, η ≠ 0 → E.IsFormOrd η ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η)) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (f : K), η ≠ 0 → f ≠ 0 →
      (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (f • η) = E.ord f + (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η) ∧
    (∀ (η : _root_.GlobalTheory.TopForm.Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a →
      (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η = a) := by
  intro k K _ _ _ c n x hx
  refine ⟨_root_.GlobalTheory.FieldPair.isFreeGen_dForm_of_trBasis c hx, fun E => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact E.exists_isFreeGen hx
  · intro η hη
    exact E.isFormOrd_formOrd hx hη
  · intro η f hη hf
    exact E.formOrd_smul hx hη hf
  · intro η a _ h
    exact h.formOrd_eq

end GlobalTheory.FieldPair
