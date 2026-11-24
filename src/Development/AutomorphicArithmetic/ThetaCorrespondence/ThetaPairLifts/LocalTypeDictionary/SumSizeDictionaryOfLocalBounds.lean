module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDictionaryEventuallyLarge
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumSize
theorem sum_size_dictionary_of_local_bounds (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) : DictK := by
  obtain ⟨CF0, h⟩ := _root_.GlobalTheory.T.twisted_dictionary_correspondence hP hI
  refine ⟨CF0, fun CF hCF => ⟨0, fun ε C _ => ?_⟩⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ =>
    hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt⟩
end GlobalTheory.SumSize
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.sum_size_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK := by
  first | exact @_root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | exact _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | (intros; apply _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds <;> assumption)
end
