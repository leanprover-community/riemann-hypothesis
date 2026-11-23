module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientLastCoordinateEtaleTowerNormalLoca
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

theorem _root_.GlobalTheory.T.exists_quotient_lastCoordinate_etaleTowerNormalLocal : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin (r + 1) → T) (hT : IsEtTower cK R cL T ι ψ τ),
  ∃ (L' : Type) (_ : Field L') (cL' : ℂ →+* L') (T' : Subring L') (π : T →+* T') (ι' : R →+* T') (ψ' : T' →+* R),
    Function.Surjective π ∧ RingHom.ker π = Ideal.span {τ (Fin.last r)} ∧ τ (Fin.last r) ≠ 0 ∧
    IsEtTower cK R cL' T' ι' ψ' (fun i => π (τ (Fin.castSucc i))) ∧ ψ'.comp π = ψ ∧ π.comp ι = ι' ∧
    ∀ a, (π ⟨cL a, hT.top.const_mem a⟩ : L') = cL' a := by
  first | exact @GlobalTheory.FieldPair.IsEtTower.exists_quotient_last | exact GlobalTheory.FieldPair.IsEtTower.exists_quotient_last | (intros; apply GlobalTheory.FieldPair.IsEtTower.exists_quotient_last <;> assumption)
