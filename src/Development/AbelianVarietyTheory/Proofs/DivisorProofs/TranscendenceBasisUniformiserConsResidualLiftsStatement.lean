module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLifts
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

theorem _root_.GlobalTheory.T.transcendenceBasis_uniformiser_cons_residual_lifts : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring), Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f → TrBasis cK (fun i => ψ (w i)) → TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧ (fun ω => @dite ℤ (∃ a, S.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧ S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  first | exact @GlobalTheory.FieldPair.trBasis_uniformiser_cons | exact GlobalTheory.FieldPair.trBasis_uniformiser_cons | (intros; apply GlobalTheory.FieldPair.trBasis_uniformiser_cons <;> assumption)
