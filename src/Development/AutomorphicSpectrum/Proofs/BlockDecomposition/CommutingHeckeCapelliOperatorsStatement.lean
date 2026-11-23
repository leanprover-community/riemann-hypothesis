module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHeckeCapelliOperators
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf

@[expose] public section

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm


theorem _root_.GlobalTheory.T.commuting_hecke_capelli_operators : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ), 0 < r → 0 < s →
  ∃ (S : Subalgebra ℂ (Module.End ℂ (Sm E (r + s)))) (a b : (E →+* ℂ) → ℕ → Module.End ℂ (Sm E (r + s))) (t : (E →+* ℂ) → ℂ),
    (∀ x ∈ S, ∀ y ∈ S, x * y = y * x) ∧
    (∀ x ∈ S, ∀ (τ : E →+* ℂ) (u : ℂ), Commute (cap (a := r + s) τ u) x) ∧
    (∀ x ∈ S, ∀ F : Sm E (r + s), (∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip v * g) = F.1 g) →
      ∀ (v : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), (x F).1 (unip v * g) = (x F).1 g) ∧
    (∀ τ k, a τ k ∈ S) ∧ (∀ τ k, b τ k ∈ S) ∧ (∀ τ, a τ r = 1) ∧ (∀ τ, b τ s = 1) ∧
    (∀ τ, a τ (r - 1) = ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i) + t τ • 1) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capR r s τ (u - (s : ℂ) / 2) = ∑ k ∈ Finset.range (r + 1), u ^ k • a τ k) ∧
    (∀ τ u, GlobalTheory.CompanionTheory.CTFin.capS r s τ (u + (r : ℂ) / 2) = ∑ k ∈ Finset.range (s + 1), u ^ k • b τ k) := by
  first | exact @GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs | exact GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs | (intros; apply GlobalTheory.CompanionTheory.CapCoeff.exists_coeffs <;> assumption)
