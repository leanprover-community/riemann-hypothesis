module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermFormPulledBackCombinationsExpandMonomials
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem _root_.GlobalTheory.T.germ_form_pulledBack_combinations_expand_monomials : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (φ : X ⟶ A₀) (p : X ⟶ T), φ ≫ f = p ≫ g ≫ affπ Rg (mA * mB) → ∀ (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q : N.ι), φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ g ≫ affπ Rg (mA * mB)) z) (comb a φ p (matOf g) z q) F = ∑ ν ∈ (GlobalTheory.FormsLocus.expand mA mB F).support, gs p z ⊤ (GlobalTheory.FormsLocus.ringOf g ((GlobalTheory.FormsLocus.expand mA mB F).coeff ν)) * gs φ z (N.U q) ((GlobalTheory.FormsLocus.monSec a d ν).f q) := by
  first | (exact @GlobalTheory.FormsLocus.germ_eval_comb) | (exact GlobalTheory.FormsLocus.germ_eval_comb) | (intros; apply GlobalTheory.FormsLocus.germ_eval_comb  <;> assumption)
