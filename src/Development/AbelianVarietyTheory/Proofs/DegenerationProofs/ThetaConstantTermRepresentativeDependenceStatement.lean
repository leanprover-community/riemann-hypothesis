module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantTermRepresentativeDependence
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

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaConstantTerm_representative_dependence : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  first | exact @GlobalTheory.Ex.txT_shift | exact GlobalTheory.Ex.txT_shift | (intros; apply GlobalTheory.Ex.txT_shift <;> assumption)
