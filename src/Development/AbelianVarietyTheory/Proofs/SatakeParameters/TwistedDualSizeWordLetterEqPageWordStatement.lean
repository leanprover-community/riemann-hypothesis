module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWord
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

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

theorem _root_.GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG), Roomy L C → ∀ a : ZMod (orderOf ψ), (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧ (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧ (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧ (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | exact GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | (intros; apply GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord <;> assumption)
