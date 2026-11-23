module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaloisCharacterPadicAlgClosureEqOne
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs

@[expose] public section

open NumberField GlobalTheory.ExpFrame Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N ReciprocityTheory.Gal Formalism.ConjugateSelfDual Polynomial

theorem _root_.GlobalTheory.T.norm_galoisCharacter_padicAlgClosure_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (χ : G E Ω →* (PadicAlgCl l)ˣ), Continuous (GlobalTheory.TripleGal.rk1 χ) → ∀ g, ‖((χ g : (PadicAlgCl l)ˣ) : PadicAlgCl l)‖ = 1 := by
  first | exact @GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | exact GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one | (intros; apply GlobalTheory.ExpFrame.CharUnit.norm_char_eq_one <;> assumption)
