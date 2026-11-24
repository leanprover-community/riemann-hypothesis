module

public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HatLettersPassDiGIBoundedFactors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.hatLetters_pass_Di_gI_boundedFactors : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → (∀ X ∈ hats d.L, X * d.L.Di ∈ nfSpan d (hats d.L) 1 0 1 ∧ X * TL.gI d.L ∈ nfSpan d (hats d.L) 0 1 1) ∧ (∀ b ∈ bmon d, (∀ f ∈ d.L.fns, Commute b f) ∧ Commute b d.L.Di ∧ Commute b (TL.gI d.L) ∧ star b ∈ bmon d) ∧ Commute d.L.Di (TL.gI d.L) := by
  first | exact @GlobalTheory.HatNF.Den.hat_den | exact GlobalTheory.HatNF.Den.hat_den | (intros; apply GlobalTheory.HatNF.Den.hat_den <;> assumption)
