module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialFormInRelativeImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.monomial_form_in_relative_image : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ) (g : Gam n d) (D : {D : Finset (E n d) // D.card = a}), good g D.1 → Tset g D.1 ⊆ S → ∃ ω ∈ relOm K (I0 n K S) a, omMap (incl le_top) a ω = monW K g D := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.RelSup.relForm_of_good <;> assumption)
