module

public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource
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
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta

theorem _root_.GlobalTheory.T.no_invariant_pairing_smaller_fock_source : ∀ X : ProvA, admQ5 X → ArchimedeanRallisFifth X → ∀ (t : ℕ) (al be ga de : List ℚ), DataAR t al be ga de → (∀ e ∈ al ++ be ++ ga ++ de, ((t : ℚ) + 3) / 2 ≤ |e|) → ∀ i : ℕ, 1 ≤ i → i ≤ al.length + be.length → i ≤ ga.length + de.length → ∀ b : Pol (al.length + be.length - i) (ga.length + de.length - i) _ _ →ₗ[ℂ] (X.ds _ _ (lamA' t al be ga de)).HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq _ _, ∀ P y, b (fockAct2 _ _ _ _ Z P) y + b P ((X.ds _ _ (lamA' t al be ga de)).HK.act Z y) = 0) → b = 0 := by
  first | exact @GlobalTheory.NoInvPairing.no_pairing_smaller_source | exact GlobalTheory.NoInvPairing.no_pairing_smaller_source | (intros; apply GlobalTheory.NoInvPairing.no_pairing_smaller_source <;> assumption)
