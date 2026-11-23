module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_localization_of_regular_quotient :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (p : Ideal R) [p.IsPrime] [IsRegularLocalRing (R ⧸ p)],
      IsRegularLocalRing (Localization.AtPrime p) ∧
      ringKrullDim (Localization.AtPrime p) + ringKrullDim (R ⧸ p) = ringKrullDim R := by
  intro R _ _ p _ _
  obtain ⟨r, x, hx, hsp⟩ := exists_cotInd_of_regular_quotient R p
  obtain ⟨-, hdim, -⟩ := regular_quotient_cotInd R _ x hx
  obtain ⟨hh, hreg⟩ := regular_localization_cotInd R _ x hx p hsp.symm
  refine ⟨hreg, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hh, add_comm]
  rw [hsp] at hdim
  rw [← hdim]
  rfl
