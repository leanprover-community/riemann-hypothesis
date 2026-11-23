module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem ball_product_length : PiBallFrom := by
  intro hPi hBQ D B P j X ka wL wF G la Q S CRm T e c hOk k

  have hC : Q.InCurve := hOk.2.1
  haveI : FiniteDimensional (Kp X la G.N) (OsK X la G.w) := hC.1
  haveI : IsReduced (OsK X la G.w) := hC.2.1
  haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC

  have hle : ballO (unifO X la G.N) Q.e Q.c ≤
      ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)) := by
    intro v hv
    exact ball_mono hU hC.2.2 (fun ζ => by dsimp only; omega) hv

  have h1 := hPi (Op X la G.N) (SectionSheafQuotient X la G.w wF) (Mon (WeightFamilies.dimY D j) k)
    (ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)))
    (ballO (unifO X la G.N) Q.e Q.c) hle
  have h2 := hBQ (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N)
    (unifO_irreducible X la G.N) (finite_As_of_curve Q hC) (SectionSheafQuotient X la G.w wF) Q.e hC.2.2 Q.c (Q.mm S T e)
  refine h1.trans ?_
  rw [h2, Fintype.card_coe, Nat.cast_mul]

end PI.PoleLengthCount
