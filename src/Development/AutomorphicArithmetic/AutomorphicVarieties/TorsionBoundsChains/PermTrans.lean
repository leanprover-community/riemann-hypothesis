module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FinGroup
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport
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
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permTrans :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] [Nonempty X] (s j : ℕ),
      StabLe G X s → CardLe (groupHomology (permRep G X) (j + 1)) (s ^ (s ^ (j + 1))) := by
  intro G X _ _ _ _ s j hs
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨hfin, hcard⟩ := hs x
  haveI := hfin
  obtain ⟨e⟩ := shapiro G X x (j + 1)
  have h1 := finGroup (MulAction.stabilizer G x) j
  have hpos : 0 < Nat.card (MulAction.stabilizer G x) := Nat.card_pos
  have hle : Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
      ≤ s ^ s ^ (j + 1) := by
    have hs1 : 0 < s := lt_of_lt_of_le hpos hcard
    calc Nat.card (MulAction.stabilizer G x) ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1)
        ≤ s ^ Nat.card (MulAction.stabilizer G x) ^ (j + 1) := Nat.pow_le_pow_left hcard _
      _ ≤ s ^ s ^ (j + 1) := Nat.pow_le_pow_right hs1 (Nat.pow_le_pow_left hcard _)
  exact transport.2.1 _ _ e.symm.toEquiv _ (transport.2.2.2 _ _ _ hle h1)
