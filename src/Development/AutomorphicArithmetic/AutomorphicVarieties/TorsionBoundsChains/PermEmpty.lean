module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
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

theorem UpperTheory.V.KH.permEmpty :
    ∀ (G X : Type) [Group G] [MulAction G X] [IsEmpty X] (j : ℕ),
      CardLe (groupHomology (permRep G X) j) 1 := by
  intro G X _ _ _ j
  have hC : Subsingleton ((groupHomology.inhomogeneousChains (permRep G X)).X j) := by
    change Subsingleton ((Fin j → G) →₀ (X →₀ ℤ))
    infer_instance
  have hZ : Subsingleton (groupHomology.cycles (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    exact (ModuleCat.mono_iff_injective (groupHomology.iCycles (permRep G X) j)).1
      inferInstance (Subsingleton.elim _ _)
  have hH : Subsingleton (groupHomology (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    induction a using groupHomology_induction_on with
    | h a =>
      induction b using groupHomology_induction_on with
      | h b => rw [Subsingleton.elim a b]
  haveI := hH
  exact ⟨Finite.of_subsingleton, (Finite.card_le_one_iff_subsingleton).2 hH⟩
