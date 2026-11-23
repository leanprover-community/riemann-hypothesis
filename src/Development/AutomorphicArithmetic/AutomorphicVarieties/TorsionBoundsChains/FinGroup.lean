module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.ImportsAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Subquot
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

open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.finGroup :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ),
      CardLe (HZ S (j + 1)) (Nat.card S ^ (Nat.card S ^ (j + 1))) := by
  intro S _ _ j
  have hi : Function.Injective (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hq : Function.Surjective (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom :=
    fun x => groupHomology_induction_on x fun y => ⟨y, rfl⟩
  have h := subquot (Fin (j + 1) → S) (groupHomology.cycles (Rep.trivial ℤ S ℤ) (j + 1))
    (HZ S (j + 1)) (groupHomology.iCycles (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom
    (groupHomology.π (Rep.trivial ℤ S ℤ) (j + 1)).hom.toAddMonoidHom (Nat.card S)
    Nat.card_pos hi hq (kill S j)
  rwa [Nat.card_fun, Nat.card_fin] at h
