module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP

@[expose] public section

open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HolomorphicRootNormBound

theorem vNormSq_lt_of_root :
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StrictAnti lam → IsHolChamber ε lam → ∀ a b : Fin n, ε a = true → ε b = false → vNormSq ε (lowK ε lam - root a b) < vNormSq ε (lowK ε lam) := by
  intro n ε lam hanti hch a b ha hb
  have hA1 : CompanionTheory.D.DSIC.A1 ε = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    rw [CompanionTheory.D.DSIC.A1, Finset.mem_filter] at hi
    exact absurd (hch.lt hanti i.2.1 i.2.2) (not_lt.2 hi.2.le)
  let i : CompanionTheory.D.DSIC.NC ε := ⟨(a, b), ha, hb⟩
  have hne : ({i} : Finset (CompanionTheory.D.DSIC.NC ε)) ≠ CompanionTheory.D.DSIC.A1 ε := by
    rw [hA1]; exact Finset.singleton_ne_empty i
  have h := CompanionTheory.D.DSIC.hNormLt n ε lam hanti {i} hne
  have hgam : CompanionTheory.D.DSIC.gam ε lam = lowK ε lam := by
    funext c
    simp [CompanionTheory.D.DSIC.gam, hA1, CompanionTheory.D.DSIC.wtA]
    rfl
  have hw : CompanionTheory.D.DSIC.wtA ({i} : Finset (CompanionTheory.D.DSIC.NC ε)) = root a b := by
    funext c
    simp only [CompanionTheory.D.DSIC.wtA, Finset.filter_singleton, root, Pi.sub_apply, Pi.single_apply, i]
    by_cases h1 : a = c <;> by_cases h2 : b = c <;> simp [h1, h2, eq_comm]
  rw [hgam, hw] at h
  exact h

end GlobalTheory.HolomorphicRootNormBound
