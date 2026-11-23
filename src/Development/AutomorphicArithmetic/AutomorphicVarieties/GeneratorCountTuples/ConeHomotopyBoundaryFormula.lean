module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LeftMultiplication.Lmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.ToInhPartialProd
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

open UpperTheory.V.ZK UpperTheory.V.ZK.PM

private theorem hp_eq (A : Type) [CommRing A] (G : Type) [Group G] (k : G) :
    ∀ (m : ℕ) (z : Ch A G m), hp A k m z = hprism A (· * k) m z
  | 0, z => by rw [hprism_zero]; rfl
  | m + 1, z => ch_ext A (fun x => by
      have h := hprism_cone A (· * k) (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [← hmap_cone A (· * k), cone_single, Fin.cons_self_tail] at h
      rw [h, hp, Finsupp.linearCombination_single, one_smul, hp_eq A G k m, map_sub]
      rfl) z

theorem UpperTheory.coneHomotopy_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k : G) (m : ℕ) (z : Ch A G (m + 1)), pr A G (m + 1) (hp A k (m + 1) z) = prism A k m (pr A G m z) := by
  intro A _ G _ k m z
  rw [hp_eq]
  exact (prism_toInh A k m z).symm
