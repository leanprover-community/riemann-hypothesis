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

private theorem hbd_eq (A : Type) [CommRing A] (G : Type) [Group G] :
    ∀ (m : ℕ) (z : Ch A G (m + 1)), PM.hbd A G m z = UpperTheory.V.ZK.hbd A G m z
  | 0, z => ch_ext A (fun x => by
      have h := hbd_cone_zero A (x 0) (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul]) z
  | m + 1, z => ch_ext A (fun x => by
      have h := hbd_cone A (x 0) m (Finsupp.single (Fin.tail (α := fun _ => G) x) 1)
      rw [cone_single, Fin.cons_self_tail] at h
      rw [h, PM.hbd, Finsupp.linearCombination_single, one_smul, hbd_eq A G m]
      rfl) z

theorem UpperTheory.tupleChain_boundary_formula :
    ∀ (A : Type) [CommRing A] (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 2)), bd A G m (pr A G (m + 1) z) = pr A G m (PM.hbd A G (m + 1) z) := by
  intro A _ G _ m z
  rw [hbd_eq]
  exact bd_toInh A m z
