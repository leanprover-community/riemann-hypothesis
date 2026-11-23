module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Topology.Algebra.Group.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

theorem UpperTheory.isOpen_right_invariance :
    ∀ {H F G : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group F] [TopologicalSpace F] [Group G]
        (ι : H →* F) (f : F →* G) (U : Subgroup F) (φ : G → ℂ), Continuous ι → IsOpen (U : Set F) →
        (∀ u ∈ U, ∀ g, φ (g * f u) = φ g) → IsOpen {h : H | (fun x => φ (x * f (ι h))) = φ} := by
  intro H F G _ _ _ _ _ _ ι f U φ hι hU hφ
  let S : Subgroup H :=
    { carrier := {h : H | (fun x => φ (x * f (ι h))) = φ}
      one_mem' := by
        funext x
        simp
      mul_mem' := by
        intro a b ha hb
        funext x
        have h1 : φ (x * f (ι a) * f (ι b)) = φ (x * f (ι a)) := congrFun hb (x * f (ι a))
        have h2 : φ (x * f (ι a)) = φ x := congrFun ha x
        rw [map_mul, map_mul, ← mul_assoc, h1, h2]
      inv_mem' := by
        intro a ha
        funext x
        have h1 : φ (x * f (ι a⁻¹) * f (ι a)) = φ (x * f (ι a⁻¹)) := congrFun ha (x * f (ι a⁻¹))
        rw [← h1]
        simp }
  have hle : U.comap ι ≤ S := by
    intro h hh
    funext x
    exact hφ (ι h) hh x
  have hopen : IsOpen ((U.comap ι : Subgroup H) : Set H) := hU.preimage hι
  exact Subgroup.isOpen_mono hle hopen
