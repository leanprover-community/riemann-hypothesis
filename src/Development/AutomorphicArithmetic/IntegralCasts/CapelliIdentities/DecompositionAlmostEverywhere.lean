module

public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped IntermediateField Algebra TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
attribute [local instance] Formalism.L2.Theta.IsVolMeasG._proof_2 Formalism.L2.Theta.IsVolMeasG._proof_1 Formalism.L2.Theta.IsDsig._proof_2 Formalism.L2.Theta.IsVolMeasG._proof_3

theorem UpperTheory.Reformulated.B.DecompositionAlmostEverywhere.decomp_AE :
    ∀ {D : Formalism.BasicNotions.D7},
    (↥D.host.F)[D.host.sqrtMinusD] = ⊤ →
      ∀ (z : Formalism.L2.Theta.AE D),
        ∃ (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (q : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F),
          z =
            (Algebra.algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (Formalism.L2.Theta.AE D) :
                  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F → Formalism.L2.Theta.AE D)
                p +
              (Algebra.algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) (Formalism.L2.Theta.AE D) :
                    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F → Formalism.L2.Theta.AE D)
                  q *
                (Formalism.L2.Theta.incA D : D.host.E → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) D.host.E)
                  D.host.sqrtMinusD := by
  intro D h z
  have hz : z ∈ Algebra.adjoin (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) {Formalism.L2.Theta.incA D D.host.sqrtMinusD} := by
    have := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥D.host.F) _ h
    exact (Set.image_singleton ▸ this).ge Algebra.mem_top
  have hs : Formalism.L2.Theta.incA D D.host.sqrtMinusD ^ 2 = -(D.host.d : Formalism.L2.Theta.AE D) := by
    rw [← map_pow, Formalism.BasicNotions.Host.sqrtMinusD, D.host.sqd_sq, map_neg, map_natCast]
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [map_zero, map_one, zero_add, one_mul]; exact hx⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add x y _ _ hx hy => obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hy; exact ⟨a + c, b + e, by rw [map_add (f := _), map_add (f := _)]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨⟨a, b, rfl⟩, c, e, rfl⟩ := And.intro hx hy
    exact ⟨a * c - D.host.d * (b * e), a * e + b * c, by
      simp only [map_add (f := _), map_sub, map_mul, map_natCast]; linear_combination (algebraMap _ _ b * algebraMap _ _ e) * hs⟩
