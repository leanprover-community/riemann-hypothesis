module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLift

theorem glO_isOpen_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  intro F _ _ _ n
  let B : Set (Matrix (Fin n) (Fin n) F) :=
    Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : F) 1))
  have hB : ∀ A : Matrix (Fin n) (Fin n) F, A ∈ B ↔ ∀ i j, ‖A i j‖ ≤ 1 := by
    intro A
    constructor
    · intro h i j
      have := h i (Set.mem_univ _) j (Set.mem_univ _)
      simpa using this
    · intro h i _ j _
      simpa using h i j
  have hBo : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let S : Set (Matrix (Fin n) (Fin n) F × (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ) :=
    B ×ˢ (MulOpposite.unop ⁻¹' B)
  have hS : glO n F = Units.embedProduct _ ⁻¹' S := by
    ext g
    simp only [glO, Set.mem_setOf_eq, Set.mem_preimage, S, Set.mem_prod, hB, Units.embedProduct_apply,
      MulOpposite.unop_op]
    constructor
    · intro h; exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
    · intro h i j; exact ⟨h.1 i j, h.2 i j⟩
  have hSo : IsOpen S := hBo.prod (hBo.preimage MulOpposite.continuous_unop)
  have hSc : IsCompact S := by
    refine hBc.prod ?_
    have : MulOpposite.unop ⁻¹' B = MulOpposite.op '' B := by
      ext x
      constructor
      · intro h; exact ⟨_, h, MulOpposite.op_unop x⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this]; exact hBc.image MulOpposite.continuous_op
  rw [hS]
  exact ⟨hSo.preimage Units.continuous_embedProduct,
    Units.isClosedEmbedding_embedProduct.isCompact_preimage hSc⟩

end GlobalTheory.JR.GLift
