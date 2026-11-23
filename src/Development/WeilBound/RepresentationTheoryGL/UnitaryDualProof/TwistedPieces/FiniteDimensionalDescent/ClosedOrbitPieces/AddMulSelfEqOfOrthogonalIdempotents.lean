module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop
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

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece

def Cx (Z : Subalgebra k (Matrix (Fin N) (Fin N) k)) (x : Matrix (Fin N) (Fin N) k) : Subalgebra k (Matrix (Fin N) (Fin N) k) :=
  Algebra.adjoin k (insert x (Z : Set (Matrix (Fin N) (Fin N) k)))

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {x : Matrix (Fin N) (Fin N) k}

theorem cx_gens (hZ : CR Z) (hx : x ∈ Bz Z) :
    ∀ a ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)), ∀ b ∈ insert x (Z : Set (Matrix (Fin N) (Fin N) k)),
      a * b = b * a := by
  intro a ha b hb
  rcases Set.mem_insert_iff.1 ha with h1 | h1
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h1, h2]
    · rw [h1]
      exact (hx b h2).symm
  · rcases Set.mem_insert_iff.1 hb with h2 | h2
    · rw [h2]
      exact hx a h1
    · exact hZ.1 a h1 b h2

theorem cx_comm (hZ : CR Z) (hx : x ∈ Bz Z) : ∀ a ∈ Cx Z x, ∀ b ∈ Cx Z x, a * b = b * a := by
  intro a ha b hb
  have key := cx_gens hZ hx
  have h : Commute a b := by
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hb ?_
    intro c hc
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute ha ?_).symm
    intro d hd
    exact key c hc d hd
  exact h.eq

theorem z_le_cx : Z ≤ Cx Z x := fun _ h => Algebra.subset_adjoin (Set.mem_insert_of_mem _ h)

theorem x_mem_cx : x ∈ Cx Z x := Algebra.subset_adjoin (Set.mem_insert _ _)

theorem pe_mem {d : ℕ} {c : Fin d → Matrix (Fin N) (Fin N) k} (hc : ∀ l, c l ∈ Z) : pe c x ∈ Cx Z x :=
  Subalgebra.sum_mem _ fun l _ => Subalgebra.mul_mem _ (z_le_cx (hc l)) (Subalgebra.pow_mem _ x_mem_cx _)

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
