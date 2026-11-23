module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearMapOfTraceEq
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Data.Matrix.Basis
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama

@[expose] public section

namespace GlobalTheory.SpanOfResidue

theorem mem_smul_top_of_entries {A : Type} [CommRing A] {r : ℕ} (I : Ideal A)
    (d : Matrix (Fin r) (Fin r) A) (hd : ∀ i j, d i j ∈ I) :
    d ∈ I • (⊤ : Submodule A (Matrix (Fin r) (Fin r) A)) := by
  rw [Matrix.matrix_eq_sum_single d]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have h : Matrix.single i j (d i j) = d i j • Matrix.single i j (1 : A) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul (hd i j) Submodule.mem_top

theorem span_eq_top_of_residue {ι A : Type} [CommRing A] [IsLocalRing A] {r : ℕ}
    (f : ι → Matrix (Fin r) (Fin r) A)
    (h : Submodule.span (IsLocalRing.ResidueField A)
      (Set.range fun (i : ι) ↦ Matrix.map (f i)
        (⇑(IsLocalRing.residue A) : A → IsLocalRing.ResidueField A)) = ⊤) :
    Submodule.span A (Set.range f) = ⊤ := by
  apply GlobalTheory.TraceConj.span_top_of_residual <;> assumption

end GlobalTheory.SpanOfResidue
