module

public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalBlockSumSqNormBlockUnitaryInvariantStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

theorem offDiagBlockNorm_cont_inv : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  intro n ε
  refine ⟨?_, ?_⟩
  · have hM : Continuous fun g : UJ ε => toM g :=
      Units.continuous_val.comp continuous_subtype_val
    refine continuous_finsetSum _ fun z _ => ?_
    exact ((continuous_apply z.1.2).comp ((continuous_apply z.1.1).comp hM)).norm.pow 2
  · intro k k' g
    have hk : toM (k : UJ ε) ∈ Kset ε := k.2
    have hk' : toM (k' : UJ ε) ∈ Kset ε := k'.2
    have hmul : toM ((k : UJ ε) * g * (k' : UJ ε)) = toM (k : UJ ε) * toM g * toM (k' : UJ ε) := rfl
    rw [hmul]
    refine GlobalTheory.T.offDiagonalBlock_sum_sq_norm_blockUnitary_invariant n ε _ _ _ ?_ hk.2 ?_ hk'.2
    · exact Matrix.mem_unitaryGroup_iff'.mp hk.1
    · exact Matrix.mem_unitaryGroup_iff'.mp hk'.1

end GlobalTheory
