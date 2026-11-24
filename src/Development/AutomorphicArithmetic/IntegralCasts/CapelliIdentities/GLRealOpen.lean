module

public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GlR
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

theorem UpperTheory.Reformulated.B.GLRealOpen.glR_open :
    ∀ {K : Type} [inst : CommRing K] [inst_1 : TopologicalSpace K] [IsTopologicalRing K] (R : Subring K),
      IsOpen (↑R : Set K) → ∀ (n : ℕ), IsOpen (↑(UpperTheory.Reformulated.B.GeneralLinearGroupOverSubring.glR R n) : Set (GL (Fin n) K)) := by
  intro K _ _ _ R hR n
  have hM : IsOpen {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R} := by
    have e : {M : Matrix (Fin n) (Fin n) K | ∀ i j, M i j ∈ R}
        = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) K => M i j) ⁻¹' (R : Set K) := by
      ext M
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rw [e]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hR.preimage (continuous_id.matrix_elem i j)
  have h1 : Continuous fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_val
  have h2 : Continuous fun g : GL (Fin n) K => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    Units.continuous_coe_inv
  exact (hM.preimage h1).inter (hM.preimage h2)
