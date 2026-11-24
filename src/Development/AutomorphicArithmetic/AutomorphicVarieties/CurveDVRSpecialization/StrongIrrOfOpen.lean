module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

@[expose] public section

open Matrix

theorem UpperTheory.V.Pr.strongIrrOfOpen :
    UpperTheory.V.Pr.StrongIrrOfOpen := by
  intro G κ _ _ _ _ n r hlin hirr W S hS hiff
  have hset : (S : Set G) = ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator,
      {g | φ (UpperTheory.V.Pr.gm r g *ᵥ v) = 0} := by
    ext g
    simp only [SetLike.mem_coe, hiff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h v hv φ hφ
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ
    · intro h v hv
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (h v hv)
  have hclosed : IsClosed (S : Set G) := by
    rw [hset]
    refine isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_
    let f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ :=
      { toFun := fun M => φ (M *ᵥ v)
        map_add' := by
          intro A B
          simp [Matrix.add_mulVec]
        map_smul' := by
          intro c A
          simp [Matrix.smul_mulVec] }
    exact hlin f
  have hopen : IsOpen (S : Set G) := S.isOpen_of_isClosed_of_finiteIndex hclosed
  apply hirr S hopen W
  intro g hg v hv
  exact (hiff g).mp hg v hv
