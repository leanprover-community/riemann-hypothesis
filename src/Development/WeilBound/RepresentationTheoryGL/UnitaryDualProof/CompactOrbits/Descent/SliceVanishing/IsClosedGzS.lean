module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.PullHomeoApply
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocStep
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import GroundTheory.AutomorphicForms.GLnLocal
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.CommutingInverses.InvCommOfComm
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVan

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def GzS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Subgroup (GL (Fin n) k) where
  carrier := Gz Z
  one_mem' a _ := by simp
  mul_mem' {g h} hg hh a ha := by
    simp only [Units.val_mul]
    rw [← mul_assoc, hg a ha, mul_assoc, hh a ha, mul_assoc]
  inv_mem' {g} hg a ha := by
    have h1 := hg a ha
    calc a * (g⁻¹).val = (g⁻¹).val * (g.val * a) * (g⁻¹).val := by simp [← mul_assoc]
      _ = (g⁻¹).val * (a * g.val) * (g⁻¹).val := by rw [h1]
      _ = (g⁻¹).val * a := by simp [mul_assoc]

theorem isClosed_GzS (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : IsClosed (GzS Z : Set (GL (Fin n) k)) := by
  have hset : (GzS Z : Set (GL (Fin n) k)) = ⋂ a ∈ Z, {g : GL (Fin n) k | a * g.val = g.val * a} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [hset]
  exact isClosed_biInter fun a _ =>
    isClosed_eq (continuous_const.mul Units.continuous_val) (Units.continuous_val.mul continuous_const)

instance gzs_lc (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : LocallyCompactSpace (GzS Z) :=
  (isClosed_GzS Z).isClosedEmbedding_subtypeVal.locallyCompactSpace

def conjB (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (hg : g ∈ Gz Z) :
    Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) →ₗ[k]
      Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) where
  toFun x := ⟨g.val * x.1 * g⁻¹.val, (Subalgebra.mem_centralizer_iff k).2 fun a ha => by
    have hx := (Subalgebra.mem_centralizer_iff k).1 x.2 a ha
    have h1 := hg a ha
    have h2 : a * g⁻¹.val = g⁻¹.val * a := (GzS Z).inv_mem (x := g) hg a ha
    calc a * (g.val * x.1 * g⁻¹.val) = (a * g.val) * x.1 * g⁻¹.val := by simp only [mul_assoc]
      _ = g.val * (a * x.1) * g⁻¹.val := by rw [h1]; simp only [mul_assoc]
      _ = g.val * x.1 * (a * g⁻¹.val) := by rw [hx]; simp only [mul_assoc]
      _ = g.val * x.1 * g⁻¹.val * a := by rw [h2]; simp only [mul_assoc]⟩
  map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c x := Subtype.ext (by simp)

def Unimod : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)), CR Z → PositivityTheory.PfBern.Frob.IsUnimod (GzS Z)

end PositivityTheory.RgUd.T.Desc.SLF
