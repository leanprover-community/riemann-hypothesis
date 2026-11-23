module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetEqOfSurj
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.EntIntegral
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem conj_sub_one (g u : GL (Fin n) k) : (g⁻¹ * u * g).val - 1 = g⁻¹.val * (u.val - 1) * g.val := by
  simp only [Units.val_mul, mul_sub, sub_mul, mul_one, Units.inv_mul]

theorem mem_stab_iff (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (c : Matrix (Fin n) (Fin n) k)
    (p : Sp k n) (u : GL (Fin n) k) (hcu : u.val * c = c * u.val) (hu : u.val - 1 ∈ Bz Z) :
    u ∈ stab Z p ↔ u.val - 1 ∈ cS Z (p.1 - c) p.2 := by
  have e : (u.val - 1) * (p.1 - c) - (p.1 - c) * (u.val - 1) =
      (u.val * p.1 - p.1 * u.val) - (u.val * c - c * u.val) := by noncomm_ring
  rw [hcu, sub_self, sub_zero] at e
  have e1 : (u.val - 1) * (p.1 - c) = (p.1 - c) * (u.val - 1) ↔ u.val * p.1 = p.1 * u.val := by
    rw [← sub_eq_zero, e, sub_eq_zero]
  have e2 : u.val * p.1 * u⁻¹.val = p.1 ↔ u.val * p.1 = p.1 * u.val := by
    constructor
    · intro h
      calc u.val * p.1 = u.val * p.1 * u⁻¹.val * u.val := by simp [mul_assoc]
        _ = p.1 * u.val := by rw [h]
    · intro h
      rw [h, mul_assoc, Units.mul_inv, mul_one]
  have e3 : u.val *ᵥ p.2 = p.2 ↔ (u.val - 1) *ᵥ p.2 = 0 := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero]
  show (u ∈ Gz Z ∧ act u p = p) ↔ _
  rw [mem_Gz_iff]
  simp only [act, Prod.ext_iff]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨⟨hu, e1.2 (e2.1 h1)⟩, e3.1 h2⟩
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨hu, e2.2 (e1.1 h1), e3.2 h2⟩

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
