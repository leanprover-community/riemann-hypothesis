module

public import Formalism.CoboundaryTransfers.Statement
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

noncomputable section

namespace Formalism.CoboundaryTransfers

namespace WachMod

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
  (W : WachMod B M D)

theorem smulO_eq (c : O) (x : D) : c • x = algebraMap O A c • x := by
  rw [algebraMap_smul]

theorem smulO_mem (c : O) {x : D} (hx : x ∈ W.N) : c • x ∈ W.N := by
  rw [smulO_eq (A := A)]; exact W.N.smul_mem _ hx

theorem qInv_smul (a : A) {y : D} (hy : W.QInv y) : W.QInv (a • y) := by
  simp only [QInv]; rw [smul_comm]; exact W.N.smul_mem a hy

theorem qInv_smulO (c : O) {y : D} (hy : W.QInv y) : W.QInv (c • y) := by
  rw [smulO_eq (A := A)]; exact W.qInv_smul _ hy

theorem xN_smul (a : A) {z : D} (hz : W.XN z) : W.XN (a • z) := by
  obtain ⟨n, hn, rfl⟩ := hz
  exact ⟨a • n, W.N.smul_mem a hn, smul_comm _ _ _⟩

theorem xN_smulO (c : O) {z : D} (hz : W.XN z) : W.XN (c • z) := by
  rw [smulO_eq (A := A)]; exact W.xN_smul _ hz

theorem isOneCochain_smul_of_tower (c : O) {y z : D} (h : W.C1 y z) : W.C1 (c • y) (c • z) :=
  ⟨W.qInv_smulO c h.1, W.xN_smulO c h.2⟩

theorem diffOne_smul_of_tower (c : O) (y z : D) : W.d1 (c • y) (c • z) = c • W.d1 y z := by
  simp only [d1, map_smul, smul_sub]

theorem cocycle_smulO (c : O) {y z : D} (h : W.Cocycle y z) : W.Cocycle (c • y) (c • z) :=
  ⟨W.isOneCochain_smul_of_tower c h.1, by rw [W.diffOne_smul_of_tower, h.2, smul_zero]⟩

end WachMod

end Formalism.CoboundaryTransfers
