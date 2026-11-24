module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.OpenSlice
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.Unimodularity.ModularCharacterFunEqOne
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure GroundTheory.Automorphic

namespace PositivityTheory.RgUd.T.Desc.SLF.Un2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lc_le {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) : Lc Z m ≤ GzS Z := inf_le_left

theorem coe_lc_subgroupOf {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) =
      Subtype.val ⁻¹' (GLnLocal.congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Lc, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem isOpen_lc {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    IsOpen (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) := by
  rw [coe_lc_subgroupOf]
  exact (GLnLocal.isOpen_congruenceSubgroup k n m).preimage continuous_subtype_val

theorem isCompact_lc {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    IsCompact (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) := by
  rw [Subtype.isCompact_iff]
  have e : Subtype.val '' (((Lc Z m).subgroupOf (GzS Z) : Subgroup (GzS Z)) : Set (GzS Z)) =
      (GzS Z : Set (GL (Fin n) k)) ∩ (GLnLocal.congruenceSubgroup k n m : Set (GL (Fin n) k)) := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Lc, Subgroup.mem_inf]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, hx.1⟩, hx, rfl⟩⟩
  rw [e]
  exact (GLnLocal.isCompact_congruenceSubgroup k n m).inter_left (isClosed_GzS Z)

theorem unimod_of_indexSym (hI : IndexSym (k := k)) : Unimod (k := k) := by
  intro n Z hZ g
  change modularCharacterFun g = 1
  obtain ⟨c, hc⟩ := hI n Z hZ g.1 g.2
  obtain ⟨hle, heq, hne⟩ := hc c le_rfl (c + c) le_rfl
  have hmap : (Lc Z c).map (MulAut.conj g.1).toMonoidHom ≤ GzS Z := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (GzS Z).mul_mem ((GzS Z).mul_mem g.2 (lc_le Z c hy)) ((GzS Z).inv_mem g.2)
  refine modularCharacterFun_eq_one g ((Lc Z c).subgroupOf (GzS Z))
    (((Lc Z c).map (MulAut.conj g.1).toMonoidHom).subgroupOf (GzS Z)) ((Lc Z (c + c)).subgroupOf (GzS Z))
    (isCompact_lc Z c) (isOpen_lc Z c) (isOpen_lc Z (c + c)) ?_ ?_ ?_ ?_ ?_
  · intro x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (hle hx).1
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (hle hx).2
  · rw [Subgroup.relIndex_subgroupOf hmap, Subgroup.relIndex_subgroupOf (lc_le Z c)]
    exact heq
  · rw [Subgroup.relIndex_subgroupOf (lc_le Z c)]
    exact hne

end PositivityTheory.RgUd.T.Desc.SLF.Un2
