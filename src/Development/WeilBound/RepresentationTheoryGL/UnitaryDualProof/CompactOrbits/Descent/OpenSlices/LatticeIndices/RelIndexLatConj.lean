module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.ValuationPiNeZero
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.OpenSlice
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.DtExistsScaleFin
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.OpenSlices.LatticeIndices.OneAddMemZeroLattice
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
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic

namespace PositivityTheory.RgUd.T.Desc.SLT

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.T.Desc.SLT.Bi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem Bi.Lat_eq_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) :
    Lat Z m = (Lat Z 0).map (smulA (pi k ^ m)) := by
  simpa using Lat_add Z m 0

private theorem smulA_injective' (m : ℕ) :
    Function.Injective (smulA (k := k) (n := n) (pi k ^ m)) := by
  have hp : pi k ^ m ≠ 0 :=
    pow_ne_zero _ ((Valuation.ne_zero_iff _).1 (GLnLocal.valuation_uniformizer_ne_zero k))
  intro x y hxy
  exact smul_right_injective (Matrix (Fin n) (Fin n) k) hp hxy

theorem Bi.relIndex_lat (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m r : ℕ) :
    (Lat Z (m + r)).relIndex (Lat Z m) = (Lat Z r).relIndex (Lat Z 0) := by
  rw [Lat_add Z m r, Lat_eq_map Z m,
    AddSubgroup.relIndex_map_map_of_injective _ _ (smulA_injective' m)]

theorem Bi.relIndex_lat_conj (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g : GL (Fin n) k) (m r : ℕ) :
    (Lat Z (m + r)).relIndex ((Lat Z m).map (conjA g)) = ((Lat Z r).map (conjA g⁻¹)).relIndex (Lat Z 0) := by
  rw [Lat_add Z m r, Lat_eq_map Z m]
  have hcomm : ((Lat Z 0).map (smulA (pi k ^ m))).map (conjA g) =
      ((Lat Z 0).map (conjA g)).map (smulA (pi k ^ m)) := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    ext1 x
    exact conjA_smulA g _ x
  rw [hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ (smulA_injective' m)]
  have hid : (conjA g⁻¹).comp (conjA g) = AddMonoidHom.id _ := by
    ext1 x
    exact conjA_inv_conjA g x
  have := AddSubgroup.relIndex_map_map_of_injective (Lat Z r) ((Lat Z 0).map (conjA g))
    (conjA_injective g⁻¹)
  rw [AddSubgroup.map_map, hid, AddSubgroup.map_id] at this
  exact this.symm

theorem indexSym [CharZero k] : IndexSym (k := k) := by
  intro n Z hZ g hg
  obtain ⟨c0, hc01, hc0⟩ := exists_shift Z g hg
  obtain ⟨c1, hc1⟩ := core Z hZ g hg
  refine ⟨c0 + c1, fun m hm m' hm' => ?_⟩
  have h1m : 1 ≤ m := by omega
  obtain ⟨r, rfl⟩ : ∃ r, m' = m + r := ⟨m' - m, by omega⟩
  have hr : c1 ≤ r := by omega
  refine ⟨Lc_le Z g hg c0 hc0 h1m (by omega), ?_, ?_⟩
  · rw [relIndex_Lc_conj Z g hg c0 hc0 h1m (by omega) (by omega), relIndex_Lc Z h1m (by omega),
      Bi.relIndex_lat_conj, Bi.relIndex_lat]
    exact (hc1 r hr).1
  · rw [relIndex_Lc Z h1m (by omega), Bi.relIndex_lat]
    exact (hc1 r hr).2

end PositivityTheory.RgUd.T.Desc.SLT
