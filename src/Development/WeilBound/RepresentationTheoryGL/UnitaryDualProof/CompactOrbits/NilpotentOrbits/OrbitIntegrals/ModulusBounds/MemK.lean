module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.EntIntegral
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.IsClosedGz
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

set_option linter.unusedSectionVars false

open Matrix Module ValuativeRel MeasureTheory GroundTheory.Automorphic.GLnLocal

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem memK (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (m : ℕ) (hm : 1 ≤ m) (u : GL (Fin n) k) :
    u ∈ congruenceSubgroup k n m ⊓ GzS Z ↔
      u.val - 1 ∈ lat (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))).toSubmodule
        (valuation k (uniformizer k : k) ^ m) := by
  rw [Subgroup.mem_inf, mem_lat, mem_C_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(mem_Gz_iff Z u).1 h2, fun i j => ?_⟩
    have := ((mem_congruenceSubgroup_iff k n).1 h1).2 i j
    simpa [Matrix.sub_apply] using this
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hw, hwv⟩ := exists_unit (k := k) m hm (u.val - 1) h2
    have : w = u := Units.ext (by rw [hwv]; abel)
    exact ⟨this ▸ hw, (mem_Gz_iff Z u).2 h1⟩

theorem memK' (K : Subgroup (GL (Fin n) k)) (g u : GL (Fin n) k) :
    u ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * u * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

end PositivityTheory.RgUd.T.Nil.Orb.BModbound
