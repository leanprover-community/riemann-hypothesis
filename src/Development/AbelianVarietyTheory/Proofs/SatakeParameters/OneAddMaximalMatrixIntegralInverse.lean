module

public import Formalism.SatakeDualWeyl.StatementF
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.Hk3

theorem one_add_maximal_inv_int (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (n : ℕ) (X : Matrix (Fin n) (Fin n) L) (hX : ∀ i j, Valued.v (X i j) < 1) :
    ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧
      ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  classical
  let v : Valuation L (WithZero (Multiplicative ℤ)) := Valued.v
  let O := v.valuationSubring
  let Y : Matrix (Fin n) (Fin n) O := fun i j => ⟨X i j, (hX i j).le⟩
  have hY : ∀ i j, IsLocalRing.residue O (Y i j) = 0 := fun i j => by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff L v).2 (hX i j)
  have h1 : (IsLocalRing.residue O).mapMatrix (1 + Y) = 1 := by
    rw [map_add (f := _), map_one]
    have : (IsLocalRing.residue O).mapMatrix Y = 0 := by
      ext i j; exact hY i j
    rw [this, add_zero]
  have hd : IsUnit (1 + Y).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1, det_one]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨Units.map (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* _).toMonoidHom u, ?_, ?_⟩
  · show O.subtype.mapMatrix (u : Matrix (Fin n) (Fin n) O) = _
    rw [hu, map_add (f := _), map_one]
    rfl
  · intro i j
    rw [← map_inv]
    exact ((u⁻¹ : (Matrix (Fin n) (Fin n) O)ˣ).1 i j).2

end GlobalTheory.Hk3
