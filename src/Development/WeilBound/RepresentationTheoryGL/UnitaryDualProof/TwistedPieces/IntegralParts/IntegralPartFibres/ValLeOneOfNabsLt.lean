module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.Zpart
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.BaseP

@[expose] public section

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_le_one_of_nabs_lt {t : kˣ} (ht : nabs k t < 1) : valuation k (t : k) ≤ 1 := by
  have h := (nabs_le_iff t 1).1 (by rw [nabs_one]; exact ht.le)
  simpa using h

theorem lat_le_inv {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) : L ≤ ((t⁻¹ : kˣ) : k) • L := by
  intro x hx
  refine (AddSubgroup.mem_smul_pointwise_iff_exists x _ L).2 ⟨(t : k) • x, hL.int _ (val_le_one_of_nabs_lt ht) x hx, ?_⟩
  simp [smul_smul]

theorem lat_smul_le {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) (j : ℕ) : ((t ^ j : kˣ) : k) • L ≤ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists x _ L).1 hx
  refine hL.int _ ?_ y hy
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_one' (val_le_one_of_nabs_lt ht) j

end PositivityTheory.RgUd.TP.Nil.Fib1
