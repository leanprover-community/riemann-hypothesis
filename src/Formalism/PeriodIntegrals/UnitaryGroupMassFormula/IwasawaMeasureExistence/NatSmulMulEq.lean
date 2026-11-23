module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdeleRing
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

def Bx (N : ℕ) : Set (Af I.F) := (fun u => algebraMap I.F (Af I.F) ((N : I.F)⁻¹) * u) '' Ohat I.F

theorem isCompact_Bx (N : ℕ) : IsCompact (Bx I N) :=
  isCompact_Ohat.image (continuous_const.mul continuous_id)

theorem mem_Bx {N : ℕ} (hN : 0 < N) {a : Af I.F} (ha : N • a ∈ Ohat I.F) : a ∈ Bx I N := by
  refine ⟨N • a, ha, ?_⟩
  have hN0 : (N : I.F) ≠ 0 := by exact_mod_cast hN.ne'
  simp only
  rw [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap I.F (Af I.F)), ← map_mul, inv_mul_cancel₀ hN0,
    map_one, one_mul]

end Cpt

end PI.IwaMeasEx.Wau

end

noncomputable section

namespace PI.IwaMeasEx.Wau

open IsDedekindDomain NumberField Formalism.MainNotions.S Topology
open scoped TensorProduct Matrix

namespace Cpt

variable (I : AutInst)

end Cpt

end PI.IwaMeasEx.Wau

end
