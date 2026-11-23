module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.IsogenyPoints
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
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny

@[expose] public section

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

universe u

section Defs

variable {F : Type u} [Field F] [DecidableEq F] (E : WeierstrassCurve F) (p : ℕ)

end Defs

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F] (E : WeierstrassCurve F)
  [E.IsElliptic] (p : ℕ) [hp : Fact p.Prime] [CharP F p]


omit [IsAlgClosed F] [E.IsElliptic] hp [CharP F p] in
theorem mem_torsionBy_natCast_iff (n : ℕ) (P : E.toAffine.Point) :
    P ∈ AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) ↔ n • P = 0 :=
  AddSubgroup.torsionBy.nsmul_iff


omit hp [CharP F p] in
theorem finite_torsionBy_natCast {n : ℕ} (hn : n ≠ 0) :
    Finite (AddSubgroup.torsionBy E.toAffine.Point (n : ℤ)) := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine Finite.of_injective (fun P : AddSubgroup.torsionBy E.toAffine.Point (n : ℤ) =>
    (⟨P.1, ?_⟩ : (mulIsogeny E n hn').pointHom.ker)) ?_
  · rw [AddMonoidHom.mem_ker, Isogeny.pointHom_apply, Isogeny.pointMap_mulIsogeny, natCast_zsmul]
    exact (mem_torsionBy_natCast_iff E n P.1).mp P.2
  · intro P Q h
    apply Subtype.ext
    exact congrArg (fun x : (mulIsogeny E n hn').pointHom.ker => (x : E.toAffine.Point)) h














end GroundTheory.Arith.Abelian
