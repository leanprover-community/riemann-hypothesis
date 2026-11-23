module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.DualWeil
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve PadicInt

universe u

variable {F : Type u} [Field F] [IsAlgClosed F] [DecidableEq F]

namespace TateCharpoly

variable {E E' E'' : WeierstrassCurve F} [E.IsElliptic] [E'.IsElliptic] [E''.IsElliptic]

theorem homPt_homComp (R : isogHom E' E'') (Q : isogHom E E') :
    homPt (homComp R Q) = (homPt R).comp (homPt Q) := by
  by_cases hQ : Q = 0
  · subst hQ
    rw [homComp_zero_right, homPt_zero, homPt_zero, AddMonoidHom.comp_zero]
  by_cases hR : R = 0
  · subst hR
    rw [homComp_zero_left, homPt_zero, homPt_zero, AddMonoidHom.zero_comp]
  obtain ⟨φ, rfl⟩ : ∃ φ : Isogeny E E', φ.toHom = Q := ⟨isogOfHom Q hQ, rfl⟩
  obtain ⟨ψ, rfl⟩ : ∃ ψ : Isogeny E' E'', ψ.toHom = R := ⟨isogOfHom R hR, rfl⟩
  rw [Isogeny.homComp_toHom, homPt_toHom, homPt_toHom, homPt_toHom]
  ext P
  rw [AddMonoidHom.comp_apply, Isogeny.pointHom_apply, Isogeny.pointHom_apply,
    Isogeny.pointHom_apply, Isogeny.pointMap_comp]

end TateCharpoly

open TateCharpoly

variable {E : WeierstrassCurve F} [E.IsElliptic] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

variable {ℓ}

namespace TateCharpoly

end TateCharpoly

end GroundTheory.Arith.Abelian
