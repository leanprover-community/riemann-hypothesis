module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC Opposite CochainComplex.HomComplex
namespace LateralTheory.EDual

theorem sec_empty_sub {R : Type} [CommRing R] (G : Shv R) (U : Scheme.{0}) [IsEmpty U] :
    Subsingleton (G.obj.obj (op U)) := by
  have hS := (G.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R))) (⊥ : Sieve U)
    (Scheme.bot_mem_grothendieckTopology U)
  refine ⟨fun x y => ?_⟩
  have e := hS.isSeparatedFor (fun _ _ h => h.elim) (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ x))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)) (fun _ _ h => h.elim) (fun _ _ h => h.elim)
  have := congrArg (fun φ => φ.hom (1 : ULift.{1} R)) e
  simpa using this

end LateralTheory.EDual
