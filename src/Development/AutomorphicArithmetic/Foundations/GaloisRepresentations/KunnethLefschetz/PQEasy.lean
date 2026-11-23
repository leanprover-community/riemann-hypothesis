module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

theorem qEasy_holds : QEasy := by
  unfold QEasy
  intro l _ k _ G
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  refine ⟨?_, ?_, ?_⟩
  · intro d e Z X p ι h n m hn U hU a
    have h0 : (pullHl l (sch.map U.ι) m 0).comp (G.hl h hn) = 0 :=
      LinearMap.ext fun x => Subtype.ext (funext fun j =>
        (G.exact j h hn U hU _).mpr ⟨x.1 j, rfl⟩)
    have h1 : (pb l U.ι m).comp (G.q h hn) = 0 := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, h0, LinearMap.baseChange_zero]
    exact LinearMap.congr_fun h1 a
  · intro d e Z X p ι h n m hn U hU hs
    have hinj : Function.Injective (G.hl h hn) := fun x y hxy =>
      Subtype.ext (funext fun j => G.inj j h hn U hU (hs j) (congrArg (fun z => z.1 j) hxy))
    unfold Gys0.q
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro d e' e Z' X' Z X p' ι' p ι h' h f u hf hp n m hn a
    have h0 : (pullHl l (sch.map f) m 0).comp (G.hl h hn) =
        (G.hl h' hn).comp (pullHl l (sch.map u) n 0) :=
      LinearMap.ext fun x => Subtype.ext (funext fun j => G.nat j h' h f u hf hp hn (x.1 j))
    have h1 : (pb l f m).comp (G.q h hn) = (G.q h' hn).comp (pb l u n) := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h0]
    exact LinearMap.congr_fun h1 a

end UpperTheory.Gal.KunnethLefschetz
