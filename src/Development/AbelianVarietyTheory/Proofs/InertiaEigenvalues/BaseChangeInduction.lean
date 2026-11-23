module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
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

namespace GlobalTheory.BaseChangeInduction

theorem baseChange_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : GlobalTheory.Prism.SemiBC u)
    (p : N → Prop) (hzero : p 0) (hadd : ∀ y z, p y → p z → p (y + z))
    (hsmul : ∀ (r : B) (y : N), p y → p (r • y)) (himg : ∀ x : M, p (u x)) (y : N) : p y := by
  let S : Submodule B N :=
    { carrier := {n | p n}
      zero_mem' := hzero
      add_mem' := fun {a b} ha hb => hadd a b ha hb
      smul_mem' := fun r n hn => hsmul r n hn }
  have hq : S.mkQ = 0 := by
    refine (h (N ⧸ S) 0).unique (fun x => ?_) (fun x => rfl)
    exact (Submodule.Quotient.mk_eq_zero S).2 (himg x)
  have hy : S.mkQ y = 0 := by rw [hq]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 hy

end GlobalTheory.BaseChangeInduction
