module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.IsUnitALMap
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClassesFrames
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfClasses
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormBoundOfTorsionCharacter
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Linter.Style
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

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms

theorem chiTors : ChiTors := by
  intro D u Ch chOf Tf c
  classical
  let P : ℂ → Prop := fun z => ∃ k : ℕ, 0 < k ∧ z ^ k = 1
  have h1 : P 1 := ⟨1, one_pos, one_pow _⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨k, hk, hx⟩ ⟨l, hl, hy⟩
    refine ⟨k * l, Nat.mul_pos hk hl, ?_⟩
    rw [mul_pow, pow_mul, hx, one_pow, one_mul, mul_comm k l, pow_mul, hy, one_pow]
  have hfac : ∀ a v h, P (((Tf.lamM a v h ((Tf.glevM).red a v h (Tf.tilAd.ka c)) : ℂˣ) : ℂ))⁻¹ := by
    intro a v h
    haveI : Finite (Formalism.L2.Forms.kv D.host.F v) := Formalism.UG.P.glint_finite_residueField v
    refine ⟨orderOf ((Tf.glevM).red a v h (Tf.tilAd.ka c)), orderOf_pos _, ?_⟩
    rw [inv_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one, inv_one]
  show P _
  rw [(Tf.glevM).chi_eq]
  refine Finset.prod_induction _ P hmul h1 fun a _ => ?_
  refine finprod_induction P h1 hmul fun v => ?_
  exact finprod_induction P h1 hmul fun h => hfac a v h

theorem normClsAt_holds : NormClsAt := normClsAt_of_tors chiTors

theorem norm_bound_of_injective_stable (h1 : ClassMapInjective) (h2 : StabiliserMapBijective) : NormBoundAtInfinity :=
  norm_bound_of_classes h1 h2 normClsAt_holds

end Formalism.L2.GlobalTheoryTheory.Br
