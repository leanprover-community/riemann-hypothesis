module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeightTraceProducts.ThFacts
import Mathlib.Algebra.MvPolynomial.Funext
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

open Polynomial UpperTheory.V.Z.Sym.Wt

private theorem swp_eval {I : Type} [Fintype I] {d : ℕ} (n : I → ℕ) (Q : Bi d n) (x : (I × Bool) × Fin d → ℂ) :
    MvPolynomial.eval x (swp d n Q).1 = MvPolynomial.eval (x ∘ UpperTheory.V.Z.Sym.Wt.flip I d) Q.1 := MvPolynomial.eval_rename _ _ _

theorem UpperTheory.V.Z.Sym.Wt.thFacts :
    UpperTheory.V.Z.Sym.Wt.ThFacts := by
  intro I _ j
  have key : ∀ (n : I → ℕ) (g : I → GL (Fin 3) ℂ) (P : Bi 3 n),
      swp 3 n (biRep 3 n g P) = biRep 3 n (fun v => invT ℂ 3 (g v)) (swp 3 n P) := by
    intro n g P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval]
    change MvPolynomial.eval _ ((mRep 3 (fun k => n k.1) (dbl 3 g)) P).1 =
      MvPolynomial.eval x ((mRep 3 (fun k => n k.1) (dbl 3 (fun v => invT ℂ 3 (g v)))) (swp 3 n P)).1
    rw [eval_mRep, eval_mRep, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    obtain ⟨⟨v, b⟩, i⟩ := p
    cases b <;> simp [act, UpperTheory.V.Z.Sym.Wt.flip, dbl, invT_invT]
  have hswp : ∀ (n : I → ℕ) (P : Bi 3 n), swp 3 n (swp 3 n P) = P := by
    intro n P
    apply Subtype.ext
    apply MvPolynomial.funext
    intro x
    rw [swp_eval, swp_eval]
    refine congrArg (fun y => MvPolynomial.eval y P.1) ?_
    funext p
    simp [UpperTheory.V.Z.Sym.Wt.flip]
  have hsg : ∀ S : I → Bool, sg S * sg S = 1 := by
    intro S
    simp only [sg, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro v _
    split_ifs <;> norm_num
  refine ⟨?_, ?_⟩
  · apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, map_smul, smul_smul, hswp, hsg, one_smul, Module.End.one_apply]
  · intro g
    apply LinearMap.ext
    intro P
    funext S
    simp only [Module.End.mul_apply, thG_apply, repG_apply, map_smul, key]
