module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.Corev.ThCLin

open Formalism.L2.Ker Formalism.L2.Th1.H

theorem hatS_mul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (vol : ℝ) (SA : Finset V)
    (Φ : V → ℂ) (p : ℂ) (y : V) :
    hatS H vol SA (fun s => p * Φ s) y = p * hatS H vol SA Φ y := by
  simp only [hatS, mul_assoc, ← Finset.mul_sum]
  ring

theorem thC_smul_move : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (p : ℂ) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : Formalism.L2.Ker.VV ι a b → ℂ), Formalism.L2.Ker.thC emb δ d sc AA SS N N' c (fun x => p * Ξ x) θ = Formalism.L2.Ker.thC emb δ d sc AA SS N N' c Ξ (fun z => p * θ z) := by
  intro E _ _ _ ι _ a b emb δ d sc AA SS N N' c p Ξ θ
  have hon : onV emb δ (fun x => p * Ξ x) = fun v => p * onV emb δ Ξ v := by
    funext v
    unfold onV
    split_ifs <;> simp
  funext z
  simp only [thC, xiV, xiL, xiS, hon, hatS_mul_left, sumU, opU]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

end GlobalTheory.Corev.ThCLin
