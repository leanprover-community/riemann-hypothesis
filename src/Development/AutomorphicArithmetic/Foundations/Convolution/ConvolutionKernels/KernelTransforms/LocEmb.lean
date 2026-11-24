module

public import GroundTheory.AutomorphicForms.StrongApproximationSLDense
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

open scoped RestrictedProduct in
private theorem cont_mulSingle {ι : Type} [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (A : ∀ i, Subgroup (G i)) (v : ι) : Continuous (RestrictedProduct.mulSingle A v) := by
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set ι) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let g : G v → Πʳ i, [G i, A i]_[Filter.principal ({v}ᶜ : Set ι)] := fun x =>
    ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro i hi
      rw [Pi.mulSingle_eq_of_ne hi]
      exact one_mem _⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem UpperTheory.ConvolutionTheory.Tf.locEmb :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
      Continuous (AdelicGLn.localEmbedding (K := K) (n := n) v) ∧
      (∀ x, finAt v (finEmb K n (AdelicGLn.localEmbedding v x)) = x) ∧
      (∀ w, w ≠ v → ∀ x, finAt w (finEmb K n (AdelicGLn.localEmbedding v x)) = 1) ∧
      (∀ w, w ≠ v → ∀ x y, AdelicGLn.localEmbedding (K := K) (n := n) v x * AdelicGLn.localEmbedding w y =
        AdelicGLn.localEmbedding w y * AdelicGLn.localEmbedding v x) ∧
      ∀ (h : AdelicGLn.FiniteAdelicGL K n), finAt v (finEmb K n h) = 1 → ∀ x,
        AdelicGLn.localEmbedding v x * h = h * AdelicGLn.localEmbedding v x := by
  classical
  intro K _ _ n v
  have e : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : AdelicGLn.FiniteAdelicGL K n),
      finAt w (finEmb K n y) = AdelicGLn.finiteRestrictedEquiv K n y w := fun w y => rfl
  have a : ∀ (u w : HeightOneSpectrum (𝓞 K)) x, AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.localEmbedding u x) w =
      Pi.mulSingle (M := fun t : HeightOneSpectrum (𝓞 K) => GL (Fin n) (t.adicCompletion K)) u x w := by
    intro u w x
    change AdelicGLn.finiteRestrictedEquiv K n ((AdelicGLn.finiteRestrictedEquiv K n).symm _) w = _
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact RestrictedProduct.coe_mulSingle_apply _ _ _ _
  have c : ∀ (h : AdelicGLn.FiniteAdelicGL K n), finAt v (finEmb K n h) = 1 → ∀ x,
        AdelicGLn.localEmbedding v x * h = h * AdelicGLn.localEmbedding v x := by
    intro h hh x
    apply (AdelicGLn.finiteRestrictedEquiv K n).injective
    refine DFunLike.ext _ _ fun w => ?_
    rw [map_mul, map_mul, RestrictedProduct.mul_apply, RestrictedProduct.mul_apply, a]
    by_cases hw : w = v
    · subst hw
      rw [← e, hh, mul_one, one_mul]
    · rw [Pi.mulSingle_eq_of_ne hw, mul_one, one_mul]
  refine ⟨(AdelicGLn.finiteRestrictedEquiv K n).symm.continuous.comp (cont_mulSingle _ v), fun x => ?_,
    fun w hw x => ?_, fun w hw x y => c _ ?_ x, c⟩
  · rw [e, a, Pi.mulSingle_eq_same]
  · rw [e, a, Pi.mulSingle_eq_of_ne hw]
  · rw [e, a, Pi.mulSingle_eq_of_ne hw.symm]
