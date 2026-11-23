module

public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.HasseEt
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.RootMapRoot
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open Matrix Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

private theorem root_isUnit {F : Type} [Field F] (p : F[X]) (h : p.coeff 0 ≠ 0) :
    IsUnit (AdjoinRoot.root p) := by
  have h1 : AdjoinRoot.mk p (X * p.divX + C (p.coeff 0)) = 0 := by
    rw [X_mul_divX_add, AdjoinRoot.mk_self]
  rw [map_add (f := _), map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_eq_zero_iff_eq_neg] at h1
  exact isUnit_of_mul_isUnit_left (h1 ▸ ((Ne.isUnit h).map (AdjoinRoot.of p)).neg)

private theorem root_reduced {F : Type} [Field F] (p : F[X]) (h : p.Separable) :
    IsReduced (AdjoinRoot p) :=
  (Ideal.isRadical_iff_quotient_reduced _).1
    (isRadical_iff_span_singleton.1 h.squarefree.isRadical)

theorem UpperTheory.ConvolutionTheory.D.nmHasse :
    UpperTheory.ConvolutionTheory.D.NmHasse := by
  intro F E _ _ _ _ _ _ σ hσ n γ hγ hf hi
  have hG := galField F E σ hσ
  haveI : IsCyclic (E ≃ₐ[F] E) := ⟨⟨σ, hσ⟩⟩
  haveI := root_reduced _ hγ
  haveI : Module.Finite F (AdjoinRoot (cp γ)) := (Matrix.charpoly_monic _).finite_adjoinRoot
  have hu : IsUnit (AdjoinRoot.root (cp γ)) := by
    refine root_isUnit _ fun h0 => ?_
    have h1 := Matrix.det_eq_sign_charpoly_coeff γ.val
    rw [cp] at h0
    rw [h0, mul_zero] at h1
    exact ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero h1
  refine (nmAlg F E F σ _ hG n γ hγ).2.2 (hasseEt F E _ hu.unit (fun v => ?_) fun v => ?_)
  · exact (nmAlg F E _ σ _ hG n γ hγ).1.1 (hf v)
  · exact (nmAlg F E _ σ _ hG n γ hγ).1.1 (hi v)
