module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTjCosetsFiniteCardLe
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ConjInv

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.lie_action_preserves_satake_eigen_at_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (w : H.P E) (B : Multiset ℂˣ) (f : Sm E 2) (X : Lie E 2), UpperTheory.V.Af.Smo.EigAt w B f.1 → UpperTheory.V.Af.Smo.EigAt w B (lie E 2 X f).1 := by
  intro E _ _ _ w B f X hf g
  have hc : ∀ (k : GL (Fin 2) (Af E)) (φ : Sm E 2) (x : GA E 2),
      (lie E 2 X φ).1 (x * finGL E 2 k) = (lie E 2 X (GlobalTheory.CuspRep.rt E 2 (finGL E 2 k) φ)).1 x := by
    intro k φ x
    have h := LinearMap.congr_fun (lie_rt_fin X k) φ
    exact (congrArg (fun ψ : Sm E 2 => ψ.1 x) h).symm
  have hev : ∀ (k : GA E 2) (φ : Sm E 2) (x : GA E 2), (GlobalTheory.CuspRep.rt E 2 k φ).1 x = φ.1 (x * k) :=
    fun _ _ _ => rfl
  refine ⟨(hf 1).card, ?_, ?_⟩
  · intro y k hk
    have hfix : GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w k)) f = f := by
      refine Subtype.ext (funext fun x => ?_)
      have h := (hf x).inv 1 k hk
      simp only [one_mul, map_one, mul_one] at h
      rw [hev]
      exact h
    have e1 : g * finGL E 2 (locGL E 2 w (y * k)) =
        g * finGL E 2 (locGL E 2 w y) * finGL E 2 (locGL E 2 w k) := by
      simp only [map_mul, mul_assoc]
    show (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (y * k))) = (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w y))
    rw [e1, hc, hfix]
  · intro ϖ hϖ j hj x
    have hfin := (GlobalTheory.TjCount.tj_cosets_finite_card_le E w 2 ϖ hϖ j hj).1
    have hsum : ∀ W : GL (Fin 2) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := 2) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c =
          ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out * W c := by
      intro W
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      rw [Set.Finite.coe_toFinset]
      exact fun h0 => hc' (by simp [h0])
    have key : ∑ c ∈ hfin.toFinset, Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out •
          GlobalTheory.CuspRep.rt E 2 (finGL E 2 (locGL E 2 w c.out)) f =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 B j • f := by
      refine Subtype.ext (funext fun z => ?_)
      have h := (hf z).eig ϖ hϖ j hj 1
      simp only [one_mul, map_one, mul_one] at h
      rw [hsum fun c => f.1 (z * finGL E 2 (locGL E 2 w c.out))] at h
      simpa [Submodule.coe_sum, Finset.sum_apply, hev] using h
    have h2 := congrArg (fun ψ : Sm E 2 => (lie E 2 X ψ).1 (g * finGL E 2 (locGL E 2 w x))) key

    simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul] at h2
    rw [hsum fun c => (lie E 2 X f).1 (g * finGL E 2 (locGL E 2 w (x * c.out)))]
    rw [← h2]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_mul, ← mul_assoc, hc]
