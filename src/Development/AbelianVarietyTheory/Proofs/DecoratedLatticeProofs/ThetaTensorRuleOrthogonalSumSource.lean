module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositiStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsSumUniformLimitProductSpanStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariableKeepsThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilTensorRuleScalarEqOneStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TensorSrc

theorem op_prod {X Y : Type} (L : Module.End ℂ (X → ℂ)) (M : Module.End ℂ (Y → ℂ)) (f : X → ℂ) (g : Y → ℂ) (u : X)
    (v : Y) : L (fun u' => M (fun v' => f u' * g v') v) u = L f u * M g v := by
  have h1 : ∀ u', M (fun v' => f u' * g v') v = M g v * f u' := by
    intro u'
    have : (fun v' => f u' * g v') = f u' • g := by funext v'; simp
    rw [this, map_smul]; simp [mul_comm]
  have h2 : (fun u' => M (fun v' => f u' * g v') v) = M g v • f := by
    funext u'; simp [h1]
  rw [h2, map_smul]; simp [mul_comm]

theorem tensorSource : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S A B : HSp D) (d : OrthDec S A B) (T : HSp D), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.TensorSource ψ d T := by
  intro D ψ hψ S A B d T
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T d
  have hb : ∀ fA fB u v, d.boxS T fA fB ((d.resS T).symm (u, v)) = fA u * fB v := by
    intro fA fB u v
    simp [OrthDec.boxS]
  refine ⟨h1, h2, h3, h4, GlobalTheory.T.thetaFunctions_sum_uniform_limit_product_span D ψ hψ S A B T d, ?_, ?_⟩
  · intro χA χB χT omS omA omB hS hA hB a b h fA fB hfA hfB
    funext x
    obtain ⟨⟨u, v⟩, rfl⟩ := (d.resS T).symm.surjective x
    rw [GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h _ (h1 fA fB hfA hfB) u v, hb]
    simp only [hb]
    exact op_prod _ _ fA fB u v
  · intro χA χB χT omS omA omB hS hA hB a b h f hf v
    refine ⟨?_, fun u => GlobalTheory.T.weilTensorRule_scalar_eq_one D ψ S A B T d χA χB χT omS omA omB hS hA hB a b h f hf u v⟩
    have := (h4 _ ((GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T d f hf).2 χB χT omB hB (b, h))).1 v
    simpa using this

end GlobalTheory.TensorSrc
