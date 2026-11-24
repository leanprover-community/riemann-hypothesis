module

public import Formalism.LocalToGlobal.ThetaOperatorCommutation.RealTh
public import ReciprocityTheory.ThetaSummability.RealCoinvariants.Numbers
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.FockAct1FockAct2Commute
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

@[expose] public section

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action

namespace PositivityTheory.KReal

abbrev ThV (D : RealData) : Type := ThC D.P D.Q D.R D.S ((D.κ : ℂ) / 2)

abbrev ThV' (D : RealData) : Type := ThC D.P' D.Q' D.R D.S (-((D.κ : ℂ) / 2))

def opV (D : RealData) (W : Mat D.R D.S) : Module.End ℂ (ThV D) :=
  ReciprocityTheory.ThetaSummability.Real.coinvOp (chiTr ((D.κ : ℂ) / 2)) (fockAct2 _ _ _ _ W) fun Z => (fockAct1_fockAct2_commute Z W).symm

def opV' (D : RealData) (W : Mat D.R D.S) : Module.End ℂ (ThV' D) :=
  ReciprocityTheory.ThetaSummability.Real.coinvOp (chiTr (-((D.κ : ℂ) / 2))) (fockAct2 _ _ _ _ W) (fun Z => (fockAct1_fockAct2_commute Z W).symm) +
    ((D.κ : ℂ) / 2 * W.trace) • 1

def CoreLM : Prop :=
  ∀ D : RealData, D.Hyp → ∃ (Pi : Type) (_ : AddCommGroup Pi) (_ : Module ℂ Pi) (act : Mat D.R D.S → Module.End ℂ Pi)
    (π : ThV D →ₗ[ℂ] Pi) (π' : ThV' D →ₗ[ℂ] Pi), Function.Surjective π ∧ Function.Surjective π' ∧
    (∀ W x, π (opV D W x) = act W (π x)) ∧ (∀ W x, π' (opV' D W x) = act W (π' x)) ∧ Nontrivial Pi ∧
    ∀ N : Submodule ℂ Pi, (∀ W, ∀ x ∈ N, act W x ∈ N) → N = ⊥ ∨ N = ⊤

def TensorIrr : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : ι → Type) (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)] (act : ∀ i, A i → Module.End ℂ (M i)),
    (∀ i, Module.rank ℂ (M i) ≤ Cardinal.aleph0) → (∀ i, Nontrivial (M i)) →
    (∀ i, ∀ N : Submodule ℂ (M i), (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ N : Submodule ℂ (PiTensorProduct ℂ M),
      (∀ i a, ∀ x ∈ N, PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i (act i a)) x ∈ N) →
      N = ⊥ ∨ N = ⊤

end PositivityTheory.KReal

end
