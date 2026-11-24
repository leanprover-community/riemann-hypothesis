module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import GroundTheory.AutomorphicForms.MeasuresModulus
import GroundTheory.AutomorphicForms.SmoothRepSchur
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology

namespace GlobalTheory.CompanionTheory.SocleFrob

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_smul_id {n : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ (GL (Fin n) k) X) (hs : IsSmooth ρ) (hi : ρ.IsIrreducible)
    (φ : X →ₗ[ℂ] X) (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : ∃ c : ℂ, φ = c • LinearMap.id := by
  haveI : ρ.IsIrreducible := hi
  have hs' : GroundTheory.Automorphic.IsSmooth ρ := hs
  obtain ⟨c, hc⟩ := (GroundTheory.Automorphic.algebraMap_intertwiningMap_bijective_of_isSmooth hs').2
    (⟨φ, fun g => LinearMap.ext fun x => hφ g x⟩ : Representation.IntertwiningMap ρ ρ)
  refine ⟨c, LinearMap.ext fun x => ?_⟩
  exact (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hc).symm

theorem isIrreducible_piTensor {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    exists_eq_smul_id _ (x a).2.rep.smooth (x a).2.rep.irr φ hφ

theorem jm_ne_zero_of_isSocle : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (h N : ℕ) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    (∀ a, 0 < (x a).1) → IsSocle π (prodIrr x hd) → Zc.jm x hd π ≠ 0 := by
  intro k _ _ _ _ h N x hd V _ _ π _ _ hS
  obtain ⟨hi, f, hf, -⟩ := hS
  haveI : Nontrivial V := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : 1 ≤ Zc.jm x hd π :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac (stdBlocks (fun a => (x a).1) hd) (isIrreducible_piTensor x) f
      ⟨v, fun h0 => hv (hf (h0.trans (map_zero f).symm))⟩
  exact ENat.one_le_iff_ne_zero.1 h1

end GlobalTheory.CompanionTheory.SocleFrob

end
