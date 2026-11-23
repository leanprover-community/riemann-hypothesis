module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFrameCol
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KappaModel

theorem finv_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψk : AddChar k Circle) (ν : Measure k), Continuous ψk → ψk ≠ 1 → ν.IsAddHaarMeasure → ∀ (C : ℂ) (Φ : Matrix Unit n k → ℂ), Φ ∈ SB (Matrix Unit n k) → GlobalTheory.KappaModel.finv ψk ν C Φ ∈ SB (Matrix n Unit k) := by
  intro k _ _ _ _ _ _ n _ _ ψk ν hψ hne hν C Φ hΦ
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (GlobalTheory.SplitWeil.conductor_exists k).1 ψk hψ hne
  let e : (n → k) ≃ₜ Matrix Unit n k :=
    { toFun := fun η => Matrix.of fun _ r => η r
      invFun := fun M => M ()
      left_inv := fun _ => rfl
      right_inv := fun M => by ext i j; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e' : Matrix n Unit k ≃ₜ (n → k) :=
    { toFun := fun x r => x r ()
      invFun := fun y => Matrix.of fun r _ => y r
      left_inv := fun M => by ext i j; rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hf : (fun η : n → k => Φ (Matrix.of fun _ r => η r)) ∈ SB (n → k) :=
    ⟨hΦ.1.comp_continuous e.continuous, hΦ.2.comp_homeomorph e⟩
  have hF := FourierPi.fourier_mem_SB (Measure.pi fun _ : n => ν) hc hf
  have eq : finv ψk ν C Φ = fun x => C * (fun y : n → k => ∫ η, Φ (Matrix.of fun _ r => η r) * (ψk (η ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ : n => ν)) (e' x) := by
    funext x; rfl
  rw [eq]
  refine ⟨?_, ?_⟩
  · exact (hF.1.comp_continuous e'.continuous).comp (fun z => C * z)
  · exact (hF.2.comp_homeomorph e').mul_left

end GlobalTheory.KappaModel
