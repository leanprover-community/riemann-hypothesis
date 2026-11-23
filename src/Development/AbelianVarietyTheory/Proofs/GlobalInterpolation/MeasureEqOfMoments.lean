module

public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMahlerExpansion
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomN

theorem measure_eq_of_moments : ∀ (q : ℕ) [Fact q.Prime] (κ : Type) [Fintype κ]
    (μ μ' : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]),
    (∀ (k : ℕ) (j : Fin k → κ) (f : C(κ → ℤ_[q], ℂ_[q])),
      (∀ a, f a = ∏ l, zc (a (j l))) → μ f = μ' f) → μ = μ' := by
  intro q _ κ _ μ μ' h
  let e := Fintype.equivFin κ
  let π : C(κ → ℤ_[q], Fin (Fintype.card κ) → ℤ_[q]) :=
    ⟨fun b i => b (e.symm i), by fun_prop⟩
  let π' : C(Fin (Fintype.card κ) → ℤ_[q], κ → ℤ_[q]) :=
    ⟨fun a i => a (e i), by fun_prop⟩
  let Φ : C(Fin (Fintype.card κ) → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] C(κ → ℤ_[q], ℂ_[q]) :=
    { toFun := fun G => G.comp π
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp π }
  have hz : (μ - μ').comp Φ = 0 := by
    exact GlobalTheory.MonomialDense.eq_zero_of_monomials q _ _ fun m k g hg => by
      have := h m (fun l => e.symm (k l)) (Φ g) fun b => hg (π b)
      simp [this]
  ext F
  have hF : Φ (F.comp π') = F := by
    ext b
    change F (π' (π b)) = F b
    congr 1
    funext i
    simp [π, π']
  have := congrArg (fun ν => ν (F.comp π')) hz
  simp only [ContinuousLinearMap.comp_apply, hF, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.MomN
