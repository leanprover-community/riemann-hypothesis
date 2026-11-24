module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsInvDer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)

noncomputable section
namespace GlobalTheory.KS

theorem isCob_of_mixed : ∀ (X : Scheme.{0}) (J K : Type) (V : J → X.Opens) (U : K → X.Opens), ⨆ k, U k = ⊤ → ∀ (z : C1 V) (z' : C1 U) (b : ∀ i k, Γ(X, V i ⊓ U k)), (∀ i i' k, rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (b i k) (V i ⊓ V i' ⊓ U k) - rsT (b i' k) (V i ⊓ V i' ⊓ U k)) → (∀ i k k', rsT (z' k k') (V i ⊓ U k ⊓ U k') = rsT (b i k') (V i ⊓ U k ⊓ U k') - rsT (b i k) (V i ⊓ U k ⊓ U k')) → IsCob U z' → IsCob V z := by
  intro X J K V U hU z z' b h1 h2 hz'
  obtain ⟨y', hy'⟩ := hz'
  have cov : ∀ O : X.Opens, O ≤ ⨆ k, O ⊓ U k := fun O x hx => by
    have : x ∈ ⨆ k, U k := by rw [hU]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  have glue : ∀ i, ∃ t : Γ(X, V i), ∀ k, rsT t (V i ⊓ U k) = rsT (y' k) (V i ⊓ U k) - b i k := by
    intro i
    refine exists_rsT_eq (fun k => V i ⊓ U k) (fun k => inf_le_left) (cov _) _ fun k l => ?_
    have e : (V i ⊓ U k) ⊓ (V i ⊓ U l) ≤ V i ⊓ U k ⊓ U l := fun x hx => ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩
    have e₁ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U k := inf_le_left
    have e₂ : V i ⊓ U k ⊓ U l ≤ V i ⊓ U l := fun x hx => ⟨hx.1.1, hx.2⟩
    have e₃ : V i ⊓ U k ⊓ U l ≤ U k ⊓ U l := fun x hx => ⟨hx.1.2, hx.2⟩
    rw [← rsT_rsT e₁ e, ← rsT_rsT e₂ e]
    congr 1
    have k₀ := congrArg (fun s => rsT s (V i ⊓ U k ⊓ U l)) (hy' k l)
    simp only [rsT_sub] at k₀
    rw [h2, rsT_rsT inf_le_right e₃, rsT_rsT inf_le_left e₃] at k₀
    simp only [rsT_sub]
    rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
    linear_combination k₀
  choose y hy using glue
  refine ⟨y, fun i i' => ?_⟩
  refine eq_of_rsT_eq (fun k => V i ⊓ V i' ⊓ U k) (fun k => inf_le_left) (cov _) _ _ fun k => ?_
  have e₁ : V i ⊓ V i' ⊓ U k ≤ V i ⊓ U k := fun x hx => ⟨hx.1.1, hx.2⟩
  have e₂ : V i ⊓ V i' ⊓ U k ≤ V i' ⊓ U k := fun x hx => ⟨hx.1.2, hx.2⟩
  show rsT (z i i') (V i ⊓ V i' ⊓ U k) = rsT (rsT (y i') (V i ⊓ V i') - rsT (y i) (V i ⊓ V i')) (V i ⊓ V i' ⊓ U k)
  rw [h1, rsT_sub, rsT_rsT inf_le_right inf_le_left, rsT_rsT inf_le_left inf_le_left,
    ← rsT_rsT inf_le_left e₂ (y i'), ← rsT_rsT inf_le_left e₁ (y i), hy, hy]
  simp only [rsT_sub]
  rw [rsT_rsT inf_le_right e₁, rsT_rsT inf_le_right e₂]
  ring

end GlobalTheory.KS
end
