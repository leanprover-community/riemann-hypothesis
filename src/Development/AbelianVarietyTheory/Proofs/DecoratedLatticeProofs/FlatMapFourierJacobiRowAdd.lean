module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingAffPtUncurry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section
namespace GlobalTheory.LocFlat

theorem add_right_mem_SB {m m' k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
    {Φ : Matrix m m' k → ℂ} (hΦ : Φ ∈ SB (Matrix m m' k)) (a : Matrix m m' k) :
    (fun z => Φ (z + a)) ∈ SB (Matrix m m' k) :=
  ⟨hΦ.1.comp_continuous (continuous_add_const a), hΦ.2.comp_homeomorph (Homeomorph.addRight a)⟩

theorem flRow_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (Φ₁ Φ₂ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ₁ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → Φ₂ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) → GlobalTheory.LocFlat.flRow ψ ν p (Φ₁ + Φ₂) = GlobalTheory.LocFlat.flRow ψ ν p Φ₁ + GlobalTheory.LocFlat.flRow ψ ν p Φ₂ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p Φ₁ Φ₂ h₁ h₂
  funext x
  have H := opE_smul_add p hψ ν (1 : ℂ)
    (add_right_mem_SB h₁ (rowAt n c p (x (Sum.inr ()))))
    (add_right_mem_SB h₂ (rowAt n c p (x (Sum.inr ()))))
  have H' := congrFun H x.toRows₁
  simp only [one_smul, Pi.add_apply] at H'
  simp only [flRow, Pi.add_apply]
  rw [← H']
  rfl

end GlobalTheory.LocFlat
