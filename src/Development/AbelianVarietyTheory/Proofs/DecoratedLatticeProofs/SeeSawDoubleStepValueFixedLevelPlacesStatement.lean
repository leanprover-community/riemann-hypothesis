module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlaces
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.SeeSaw.GValMid.gValue_mid | exact GlobalTheory.SeeSaw.GValMid.gValue_mid | (intros; apply GlobalTheory.SeeSaw.GValMid.gValue_mid <;> assumption)
