module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGap
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

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.tensor_weighted_bessel_gap : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (FI : κ → Mx k r → (Wq →L[ℂ] Wp)) (sI τ : κ → ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → (∀ I, (RI I).IsDS ε (muI I) ∧ Formalism.QuantumDeterminants.GapAtLeast ε (muI I) h) → GapOK k r h → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om') → (∀ I, IsBeL (RI I) D.z D.π D.μW D.μN (lI I) ∧ IsBeL (RI I) D.z' D.π' D.μW' D.μN (lI' I)) → IsCoef R l l' F s → (∀ I, ((¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) ∧ τ I = 0) ∨ (IsCoef (RI I) (lI I) (lI' I) (FI I) (sI I) ∧ sI I ≠ 0 ∧ ∃ κ₀ κ₁ : ℂ, (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) ∧ τ I = (ep I : ℂ) * κ₁ * star κ₀ * s / sI I)) → ∀ γ ∈ JF.Om k r D.z D.z', Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om • B.JF D F γ = ∑ I, τ I • B.JF D (FI I) γ := by
  first | exact @GlobalTheory.BesselPieri.pieri_bessel | exact GlobalTheory.BesselPieri.pieri_bessel | (intros; apply GlobalTheory.BesselPieri.pieri_bessel <;> assumption)
