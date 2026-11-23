module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockProjectionBessel
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.block_projection_bessel : Hyps → AmpKF → CellConv → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (L : LocBessel k r) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (μG : Measure (Mt k r)) (om om' : ι → ℂ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (lI : ∀ I, (RI I).H → L.Wp) (lI' : ∀ I, (RI I).H → L.Wq) (w : R.H) (wI : ∀ I, (RI I).H) (κ₀ κ₁ : κ → ℂ), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → (∀ I, (RI I).IsDS L.ε (muI I) ∧ GapAtLeast L.ε (muI I) h) → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → L.c ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Sset k r L.z, ρ g *ᵥ om = om) → (∀ g ∈ Sset k r L.z', ρ g *ᵥ om' = om') → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∀ I, (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π (RI I).σ L.μW L.μN x v = (innerSL ℂ (lI I v)).smulRight (lI I x)) ∧ (∀ x ∈ (RI I).sm, ∀ v ∈ (RI I).TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' (RI I).σ L.μW' L.μN x v = (innerSL ℂ (lI' I v)).smulRight (lI' I x))) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → (∀ I, PI.UpqRep.IsLowUnitH k r L.ε (muI I) (RI I).σ (wI I)) → (∀ I, ∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ I • l v ∧ lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ I • l' v) → ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r)) (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν → (herm Γ (ρ γ *ᵥ om') om * (PI.BesselPeriodGGP.fdegH μG R.σ w : ℂ)) • amp R l l' w νR γ = ∑ I, ((ep I : ℂ) * κ₁ I * star (κ₀ I) * (PI.BesselPeriodGGP.fdegH μG (RI I).σ (wI I) : ℂ)) • amp (RI I) (lI I) (lI' I) (wI I) νR γ := by
  exact @GlobalTheory.CellPieri.amp_pieri
