module

public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresDoubleCosetAdjointCommute
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

@[expose] public section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

theorem _root_.GlobalTheory.T.classPres_doubleCoset_adjoint_commute : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (L : Subgroup G) (x : G) (A A' B : Finset G) (T T' U : Module.End K S.Forms), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((T' f : S.Forms) : S.Cl → S.V) = dcOp A' (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((U f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) → (∀ f g : S.Forms, S.csum ((T f : S.Forms) : S.Cl → S.V) (g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) ((T' g : S.Forms) : S.Cl → S.V)) ∧ ((∀ F ∈ AdForms ι ρ J χ, dcOp A (dcOp B F) = dcOp B (dcOp A F)) → Commute T U) := by
  first | exact @GlobalTheory.classPres_dcOp_adjoint_commute | exact GlobalTheory.classPres_dcOp_adjoint_commute | (intros; apply GlobalTheory.classPres_dcOp_adjoint_commute <;> assumption)
