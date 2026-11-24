module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameRealUnitaryOrbitGramRigid
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

theorem _root_.GlobalTheory.T.unitFrame_real_unitary_orbit_gram_rigid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (G : Type) [Group G] (Gi : Subgroup G) (dict : G → Σ k, Frame (X k).Ψ r) (ar : ∀ k, G → (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (J : ∀ k, (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (x0 : ∀ k, Frame (X k).Ψ r), (∀ k τ, (J k τ).IsHermitian ∧ (J k τ).det ≠ 0) → (∀ k (u : (X k).Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ, (u τ)ᵀ * J k τ * (u τ).map (starRingEnd ℂ) = J k τ) → ∃ h ∈ Gi, ∀ τ, ar k h τ = u τ) → (∀ k, x0 k ∈ (X k).dom ∧ ∃ g, dict g = ⟨k, x0 k⟩) → (∀ g, ∀ h ∈ Gi, ∃ γ ∈ (X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ (rmul (dict g).2 fun τ => ((mat (x0 (dict g).1) τ)⁻¹ * ar (dict g).1 h τ * mat (x0 (dict g).1) τ : Matrix (Fin r) (Fin r) ℂ))⟩) → (∀ g, (dict g).2 ∈ (X (dict g).1).dom) → (∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) → (∀ k (τ : (X k).Ψ), ∃ t : ℝ, t ≠ 0 ∧ (X k).Gm.map τ.1 = (t : ℂ) • J k τ) ∧ ∀ g τ, gram τ.1 (X (dict g).1).Gm (mat (dict g).2 τ) = gram τ.1 (X (dict g).1).Gm (mat (x0 (dict g).1) τ) := by
  first | exact @GlobalTheory.PeterssonRigid.rigid | exact GlobalTheory.PeterssonRigid.rigid | (intros; apply GlobalTheory.PeterssonRigid.rigid <;> assumption)
