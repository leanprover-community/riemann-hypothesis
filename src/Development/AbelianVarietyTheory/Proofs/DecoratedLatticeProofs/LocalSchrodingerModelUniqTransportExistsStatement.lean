module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSchrodingerModelUniqTransportExists
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.localSchrodingerModel_uniq_transport_exists : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ T₁ T₂, p.IsModel ψ FS FT T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₀, Φ₀ ≠ 0 → T₁ Φ₀ = T₂ Φ₀ → T₁ = T₂) ∧ (∀ T₁, p.IsModel ψ FS FT T₁ → ∀ A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (A f)) → (∀ f, IsThetaFunO ψ S T f → ∀ y : WO S T, IsHalf (p.e + cA D p.e) y → A (heisO ψ S T y f) = heisO ψ S T y (A f)) → p.IsModel ψ FS FT (A ∘ₗ T₁)) ∧ ∀ f₀, IsThetaFunO ψ S T f₀ → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → heisO ψ S T (p.up FS FT x) f₀ = f₀) → (∀ y : WO S T, IsHalf (cA D p.e) y → (∀ x : Matrix Y Y' k, (∀ r q, x r q ∈ 𝒪[k]) → ψ (symplO S T (p.up FS FT x) y) = 1) → heisO ψ S T y f₀ = f₀) → ∃ T₁, p.IsModel ψ FS FT T₁ ∧ ∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → T₁ Φ = f₀ := by
  first | exact @GlobalTheory.LocModU.localModel_uniq_transport_exist | exact GlobalTheory.LocModU.localModel_uniq_transport_exist | (intros; apply GlobalTheory.LocModU.localModel_uniq_transport_exist <;> assumption)
