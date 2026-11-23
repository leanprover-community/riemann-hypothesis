module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormAevalSubLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
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

noncomputable section

namespace GlobalTheory.Cong

variable {k : Type} [NormedField k]

def PolyApprox [IsUltrametricDist k] {J : Type} (θ : J → k) (S : Set (J → k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (J → k)) (c : (J → k) → k), (s : Set (J → k)) ⊆ S ∧
    ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval θ P - ∑ η ∈ s, c η * MvPolynomial.aeval η P‖ ≤ ε

def trc {Γ A : Type} [Group Γ] [CommRing A] {a : ℕ} (r : Γ →* GL (Fin a) A) (g : Γ) : A :=
  ((r g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).trace

def LinApprox {Γ : Type} [Group Γ] {a : ℕ} (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (s : Finset (Γ →* GL (Fin a) k)) (c : (Γ →* GL (Fin a) k) → k), (s : Set (Γ →* GL (Fin a) k)) ⊆ C ∧
    ∀ g : Γ, ‖trc r g - ∑ ρ ∈ s, c ρ * trc ρ g‖ ≤ ε

def opOf {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) (v : V) : V :=
  f.sum fun g c => c • ρ g v

theorem PolyApprox.mono [IsUltrametricDist k] {J : Type} {θ : J → k} {S T : Set (J → k)} (h : PolyApprox θ S)
    (hST : S ⊆ T) : PolyApprox θ T := fun ε hε => by
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  exact ⟨s, c, hs.trans hST, hP⟩

variable [NormOneClass k] [IsUltrametricDist k]

theorem aeval_sub_le {J : Type} {x y : J → k} {δ : ℝ} (hδ : 0 ≤ δ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1)
    (hxy : ∀ j, ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖MvPolynomial.aeval x P‖ ≤ 1 ∧ ‖MvPolynomial.aeval y P‖ ≤ 1 ∧
      ‖MvPolynomial.aeval x P - MvPolynomial.aeval y P‖ ≤ δ := by
  first
  | exact @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le
  | (apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormAevalSubBound.norm_aeval_sub_le ..)

end GlobalTheory.Cong

end
