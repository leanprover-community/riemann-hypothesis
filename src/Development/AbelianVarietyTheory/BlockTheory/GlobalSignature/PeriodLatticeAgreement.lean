module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement

open Formalism.MainNotions.TaylorLogMetric
open scoped UpperHalfPlane

def latt (ω₁ τ : ℂ) : AddSubgroup ℂ where
  carrier := {w | ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ)}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    exact ⟨m + m', n + n', by push_cast; ring⟩
  neg_mem' := by
    rintro _ ⟨m, n, rfl⟩
    exact ⟨-m, -n, by push_cast; ring⟩

def scale (c : ℂ) (Λ : AddSubgroup ℂ) : AddSubgroup ℂ := Λ.map (AddMonoidHom.mulLeft c)

def period (Λ : AddSubgroup ℂ) : ℝ := ‖discr Λ‖ ^ ((1 : ℝ) / 6) * area Λ / Real.pi

def DiscrEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    discr (latt ω₁ τ) = (2 * (Real.pi : ℂ) / ω₁) ^ 12 * ModularForm.eta (τ : ℂ) ^ 24

def AreaEq : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 → area (latt ω₁ τ) = ‖ω₁‖ ^ 2 * τ.im

def PeriodEta : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ), ω₁ ≠ 0 →
    period (latt ω₁ τ) = 4 * Real.pi * τ.im * ‖ModularForm.eta (τ : ℂ)‖ ^ 4

def DiscrScale : Prop :=
  ∀ (ω₁ : ℂ) (τ : ℍ) (c : ℂ), ω₁ ≠ 0 → c ≠ 0 →
    discr (scale c (latt ω₁ τ)) = c ^ (-12 : ℤ) * discr (latt ω₁ τ)

def AgreePeriodPair : Prop :=
  ∀ L : PeriodPair,
    (∀ k : ℕ, 2 ≤ k →
      Summable (fun w : {w : ℂ // w ∈ L.lattice.toAddSubgroup ∧ w ≠ 0} => 1 / (w : ℂ) ^ (2 * k)) ∧
      eisG L.lattice.toAddSubgroup k = L.G (2 * k)) ∧
    g2 L.lattice.toAddSubgroup = L.g₂ ∧ g3 L.lattice.toAddSubgroup = L.g₃

def LatticePeriodEta : Prop :=
  DiscrEta ∧ AreaEq ∧ PeriodEta ∧ DiscrScale ∧ AgreePeriodPair

theorem mem_latt {ω₁ τ w : ℂ} : w ∈ latt ω₁ τ ↔ ∃ m n : ℤ, w = ω₁ * ((m : ℂ) + (n : ℂ) * τ) := Iff.rfl

theorem mem_scale {c w : ℂ} {Λ : AddSubgroup ℂ} : w ∈ scale c Λ ↔ ∃ v ∈ Λ, c * v = w := by
  simp [scale, AddSubgroup.mem_map]

theorem scale_latt (c ω₁ τ : ℂ) : scale c (latt ω₁ τ) = latt (c * ω₁) τ := by
  ext w
  rw [mem_scale, mem_latt]
  constructor
  · rintro ⟨_, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, ⟨m, n, rfl⟩, by ring⟩

end GlobalTheory.IndefiniteRowSideFullHecke.PeriodLatticeAgreement
