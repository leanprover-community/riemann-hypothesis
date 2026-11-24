module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

private lemma conj_toAdd {Γ : Type} [Group Γ] {m : ℕ} (x : Γ →* Multiplicative (ZMod m)) (s h : Γ) :
    (x (s * h * s⁻¹)).toAdd = (x h).toAdd := by
  have e : x (s * h * s⁻¹) = x h := by
    rw [map_mul, map_mul, map_inv, mul_comm (x s) (x h), mul_inv_cancel_right]
  rw [e]

private lemma mul_toAdd {Γ : Type} [Group Γ] {m : ℕ} (x : Γ →* Multiplicative (ZMod m)) (g h : Γ) :
    (x (g * h)).toAdd = (x g).toAdd + (x h).toAdd := by
  rw [map_mul, toAdd_mul]

theorem UpperTheory.V.Z.Kato.Sym.PT.edgeGeo :
    UpperTheory.V.Z.Kato.Sym.PT.EdgeGeo := by
  intro Γ _ m Δ x y η hc
  refine ⟨fun g hg h hh => ?_, fun σ hσ g hg h hh => ?_⟩
  · have ha : g * h * g⁻¹ ∈ Δ := Δ.mul_mem (Δ.mul_mem hg hh) (Δ.inv_mem hg)
    have e : g * h * g⁻¹ * g = g * h := by group
    have h1 := hc _ ha g hg
    have h2 := hc g hg h hh
    rw [e, conj_toAdd x] at h1
    simp only [GlobalTheory.KEdge.edge]
    linear_combination h2 - h1
  · have hg' := hσ g hg
    have hh' := hσ h hh
    have e : σ * (g * h) * σ⁻¹ = (σ * g * σ⁻¹) * (σ * h * σ⁻¹) := by group
    have h1 := hc _ hg' _ hh'
    have h2 := hc g hg h hh
    rw [conj_toAdd x, conj_toAdd y] at h1
    simp only [GlobalTheory.KEdge.edge, e, mul_toAdd x, mul_toAdd y]
    linear_combination h1 - h2
