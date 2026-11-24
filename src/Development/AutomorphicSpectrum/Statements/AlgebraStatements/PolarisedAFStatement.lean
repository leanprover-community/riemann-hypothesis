module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
open scoped Matrix

def PolarisedAFStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R]
    (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R),
    HodgeTateSetting p v R O σ cp → ∀ H : HodgeTateDatum p g v R O σ cp,
    let φ := algebraMap R C
    let AF := afLat p H.AA.carrier
    let H' : Set (Ix g → C) := {x | ∀ l ∈ AF, v (∑ i, φ (l i) * x i) ≤ 1}
    let hb : Matrix (Ix g) (Fin g) C := (((H.E.map (algebraMap ℤ_[p] R))ᵀ)⁻¹ * H.Htᵀ).map φ
    AF = Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) ∧
    (∀ l : Ix g → R, cp • l ∈ AF) ∧
    HasLen v R ((Ix g → R) ⧸ AF) (v (φ cp) ^ g) ∧
    HasLen v R (AFQuot p H.AA.carrier) (v (φ cp) ^ g) ∧
    (∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧ ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1) ∧
    (∀ x, (x ∈ H' ∧ H.Ht.map φ *ᵥ x = 0) ↔
      ∃ w : Fin g → C, (∀ k, v (w k) ≤ 1) ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧
    (∀ w : Fin g → C, (∀ k, v (w k) ≤ 1) → ∃ x ∈ H', H.Ht.map φ *ᵥ x = w) ∧
    GenAF p H.AA.carrier ⊥ ∧ IsTight v p H.AA.carrier

end GlobalTheory.CompanionTheory.Ar.GR
