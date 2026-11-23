module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.IndChar

theorem isChar_iff_coord {G : Type} [Group G] (χ : G → ℂ) :
    GlobalTheory.GLq.IsChar χ ↔ GlobalTheory.BI.IsChar ℂ ℂ χ := by
  constructor
  · rintro ⟨V, hV⟩

    let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := (Module.finBasis ℂ V).equivFun
    refine ⟨Module.finrank ℂ V, GlobalTheory.BI.transportRep V.ρ e, fun g => ?_⟩
    rw [GlobalTheory.BI.character_transportRep, ← hV g]
    rfl
  · rintro ⟨n, ρ, hρ⟩
    refine ⟨FDRep.of ρ, fun g => ?_⟩
    rw [hρ g]
    rfl

theorem isChar_induced : ∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G) (φ : H → ℂ), IsChar φ → IsChar (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G, if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) := by
  intro G _ _ H φ hφ

  have hind : GlobalTheory.BI.IsChar ℂ ℂ (GlobalTheory.BI.ind H φ) :=
    GlobalTheory.BI.isChar_ind ℂ ℂ G H φ ((isChar_iff_coord φ).mp hφ)
  have heq : (fun x : G => (Nat.card H : ℂ)⁻¹ * ∑ y : G,
      if h : y⁻¹ * x * y ∈ H then φ ⟨_, h⟩ else 0) = GlobalTheory.BI.ind H φ := by
    funext x
    unfold GlobalTheory.BI.ind
    rw [finsum_eq_sum_of_fintype]
    congr 1
  rw [heq]
  exact (isChar_iff_coord _).mpr hind

end GlobalTheory.GLm.IndChar
