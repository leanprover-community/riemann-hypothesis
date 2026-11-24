module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem exists_representation_character_eq_add (K : Type) [Field K] (G : Type) [Group G]
    (n m : ℕ) (ρ : Representation K G (Fin n → K)) (σ : Representation K G (Fin m → K)) :
    ∃ τ : Representation K G (Fin (n + m) → K),
      ∀ g, τ.character g = ρ.character g + σ.character g := by
  let e : ((Fin n → K) × (Fin m → K)) ≃ₗ[K] (Fin (n + m) → K) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) K K).symm ≪≫ₗ
      LinearEquiv.funCongrLeft K K finSumFinEquiv.symm
  refine ⟨{ toFun := fun g => e.conj ((ρ g).prodMap (σ g)), map_one' := ?_, map_mul' := ?_ },
    fun g => ?_⟩
  · simp only [map_one, LinearMap.prodMap_one]
    exact e.conj_id
  · intro g h
    simp only [map_mul]
    rw [← LinearMap.prodMap_mul]
    exact e.conj_comp _ _
  · simp only [Representation.character]
    show LinearMap.trace K _ (e.conj _) = _
    rw [LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem _root_.GlobalTheory.BI.isChar_zero_and_add : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (G : Type) [Group G], _root_.GlobalTheory.BI.IsChar K L (0 : G → L) ∧
      ∀ a b : G → L, _root_.GlobalTheory.BI.IsChar K L a → _root_.GlobalTheory.BI.IsChar K L b →
        _root_.GlobalTheory.BI.IsChar K L (a + b) := by
  intro K L _ _ _ G _
  refine ⟨?_, ?_⟩
  · unfold _root_.GlobalTheory.BI.IsChar
    refine ⟨0, 1, fun g => ?_⟩
    simp [Representation.character]
  · intro a b ha hb
    unfold _root_.GlobalTheory.BI.IsChar at ha hb ⊢
    obtain ⟨n, ρ, hρ⟩ := ha
    obtain ⟨m, σ, hσ⟩ := hb
    obtain ⟨τ, hτ⟩ := exists_representation_character_eq_add K G n m ρ σ
    refine ⟨n + m, τ, fun g => ?_⟩
    rw [Pi.add_apply, hρ g, hσ g, hτ g, map_add (f := _)]

end GlobalTheory.BI
