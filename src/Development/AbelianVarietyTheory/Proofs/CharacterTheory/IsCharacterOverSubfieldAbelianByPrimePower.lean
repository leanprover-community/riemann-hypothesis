module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrimStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsAbelianByPrimePowerGroupSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducibleStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldLinearOfPrimitiveRootStatement
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldZeroAndAddStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_abByP : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → (∀ g : G, g ^ m = 1) → AbByP G →
      ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn hG hA χ hχ
      refine GlobalTheory.T.isCharacterOverSubfield_induction_irreducible L L G (fun a => IsChar K L a) (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).1 ?_ χ hχ
      intro φ c hφ _ hc
      refine (GlobalTheory.T.isCharacterOverSubfield_zero_and_add K L G).2 φ c ?_ hc
      rcases GlobalTheory.T.irreducibleCharacter_linear_or_induced_abelianByPrimePower L G φ hA hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have : φ = fun g => (lam g : L) := funext hlam
        rw [this]
        exact GlobalTheory.T.isCharacterOverSubfield_linear_of_primitiveRoot K L G m ζ lam hm hζ hG
      · have hlt : Nat.card T < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group T)
            (fun h => hT (Subgroup.eq_top_of_card_eq T h))
        refine GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction K L G T ψ (ih _ hlt T rfl ?_ (GlobalTheory.T.isAbelianByPrimePowerGroup_subgroup G T hA) ψ hψ)
        intro g
        exact Subtype.ext (by simpa using hG g)
  intro G _ _
  exact key _ G rfl
end GlobalTheory.BI
