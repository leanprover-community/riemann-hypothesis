module

public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.LogRootDiscChar
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
public import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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

namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

private theorem annihilator_eq_iso (H : Subgroup (ZMod N)ˣ) :
    annihilator ℂ (H : Set (ZMod N)ˣ) =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ H).ofDual := by
  ext χ
  simp [mem_annihilator_iff]

private theorem charKer_eq_iso (X : Subgroup (DirichletCharacter ℂ N)) :
    charKer X =
      (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod N) ℂ).symm (OrderDual.toDual X) := by
  ext m
  simp [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, Units.ext_iff]

private theorem card_annihilator_eq (H : Subgroup (ZMod N)ˣ) :
    Nat.card (annihilator ℂ (H : Set (ZMod N)ˣ)) = H.index := by
  rw [annihilator_eq_iso, MulChar.card_subgroupOrderIsoSubgroupMulChar]
  rfl

theorem annihilator_charKer (X : Subgroup (DirichletCharacter ℂ N)) (H : Subgroup (ZMod N)ˣ) :
    annihilator ℂ (charKer X : Set (ZMod N)ˣ) = X ∧
      charKer (annihilator ℂ (H : Set (ZMod N)ˣ)) = H ∧ Nat.card X = (charKer X).index := by
  have h1 : annihilator ℂ (charKer X : Set (ZMod N)ˣ) = X := by
    rw [charKer_eq_iso, annihilator_eq_iso, OrderIso.apply_symm_apply]
    rfl
  refine ⟨h1, ?_, ?_⟩
  · rw [annihilator_eq_iso, charKer_eq_iso]
    simp
  · rw [← card_annihilator_eq, h1]

end KStar.Ram
