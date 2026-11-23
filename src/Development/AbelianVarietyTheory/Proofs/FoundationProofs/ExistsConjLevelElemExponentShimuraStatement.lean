module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelElemExponentShimura
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem _root_.GlobalTheory.T.exists_conj_level_elem_exponent_shimura : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (N l n M : ℕ) [Fact l.Prime], 0 < M → N ∣ M → l ∣ M → l ^ n ∣ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)), γ ∈ Gam N l → ∃ γ'' ∈ Gam N l, ∃ ζ : Ω, IsPrimitiveRoot ζ M ∧ ∃ d : ℤ, s ζ = ζ ^ d ∧ ((en γ 0 0 : ZMod M) = en γ'' 0 0 ∧ (en γ 0 1 : ZMod M) = d * en γ'' 0 1 ∧ (d : ZMod M) * en γ 1 0 = en γ'' 1 0 ∧ (en γ 1 1 : ZMod M) = en γ'' 1 1) ∧ (d : ZMod (l ^ n)) = PadicInt.toZModPow n (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) := by
  first | exact @GlobalTheory.exists_conj_level_exponent | exact GlobalTheory.exists_conj_level_exponent | (intros; apply GlobalTheory.exists_conj_level_exponent <;> assumption)
