module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisConjugateModularFunctionSomeLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHomStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHomStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_ringEquiv_coeff_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω),
    ∃ σ : GlobalTheory.FN.ring ε.range ≃+* GlobalTheory.FN.ring ε.range, ∀ (a : GlobalTheory.FN.ring ε.range) (h h' : HahnSeries ℚ Ω),
      IsExp ε a h → IsExp ε (σ a : GlobalTheory.FN.ring ε.range) h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s
  obtain ⟨e, he_inj, he⟩ := GlobalTheory.T.exists_injective_cuspExpansion_ringHom Ω ε
  have hmem := (GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1
  have key : ∀ t : Ω ≃+* Ω, ∃ c : ring ε.range → ring ε.range, ∀ a,
      (∀ r, (e (c a)).coeff r = t ((e a).coeff r)) ∧
      ∀ h h' : HahnSeries ℚ Ω, IsExp ε a h → IsExp ε (c a : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
    intro t
    have hex : ∀ a : ring ε.range, ∃ b : ring ε.range, ∀ h h' : HahnSeries ℚ Ω,
        IsExp ε a h → IsExp ε (b : ℍ → ℂ) h' → ∀ r, h'.coeff r = t (h.coeff r) := by
      intro a
      obtain ⟨f', hf', hp⟩ := GlobalTheory.T.exists_galoisConjugate_modularFunction_someLevel Ω ε t a ((hmem a).1 a.2)
      exact ⟨⟨f', (hmem f').2 hf'⟩, hp⟩
    choose c hc using hex
    exact ⟨c, fun a => ⟨hc a (e a) (e (c a)) (he a) (he (c a)), hc a⟩⟩
  have mapc : ∀ t : Ω ≃+* Ω, ∃ Φ : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω, ∀ h r, (Φ h).coeff r = t (h.coeff r) := by
    intro t
    obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω t.toRingHom 1 (fun _ => 1) one_pos rfl (by simp)
    exact ⟨Φ, fun h r => by simpa using hΦ h r⟩
  obtain ⟨c, hc⟩ := key s
  obtain ⟨d, hd⟩ := key s.symm
  obtain ⟨Φ, hΦ⟩ := mapc s
  have ec : ∀ a, e (c a) = Φ (e a) := fun a => by
    ext r
    rw [(hc a).1, hΦ]
  refine ⟨{ toFun := c, invFun := d, left_inv := ?_, right_inv := ?_, map_add' := ?_, map_mul' := ?_ },
    fun a h h' => (hc a).2 h h'⟩
  · intro a
    apply he_inj
    ext r
    rw [(hd _).1, (hc a).1]
    simp
  · intro a
    apply he_inj
    ext r
    rw [(hc _).1, (hd a).1]
    simp
  · intro a b
    apply he_inj
    simp only [map_mul, ec]
  · intro a b
    apply he_inj
    simp only [map_add (f := _), ec]

end GlobalTheory.FN
