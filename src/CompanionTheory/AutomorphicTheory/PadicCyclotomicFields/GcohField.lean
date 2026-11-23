module

public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohDefs
public import Mathlib.NumberTheory.Padics.ValuativeRel
public import GroundTheory.LocalFields.Examples
public import GroundTheory.LocalFields.FiniteExtension
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCount
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

theorem integer_padic_eq (p : ℕ) [Fact p.Prime] : 𝒪[ℚ_[p]] = PadicInt.subring p := by
  ext x
  change valuation ℚ_[p] x ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← (valuation ℚ_[p]).map_one, ← Valuation.Compatible.vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    GroundTheory.LocalField.Padic.mulValuation_le_iff_norm_le, norm_one]

theorem card_quotient_padic (p : ℕ) [Fact p.Prime] (m : ℕ) :
    Nat.card (𝒪[ℚ_[p]] ⧸ Ideal.span {((p ^ m : ℕ) : 𝒪[ℚ_[p]])}) = p ^ m := by
  let e : 𝒪[ℚ_[p]] ≃+* ℤ_[p] := RingEquiv.subringCongr (integer_padic_eq p)
  have h1 : Ideal.span {((p ^ m : ℕ) : ℤ_[p])} =
      (Ideal.span {((p ^ m : ℕ) : 𝒪[ℚ_[p]])}).map (e : 𝒪[ℚ_[p]] →+* ℤ_[p]) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr (Ideal.quotientEquiv _ _ e h1).toEquiv, Nat.cast_pow,
    ← PadicInt.ker_toZModPow,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow m))).toEquiv, Nat.card_zmod]

theorem isSepClosure_padic (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    IsSepClosure ↥K (PadicAlgCl l) :=
  ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable ℚ_[l] K _⟩

theorem gcField : SgcField := by
  intro l _ K hK
  refine ⟨isSepClosure_padic l K, ?_⟩
  obtain ⟨v, t, h1, h2⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K
  refine ⟨v, t, h1, fun m => ?_⟩
  rw [@card_quotient_span_natCast_finiteExtension ℚ_[l] K _ _ _ _ _ v t h1 _ h2 hK,
    card_quotient_padic]

end CompanionTheory.LocalTateOrthogonality.Gcoh
