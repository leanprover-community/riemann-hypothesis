module

public import GroundTheory.GlobalFields.NormResidueSymbol.RationalCyclotomic
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
public import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField IdeleGroup IntermediateField Topology
open scoped GroundTheory.LocalField.Abstract

noncomputable section

namespace RationalSymbol

open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract

theorem continuous_cycRestrict : Continuous cycRestrict := by
  have : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  have h : @Normal ℚ maxCyclotomic _ _ (IntermediateField.algebra' maxCyclotomic) := by
    convert isGalois_maxCyclotomic.to_normal
  have hc := @InfiniteGalois.restrictNormalHom_continuous ℚ (AlgebraicClosure ℚ) _ _ _ maxCyclotomic h
  exact hc

theorem continuous_cycCharacter : Continuous cycCharacter := by
  have : T2Space Gal(maxCyclotomic/ℚ) := krullTopology_t2
  have hq : IsQuotientMap cycRestrict :=
    continuous_cycRestrict.isClosedMap.isQuotientMap continuous_cycRestrict cycRestrict_surjective
  rw [hq.continuous_iff]
  exact continuous_character.congr fun σ ↦ (cycCharacter_cycRestrict σ).symm

def cycCharacterHomeomorph : Gal(maxCyclotomic/ℚ) ≃ₜ* ℤ̂ˣ where
  toMulEquiv := cycCharacter
  continuous_toFun := continuous_cycCharacter
  continuous_invFun :=
    (continuous_cycCharacter.homeoOfEquivCompactToT2 (f := cycCharacter.toEquiv)).symm.continuous

def unitsPadicHomeomorph : (Π q : Nat.Primes, ℤ_[q])ˣ ≃ₜ* ℤ̂ˣ :=
  unitsContinuousMulEquiv padicEquiv.symm.toMulEquiv continuous_ofPadics continuous_toPadics

theorem unitPart_eq (x : IdeleClassGroup ℚ) :
    unitPart x = unitsPadicHomeomorph (RationalIdeles.ideleClassGroupEquiv x).2 :=
  Units.ext rfl

theorem continuous_unitPart : Continuous unitPart := by
  have h : (unitPart : IdeleClassGroup ℚ → ℤ̂ˣ) =
      unitsPadicHomeomorph ∘ Prod.snd ∘ RationalIdeles.ideleClassGroupEquiv :=
    funext unitPart_eq
  rw [h]
  exact unitsPadicHomeomorph.continuous.comp
    (continuous_snd.comp RationalIdeles.ideleClassGroupEquiv.continuous)

end RationalSymbol

end

end GroundTheory.Global
