module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalRingOfIsIntegralOfHenselian
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.NormalLocal

theorem exists_normal_local (A : Type) [CommRing A] [HenselianLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S) (_ : IsIntegrallyClosed S) (_ : IsLocalRing S) (f : A →+* S),
      f.IsIntegral ∧ RingHom.ker f = 𝔭 := by
  let B := A ⧸ 𝔭
  let K := FractionRing B
  let S := integralClosure B K
  have : IsFractionRing S K := inferInstance
  have hic : IsIntegrallyClosed S := (isIntegrallyClosed_iff_isIntegrallyClosedIn K).mpr inferInstance
  letI : Algebra A S := ((algebraMap B S).comp (Ideal.Quotient.mk 𝔭)).toAlgebra
  have h1 : (Ideal.Quotient.mk 𝔭).IsIntegral := RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  have h2 : (algebraMap B S).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := B) x
  have hint : (algebraMap A S).IsIntegral := RingHom.IsIntegral.trans _ _ h1 h2
  haveI : Algebra.IsIntegral A S := ⟨fun x => hint x⟩
  have hloc : IsLocalRing S := GlobalTheory.IntClLocal.isLocalRing_of_isIntegral_of_henselian A S
  have hinjK : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
  have hinj : Function.Injective (algebraMap B S) := by
    intro x y h
    exact hinjK (congrArg Subtype.val h)
  refine ⟨S, inferInstance, inferInstance, hic, hloc, algebraMap A S, hint, ?_⟩
  ext a
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  change (algebraMap B S) (Ideal.Quotient.mk 𝔭 a) = 0 ↔ _
  rw [← map_zero (algebraMap B S), hinj.eq_iff]

end GlobalTheory.NormalLocal
