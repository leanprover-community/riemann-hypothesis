module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.secCard_of :
    SecCard := by
  intro p _ D R _ b N M r w j c T hm K _ _ hp x y hxy
  subst hxy
  let β : R →+* K := (Spec.preimage (y ≫ T.s ≫ M.s)).hom
  haveI : CharZero K := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
    · exfalso
      have hcast : ((ringChar K : ℕ) : K) = 0 := ringChar.Nat.cast_ringChar
      by_cases hqp : ringChar K = p
      · rw [hqp] at hcast
        exact hp hcast
      · have hcop : (ringChar K).Coprime p := (Nat.coprime_primes hq (Fact.out)).mpr hqp
        have hu := (b.unit _ hcop).map β
        rw [map_natCast, hcast] at hu
        exact not_isUnit_zero hu
    · haveI : CharP K 0 := ringChar.of_eq hq
      exact CharP.charP_to_charZero K
  obtain ⟨-, hcard⟩ := T.tj K y
  rw [hm, Nat.one_mul] at hcard
  rw [← hcard]
  symm
  have hK : ∀ a : Over.mk y ⟶ T.o.A,
      KilledBy T.o w a ↔ KilledBy M.univ w (T.ms.ptEquiv (Over.mk y) a) := by
    intro a
    unfold KilledBy
    refine forall₂_congr (fun c _ => ?_)
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]
  have hker : ∀ a : Over.mk y ⟶ T.o.A,
      KerAt T y (T.ms.ptEquiv (Over.mk y) a).left ↔ a ≫ T.ψ = 1 := by
    intro a
    rw [ObjMap.ptEquiv_left]
    constructor
    · intro h
      exact h a rfl
    · intro h a' ha'
      have ha : a' = a := by
        apply (T.ms.ptEquiv (Over.mk y)).injective
        apply Over.OverMorphism.ext
        rw [ObjMap.ptEquiv_left, ObjMap.ptEquiv_left, ha']
      rw [ha]
      exact h
  refine Nat.card_congr (Equiv.subtypeEquiv (T.ms.ptEquiv (Over.mk y)).toEquiv (fun a => ?_))
  exact ⟨fun h => ⟨(hK a).mp h.2, (hker a).mpr h.1⟩, fun h => ⟨(hker a).mp h.2, (hK a).mpr h.1⟩⟩
