module

public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsDedekindDomain

namespace GlobalTheory.InertiaDVR

theorem perfectField_residueField_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    [PerfectField (IsLocalRing.ResidueField R)] (p : Ideal R) [p.IsPrime] (hp : p = IsLocalRing.maximalIdeal R) :
    PerfectField p.ResidueField := by
  subst hp
  have hb := Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R)
  let e : IsLocalRing.ResidueField R ≃+* (IsLocalRing.maximalIdeal R).ResidueField :=
    RingEquiv.ofBijective _ hb
  letI : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    e.toRingHom.toAlgebra
  have : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.maximalIdeal R).ResidueField :=
    ⟨fun x => by obtain ⟨y, rfl⟩ := e.surjective x; exact isIntegral_algebraMap⟩
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField R)

theorem card_inertia_eq_ramificationIdx : ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (IsLocalRing.ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Algebra R L] [IsScalarTower R K L]
    [SMulCommClass (L ≃ₐ[K] L) R L] [IsDedekindDomain (integralClosure R L)]
    [IsFractionRing (integralClosure R L) L] (P : IsDedekindDomain.HeightOneSpectrum (integralClosure R L)),
    Nat.card (P.asIdeal.inertia (L ≃ₐ[K] L)) = P.asIdeal.ramificationIdx R := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have : IsGaloisGroup (L ≃ₐ[K] L) R (integralClosure R L) := IsGaloisGroup.of_isFractionRing _ _ _ K L
  have : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : FaithfulSMul R (integralClosure R L) :=
    (faithfulSMul_iff_algebraMap_injective R _).2 (fun a b h => hinj (congrArg Subtype.val h))
  have : Module.Flat R (integralClosure R L) :=
    Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  have := P.isPrime
  have hp0 : P.asIdeal.under R ≠ ⊥ := Ideal.under_ne_bot R P.ne_bot
  have hpm : P.asIdeal.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal ((Ideal.IsPrime.under R P.asIdeal).isMaximal hp0)
  have : PerfectField (P.asIdeal.under R).ResidueField :=
    perfectField_residueField_maximalIdeal R _ hpm
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.asIdeal.under R) P.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under R) P.asIdeal (L ≃ₐ[K] L)]

end GlobalTheory.InertiaDVR
