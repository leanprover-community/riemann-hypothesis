module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

namespace GroundTheory.Arith.Toric

universe u

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra

section IntegralDim

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

theorem ringKrullDim_le_of_isIntegral : ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ hpq =>
    Ideal.IsIntegral.comap_lt_comap (R := R) hpq

theorem exists_ltSeries_lift (hinj : Function.Injective (algebraMap R A))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ l' : LTSeries (PrimeSpectrum A), l'.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R A) l'.last = l.last := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal A)
      (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, PrimeSpectrum.ext hQx⟩
  | snoc p x hx ih =>
    obtain ⟨l', hlen, hlast⟩ := ih
    have hle : l'.last.asIdeal.comap (algebraMap R A) ≤ x.asIdeal := by
      have := congrArg PrimeSpectrum.asIdeal hlast
      rw [PrimeSpectrum.comap_asIdeal] at this
      rw [this]
      exact le_of_lt hx
    obtain ⟨Q, hQle, hQ, hQx⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal l'.last.asIdeal hle
    have hlt : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle fun h => ?_
      have h1 : PrimeSpectrum.comap (algebraMap R A) l'.last = x := by
        rw [h]; exact PrimeSpectrum.ext hQx
      exact (ne_of_lt hx) (hlast.symm.trans h1)
    exact ⟨l'.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], PrimeSpectrum.ext (by simpa using hQx)⟩

theorem ringKrullDim_le_of_isIntegral_of_injective (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim R ≤ ringKrullDim A := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift hinj l
  exact le_iSup_of_le l' (by rw [hlen])

theorem ringKrullDim_eq_of_isIntegral (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_le_of_isIntegral_of_injective hinj)

end IntegralDim


variable {k G : Type u} [CommRing k] [IsDomain k] [AddCommGroup G] [Module.Free ℤ G]

variable [Module.Finite ℤ G]



variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]


end GroundTheory.Arith.Toric
