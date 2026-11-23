module

public import Formalism.PeriodIntegrals.LocDualGen
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
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq

@[expose] public section

noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen.Part2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p)

theorem alg_mem_O (r : 𝒪[A.Fp]) : algebraMap A.Fp A.Ep (r : A.Fp) ∈ A.O := by
  rw [A.O_def]
  have : algebraMap A.Fp A.Ep (r : A.Fp) = algebraMap 𝒪[A.Fp] A.Ep r := rfl
  rw [this]
  exact isIntegral_algebraMap

theorem dualAtL_mul_unit (δ : A.Fp) (u : 𝒪[A.Fp]) (hu : IsUnit u) (h : DualAtL A δ) :
    DualAtL A (δ * (u : A.Fp)) := by
  intro x
  rw [← h x]
  obtain ⟨v, rfl⟩ := hu
  have hv : ((v : 𝒪[A.Fp]) : A.Fp) * ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  set a := algebraMap A.Fp A.Ep ((v : 𝒪[A.Fp]) : A.Fp)
  set b := algebraMap A.Fp A.Ep ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp)
  have hab : a * b = 1 := by rw [← map_mul, hv, map_one]
  have hinv : (((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = ((v⁻¹ : (𝒪[A.Fp])ˣ) : A.Fp) :=
    inv_eq_of_mul_eq_one_right hv
  have key : algebraMap A.Fp A.Ep (δ * ((v : 𝒪[A.Fp]) : A.Fp))⁻¹ = algebraMap A.Fp A.Ep δ⁻¹ * b := by
    rw [mul_inv, map_mul, hinv]
  constructor
  · intro H y hy
    have := H (y * a) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * (y * a) * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * y * algebraMap A.Fp A.Ep δ⁻¹ * (a * b) by ring,
      hab, mul_one] at this
  · intro H y hy
    have := H (y * b) (A.O.mul_mem hy (alg_mem_O A _))
    rwa [key, show x * y * (algebraMap A.Fp A.Ep δ⁻¹ * b) = x * (y * b) * algebraMap A.Fp A.Ep δ⁻¹ by ring]

end PI.LocDualGen.Part2
