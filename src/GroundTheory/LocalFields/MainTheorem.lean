module

public import GroundTheory.LocalFields.LocalArtinFunctoriality
public import GroundTheory.LocalFields.LocalArtinTransport
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
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel


variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]


section Functoriality

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {K' : Type*} [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem isSepClosure_of_isSeparable (K K' Ω : Type*) [Field K] [Field K'] [Field Ω] [Algebra K K']
    [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω] [Algebra.IsSeparable K K'] [IsSepClosure K' Ω] :
    IsSepClosure K Ω :=
  ⟨IsSepClosure.sep_closed K', Algebra.IsSeparable.trans K K' Ω⟩

theorem localArtinMap_norm [Algebra K K'] [ValuativeExtension K K'] [FiniteDimensional K K']
    [Algebra.IsSeparable K K'] {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower K K' Ω] [IsSepClosure K' Ω] (x : K'ˣ) {y : Ω} :
    have := isSepClosure_of_isSeparable K K' Ω
    ∀ hy : y ∈ maximalAbelianExtension K Ω,
      ((localArtinMap K' Ω x ⟨y, maximalAbelianExtension_le_of_algebra hy⟩ :
        maximalAbelianExtension K' Ω) : Ω) =
        ((localArtinMap K Ω (normUnits K K' x) ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) := by
  intro _ hy
  exact localArtinMap_apply_of_algebra x hy

theorem localArtinMap_transport {Ω Ω' : Type*} [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K' Ω']
    [IsSepClosure K Ω] [IsSepClosure K' Ω'] (e : K ≃+* K') (he : ∀ x y : K, e x ≤ᵥ e y ↔ x ≤ᵥ y)
    (ε : Ω ≃+* Ω') (hε : ∀ x : K, ε (algebraMap K Ω x) = algebraMap K' Ω' (e x)) (x : Kˣ) {y : Ω}
    (hy : y ∈ maximalAbelianExtension K Ω) :
    ε ((localArtinMap K Ω x ⟨y, hy⟩ : maximalAbelianExtension K Ω) : Ω) =
      ((localArtinMap K' Ω' (Units.map e.toRingHom.toMonoidHom x)
        ⟨ε y, (mem_maximalAbelianExtension_transport_iff e ε hε).2 hy⟩ :
          maximalAbelianExtension K' Ω') : Ω') :=
  transport_localArtinMap_apply e he ε hε x hy

end Functoriality

end GroundTheory.LocalField
