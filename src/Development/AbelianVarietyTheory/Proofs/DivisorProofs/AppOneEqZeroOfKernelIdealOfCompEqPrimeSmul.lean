module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G H : PDivGroup p R) (f : G ⟶ H) (g : H ⟶ G),
      g ≫ f = (p : ℤ_[p]) • 𝟙 H → ∀ a ∈ kerIdeal (f.app 1), g.app 1 a = 0 := by
  intro p _ R _ G H f g hgf a ha
  have hle : kerIdeal (f.app 1) ≤ RingHom.ker (g.app 1 : G.A 1 →ₐ[R] H.A 1) := by
    rw [kerIdeal, Ideal.map_le_iff_le_comap]
    intro c hc
    have hc' : counit (R := R) c = 0 := hc
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have e : g.app 1 (f.app 1 c) = Hom.app (g ≫ f) 1 c := rfl
    change g.app 1 (f.app 1 c) = 0
    rw [e, hgf, prime_smul_id_app]
    have h1 := H.mulBy_pow_self 1 c
    rw [pow_one] at h1
    rw [h1, hc', map_zero]
  exact hle ha

end GlobalTheory.PDivGroup
