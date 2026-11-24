module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem RatModel.IsCl.subfield_eq_top_of_ratios {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]
    {M : RatModel o Ω} {J : Type} {t : J → Ω} (h : M.IsCl t) (K : Subfield Ω)
    (hc : ∀ a, algebraMap o Ω a ∈ K) (hr : ∀ i j, t j / t i ∈ K) : K = ⊤ := by
  obtain ⟨i, hi⟩ := h.1 (genericPoint M.Z)
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi.1
  have hne : (U : Set M.Z).Nonempty := ⟨genericPoint M.Z, by rw [hD]; exact hi⟩
  let A : Subalgebra o Ω := { K.toSubring with algebraMap_mem' := hc }
  have hle : M.ringOn U ≤ A := by
    rw [hR]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact hr i j
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, -, rfl⟩ := RatModel.exists_eq_div hU hne x
  exact div_mem (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩))
    (hle ((RatModel.mem_ringOn_iff_exists hne).2 ⟨b, rfl⟩))

theorem finite_closure_theta_ratios_of_isCl (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω) (J : Type) (t : J → Ω) (h : M.IsCl t) :
    Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)})) Ω := by
  obtain ⟨x, hx⟩ := S.th_ne
  have htop := h.subfield_eq_top_of_ratios (Subfield.closure (Set.range (algebraMap o Ω) ∪
      {x | ∃ i j : S.Gam × J, x = S.th j.1 * t j.2 / (S.th i.1 * t i.2)}))
    (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
    (fun i j => Subfield.subset_closure (Or.inr ⟨(x, i), (x, j), (mul_div_mul_left _ _ hx).symm⟩))
  refine Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun y => ⟨⟨y, ?_⟩, rfl⟩
  rw [htop]
  exact Subfield.mem_top y

end GlobalTheory.ZH
