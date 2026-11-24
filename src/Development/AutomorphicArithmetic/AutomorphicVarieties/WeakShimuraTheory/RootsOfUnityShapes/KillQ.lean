module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Rq.killQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ T : Tower D, T.Ok →
      ∀ (pr : Bool) (g0 : G ℚ Ω) (M : Type) [Monoid M] (r : G ℚ Ω →* M), (∀ g ∈ (frQ D pr g0).N, r g = 1) →
        ∀ g ∈ (T.fr ∅).N, r (resQ T.F g) = 1 := by
  intro Ω _ _ _ l _ c D hD T hT pr g0 M _ r hr g hg
  obtain ⟨A, hA, hI, hb⟩ := hg
  have hIQ : resQ T.F g ∈ Ine (F := ℚ) A := hI
  have hl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  by_cases hw : Raw.Away D.T A
  · exact hr _ (Or.inl ⟨A, hw, hIQ, hb⟩)
  · have hw' : ∃ p ∈ D.T, A.valuation (p : Ω) < 1 := by
      by_contra h
      exact hw fun p hp hv => h ⟨p, hp, hv⟩
    obtain ⟨p, hp, hv⟩ := hw'
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact absurd hv hl
    have hpS : p ∈ D.S := by
      unfold Raw.Sb at hp
      exact Finset.mem_of_mem_filter _ hp
    have hpp : p.Prime := hD.S_prime p hpS
    obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 p A (D.pl p) hpp hv (hD.pl_over p hpp)
    have hψ : D.ψ (resQ T.F g) = 1 :=
      hT.kb A (fun q hq => by rw [Finset.mem_singleton.1 hq]; exact hl) g hI hb
    have hk : u⁻¹ * resQ T.F g * u ∈ D.ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, hψ, mul_one, ← map_mul, inv_mul_cancel, map_one]
    have h1 : r (u⁻¹ * resQ T.F g * u) = 1 := hr _ (Or.inr ⟨p, hp, hu _ hIQ, hk⟩)
    have h2 : resQ T.F g = u * (u⁻¹ * resQ T.F g * u) * u⁻¹ := by group
    rw [h2, map_mul, map_mul, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]
