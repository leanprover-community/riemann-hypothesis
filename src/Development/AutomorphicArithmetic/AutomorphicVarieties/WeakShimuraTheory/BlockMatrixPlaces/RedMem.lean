module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.redMem :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T) (n : ℕ) z y, IsZn ρ c N H P (n + 1) z y → IsZn ρ c N H P n (fun g => redn A T n (z g)) (redn A T n y) ∧
          (Prim z → 0 < n → Prim fun g => redn A T n (z g)) ∧ (Prim (fun g => redn A T n (z g)) → Prim z) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P n z y hz
  have eqv : ∀ (g : Γ) (w : T ⧸ lev A T (n + 1)),
      redn A T n (modRep ρ (n + 1) g w) = modRep ρ n g (redn A T n w) := by
    intro g w
    obtain ⟨x, rfl⟩ := (lev A T (n + 1)).mkQ_surjective w
    rw [modRep_mk, redn_mk, redn_mk, modRep_mk]
  have img : ∀ (Q : Submodule A T) (w : T ⧸ lev A T (n + 1)), w ∈ Q.map (lev A T (n + 1)).mkQ →
      redn A T n w ∈ Q.map (lev A T n).mkQ := by
    rintro Q _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine ⟨⟨hz.lc.comp (redn A T n), fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_, ?_⟩
  · rw [hz.coc, map_add (f := _), eqv]
  · rw [hz.cz, map_zero]
  · rw [hz.kill g hg, map_zero]
  · have := img P _ (hz.loc h hh)
    rw [map_sub, map_sub, eqv] at this
    exact this
  · rintro ⟨g, hg⟩ hn
    refine ⟨g, fun hm => hg ?_⟩
    obtain ⟨x, hx⟩ := (lev A T (n + 1)).mkQ_surjective (z g)
    obtain ⟨x', hx', e⟩ := hm
    have e' : (lev A T n).mkQ x' = (lev A T n).mkQ x := by rw [e, ← redn_mk, hx]
    have hd : x' - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e'
    have hle : lev A T n ≤ lev A T 1 := Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)
    refine ⟨x, ?_, hx⟩
    have := (lev A T 1).sub_mem hx' (hle hd)
    rwa [sub_sub_cancel] at this
  · rintro ⟨g, hg⟩
    exact ⟨g, fun hm => hg (img _ _ hm)⟩
