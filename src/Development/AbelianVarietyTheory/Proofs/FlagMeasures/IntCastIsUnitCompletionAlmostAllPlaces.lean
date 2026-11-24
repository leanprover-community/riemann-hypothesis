module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

theorem intCast_isUnit_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (D : ℤ), D ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (D : (A.loc p).Fp)}.Finite := by
  intro F E _ _ _ _ _ sig A D hD
  have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD
  refine (HeightOneSpectrum.Support.finite (𝓞 F) ((D : F)⁻¹)).subset fun p hp => ?_
  by_contra hs
  apply hp
  have hs' : p.valuation F ((D : F)⁻¹) ≤ 1 := by
    have := hs
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at this
    exact this
  have h1 : p.valuation F (D : F) ≤ 1 := by
    have := p.valuation_le_one (K := F) (D : 𝓞 F)
    simpa using this
  have m1 := ((integers_local A).2.2.1 (D : F) p).2 h1
  have m2 := ((integers_local A).2.2.1 ((D : F)⁻¹) p).2 hs'
  have hne : (A.loc p).ιF (D : F) ≠ 0 := by
    rw [map_ne_zero]; exact hDF
  refine ⟨⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (A.loc p).ιF (D : F) * (A.loc p).ιF ((D : F)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ hDF, map_one]
  · apply Subtype.ext
    change (A.loc p).ιF ((D : F)⁻¹) * (A.loc p).ιF (D : F) = 1
    rw [← map_mul, inv_mul_cancel₀ hDF, map_one]
  · change (A.loc p).ιF (D : F) = _
    exact map_intCast _ D

end GlobalTheory.HL.PlacesInt
