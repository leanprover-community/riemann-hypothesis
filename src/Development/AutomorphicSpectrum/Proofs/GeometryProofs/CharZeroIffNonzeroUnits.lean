module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GenericMap
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.CharTie

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}

theorem unit_natCast (h : Char0 ξ q) (n : ℕ) (hn : n ≠ 0) : unitAt ξ q (n : Ω) :=
  _root_.UpperTheory.Reformulated.B.GenericMap.main h n hn

theorem char_zero_iff_integers_units (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω]
    (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω) (ht : CoordTie (𝓞 F) ξ t) (p : Cpt ξ) :
    Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  constructor
  · intro h d hd
    have hreg : ∀ b : 𝓞 F, algebraMap (𝓞 F) Ω b ∈ regAt ξ p := by
      intro b
      obtain ⟨c, hc⟩ := ht.cover p
      exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ b) p hc
    have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hd
    obtain ⟨d', hd'⟩ := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem (Ideal.span {d}))
    have hu := unit_natCast h _ hn
    have e : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : Ω) = algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d' := by
      rw [← map_mul, ← hd', map_natCast]
    rw [e] at hu
    have ha : algebraMap (𝓞 F) Ω d ≠ 0 := left_ne_zero_of_mul hu.1
    have hb : algebraMap (𝓞 F) Ω d' ≠ 0 := right_ne_zero_of_mul hu.1
    refine ⟨ha, hreg d, ?_⟩
    have e2 : (algebraMap (𝓞 F) Ω d)⁻¹ =
        algebraMap (𝓞 F) Ω d' * (algebraMap (𝓞 F) Ω d * algebraMap (𝓞 F) Ω d')⁻¹ := by
      field_simp
    rw [e2]
    exact mul_mem (hreg d') hu.2.2
  · intro h r hr hf
    have hr0 : (r : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
    have := h _ hr0
    rw [map_natCast] at this
    exact hf this

end GlobalTheory.CompanionTheory.Ar.SncBase.CharTie
