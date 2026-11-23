module

public import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
public import Formalism.LocalToGlobal.Divisibility.ConjugationAtDistinguishedPlace
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.RayFieldNorm

theorem normSq_eq_absNorm {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (π : 𝓞 K) :
    ‖φ π‖ ^ 2 = (Ideal.absNorm (Ideal.span {π}) : ℝ) := by
  have h1 : Fintype.card (InfinitePlace K) = 1 := by
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h4 := IsTotallyComplex.nrRealPlaces_eq_zero K
    omega
  have : Subsingleton (InfinitePlace K) := Fintype.card_le_one_iff_subsingleton.mp h1.le
  have h5 := InfinitePlace.prod_eq_abs_norm (π : K)
  rw [Fintype.prod_subsingleton _ (InfinitePlace.mk φ), IsTotallyComplex.mult_eq,
    InfinitePlace.apply] at h5
  rw [h5, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  simp

theorem isTotallyComplex_of_isEmpty {K : Type} [Field K] [NumberField K]
    (h : IsEmpty (K →+* ℝ)) : IsTotallyComplex K := by
  rw [isTotallyComplex_iff]
  intro w
  rw [← InfinitePlace.not_isReal_iff_isComplex]
  intro hw
  obtain ⟨φ, hφ, -⟩ := hw
  exact h.elim (NumberField.ComplexEmbedding.IsReal.embedding hφ)

theorem exists_mul_conj_eq_norm : ∀ (K : Type) [Field K] [NumberField K], IsEmpty (K →+* ℝ) → Module.finrank ℚ K = 2 →
    ∀ (j : K →+* Qb) (π : 𝓞 K) (p : ℕ), Ideal.absNorm (Ideal.span {π}) = p →
      ∃ σ : Qb →ₐ[ℚ] Qb, j (π : K) * σ (j (π : K)) = (p : Qb) := by
  intro K _ _ hE hK j π p hp
  haveI := isTotallyComplex_of_isEmpty hE
  haveI : Algebra.IsAlgebraic ℚ Qb := AlgebraicClosure.isAlgebraic ℚ
  let ι : Qb →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := Qb)).toRingHom
  refine ⟨(Formalism.L2.DIV.conjQb ι).toAlgHom, ?_⟩
  apply ι.injective
  have hn := normSq_eq_absNorm hK (ι.comp j) π
  rw [hp] at hn
  have hc : ι (j (π : K)) * starRingEnd ℂ (ι (j (π : K))) = ((‖ι (j (π : K))‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hs := Formalism.L2.DIV.conjQb_spec ι (j (π : K))
  change ι (j (π : K) * (Formalism.L2.DIV.conjQb ι) (j (π : K))) = ι (p : Qb)
  rw [map_mul, hs, hc, map_natCast]
  simp only [RingHom.comp_apply] at hn
  rw [hn]
  simp

end GlobalTheory.RayFieldNorm
