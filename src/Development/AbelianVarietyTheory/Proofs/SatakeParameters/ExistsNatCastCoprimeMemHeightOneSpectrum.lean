module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.IsComplRatCompl
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Imports
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory

theorem natCast_mem_heightOneSpectrum_coprime :
    ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (P : HeightOneSpectrum (𝓞 E)), ((p : ℕ) : 𝓞 E) ∉ P.asIdeal → ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p := by
  intro E _ _ p hp P hpP
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  haveI : P.asIdeal.IsPrime := P.isPrime
  have hmem : ∀ n : ℕ, ((n : 𝓞 E) ∈ P.asIdeal ↔ ringChar (𝓞 E ⧸ P.asIdeal) ∣ n) := by
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.spec _ n
  have hq0 : ringChar (𝓞 E ⧸ P.asIdeal) ≠ 0 := by
    intro h0
    have := (hmem _).1 (Ideal.absNorm_mem P.asIdeal)
    rw [h0, zero_dvd_iff] at this
    exact hN this
  have hqp : (ringChar (𝓞 E ⧸ P.asIdeal)).Prime :=
    (CharP.char_is_prime_or_zero (𝓞 E ⧸ P.asIdeal) _).resolve_right hq0
  refine ⟨ringChar (𝓞 E ⧸ P.asIdeal), hqp.pos, (hmem _).2 dvd_rfl, ?_⟩
  refine (Nat.coprime_primes hqp hp).2 ?_
  intro hq
  exact hpP ((hmem p).2 (hq ▸ dvd_rfl))

end GlobalTheory
