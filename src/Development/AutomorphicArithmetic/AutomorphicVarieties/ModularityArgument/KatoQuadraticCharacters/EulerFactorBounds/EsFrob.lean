module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.EsStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.FrobeniusConjugateInertia.FrobConjIne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsFrob : UpperTheory.V.Z.Kato.Nb.SEsFrob := by
  intro Ω _ _ _ l _ v B σ hq hql hB hF
  obtain ⟨hσ, hfr⟩ := hF
  have hmem : ∀ g : Gal(Ω/ℚ), g ∈ ValuationSubring.decompositionSubgroup ℚ B → ∀ y ∈ B, g y ∈ B :=
    fun g hg y hy => (B.subMulAction ℚ).smul_mem' ⟨g, hg⟩ hy
  refine ⟨⟨?_, fun y hy => ⟨hmem σ hσ y hy, hmem σ⁻¹ (inv_mem hσ) y hy,
    hfr y ((B.valuation_le_one_iff y).mpr hy)⟩⟩, ?_⟩
  · rw [ValuationSubring.mem_nonunits_iff]
    have h := (hB ((normV v : ℕ) : 𝓞 ℚ)).mpr ((UpperTheory.V.Z.Kato.Nb.mem_place_iff v _).mpr dvd_rfl)
    simpa using h
  · have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
      rw [UpperTheory.V.Z.Kato.Nb.mem_place_iff]
      intro hd
      exact hql ((Nat.prime_dvd_prime_iff_eq hq Fact.out).mp hd)
    exact cycZ_of_isFrob hl hB ⟨hσ, hfr⟩
