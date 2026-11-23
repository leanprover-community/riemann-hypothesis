module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.Mem.UnramTower

theorem unramIn_trans : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N], (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn L 𝔭) → (∀ P : HeightOneSpectrum (𝓞 L), GlobalTheory.NT.UnramIn N P) → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn N 𝔭 := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ hL hN 𝔭 σ hσ
  obtain ⟨Q, hQ, hQo, hσ⟩ := hσ
  have hσ' : ∀ x : 𝓞 N, σ • x - x ∈ Q := fun x => hσ x
  have hPo : (Q.under (𝓞 L)).LiesOver 𝔭.asIdeal := inferInstance
  have hP : (Q.under (𝓞 L)).IsPrime := inferInstance
  have h1 : σ.restrictNormal L = 1 := by
    refine hL 𝔭 _ ⟨Q.under (𝓞 L), hP, hPo, ?_⟩
    intro x
    have hx := hσ' (algebraMap (𝓞 L) (𝓞 N) x)
    have e : algebraMap (𝓞 L) (𝓞 N) ((σ.restrictNormal L) • x) = σ • algebraMap (𝓞 L) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact AlgEquiv.restrictNormal_commutes σ L (x : L)
    show (σ.restrictNormal L) • x - x ∈ Ideal.comap (algebraMap (𝓞 L) (𝓞 N)) Q
    rw [Ideal.mem_comap, map_sub, e]
    exact hx
  have hfix : ∀ y : L, σ (algebraMap L N y) = algebraMap L N y := by
    intro y
    rw [← AlgEquiv.restrictNormal_commutes σ L y, h1]
    rfl
  let τ : N ≃ₐ[L] N := { σ.toRingEquiv with commutes' := hfix }
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨Q.under (𝓞 L), hP, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have h2 : τ = 1 := by
    refine hN P τ ⟨Q, hQ, ⟨rfl⟩, ?_⟩
    intro x
    exact hσ' x
  ext y
  exact DFunLike.congr_fun h2 y

end GlobalTheory.Mem.UnramTower
