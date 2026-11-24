module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radConj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (ζ β : Ω) (σ : Ω ≃+* Ω) (k : ZMod n) (φ φ' : U → ZMod n), ζ ^ n = 1 → σ ζ = ζ ^ k.val → IsRad ζ U φ β →
    (∀ u' : U, ∃ u : U, (∀ x, u'.1 (σ x) = σ (u.1 x)) ∧ φ' u' = k * φ u) → IsRad ζ U φ' (σ β) := by
  intro F Ω _ _ _ _ _ U n _ ζ β σ k φ φ' hζ hσ hβ h
  refine ⟨fun h0 => hβ.1 (σ.injective (by rw [h0, map_zero])), fun u' => ?_⟩
  obtain ⟨u, hu, hφ⟩ := h u'
  rw [hu β, hβ.2 u, map_mul, map_pow, hσ, hφ, ZMod.val_mul, ← pow_mul, ← pow_eq_pow_mod _ hζ]
