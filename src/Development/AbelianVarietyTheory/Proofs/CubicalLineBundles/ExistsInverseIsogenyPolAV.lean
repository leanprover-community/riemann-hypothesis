module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsogenyOfSurjectivePolAV
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory

theorem exists_inverse_isogeny_polAV : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp K)) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → Surjective Φ.left → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hU hL K _ σ P P' Φ hg hΦ hs
  obtain ⟨hf, hfl, n, hn, hk⟩ := isogeny_of_surjective_polAV hU hL K σ P P' Φ hg hΦ hs
  have := P.isAb.comm
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 P.A ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit P.A ≫ η[P.A]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 P.A ^ m) (𝟙 P.A) ≫ μ[P.A]))
  have hm := hpow n
  obtain ⟨⟨ψ, hψ, e⟩, hE⟩ := exists_monHom_factor_of_flat_surjective _ P.A P'.A P.A Φ (𝟙 P.A ^ n) hΦ hm hfl hs inferInstance
    (fun T x hx => by rw [MonObj.comp_pow, Category.comp_id, hk T x hx])
  refine ⟨n, ψ, hn, hψ, e, ?_⟩
  rw [← cancel_epi Φ, reassoc_of% e, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
    Category.comp_id]

end GlobalTheory
