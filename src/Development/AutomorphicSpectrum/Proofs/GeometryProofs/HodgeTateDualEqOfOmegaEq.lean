module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIntegralAdeleLimitCompatibleIntSystem
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem htDual_htW_relabel : ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (L : LB G.left) (L' : LB G'.left) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (M' : LieModel G' ξ V) (n n' : ℕ) (ρ : 𝓞 E →+* Module.End Ω V) (τ : 𝓞 E →+* Ω) (q : Cpt ξ), M'.htOm L' n' q = M.htOm L n q → M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q ∧ M'.htW L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) (differentIdeal ℤ (𝓞 E)) q = M.htW L n ρ τ (differentIdeal ℤ (𝓞 E)) q := by
  intro E _ _ s X Ω _ ξ G G' _ _ L L' V _ _ M M' n n' ρ τ q h
  have hE : eigSp (ρ.comp s.toRingHom) (τ.comp s.toRingHom) = eigSp ρ τ :=
    eigSp_comp_ringEquiv Ω V (𝓞 E) ρ s τ
  have h1 : M'.htDual L' n' (ρ.comp s.toRingHom) (τ.comp s.toRingHom) q = M.htDual L n ρ τ q := by
    unfold LieModel.htDual
    rw [hE, h]
  refine ⟨h1, ?_⟩
  unfold LieModel.htW
  rw [hE, h1]
  congr 1
  ext e
  constructor
  · rintro ⟨he, H⟩
    refine ⟨he, fun d hd => ?_⟩
    have hd' : s.symm d ∈ differentIdeal ℤ (𝓞 E) :=
      (GlobalTheory.T.different_ideal_automorphism_invariant E s (s.symm d)).1 (by simpa using hd)
    simpa using H _ hd'
  · rintro ⟨he, H⟩
    exact ⟨he, fun d hd => H _ ((GlobalTheory.T.different_ideal_automorphism_invariant E s d).2 hd)⟩

end GlobalTheory.CompanionTheory.Ar
