module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomInjectiveApplyOfTranscendental
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_algHom_algebraicClosure_apply_eq_pow :
    ∀ (Ω : Type) [Field Ω] (K0 : Subfield Ω) (x : Ω), Transcendental K0 x → ∀ m : ℕ, 0 < m →
      ∃ τ : Ω →ₐ[K0] AlgebraicClosure Ω, τ x = algebraMap Ω (AlgebraicClosure Ω) x ^ m := by
  intro Ω _ K0 x hx m hm
  classical
  have h1 : AlgebraicIndepOn K0 id ({x} : Set Ω) :=
    algebraicIndependent_unique_type_iff.2 hx
  obtain ⟨s, hxs, hs⟩ := exists_isTranscendenceBasis_superset h1
  let i₀ : s := ⟨x, hxs rfl⟩
  have h2 := (algebraicIndependent_update_pow hs.1 i₀ hm).map'
    (f := IsScalarTower.toAlgHom K0 Ω (AlgebraicClosure Ω))
    (algebraMap Ω (AlgebraicClosure Ω)).injective
  obtain ⟨j, hj⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hs h2
  exact ⟨j, by simpa [i₀] using hj i₀⟩

end GlobalTheory
