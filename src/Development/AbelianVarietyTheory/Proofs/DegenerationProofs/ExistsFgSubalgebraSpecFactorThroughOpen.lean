module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_fg_subalgebra_spec_factors_open (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (R : Subalgebra o Ω) (hR : R.FG) (V : (Sp R).Opens) (hV : (V : Set (Sp R)).Nonempty) :
    ∃ (R' : Subalgebra o Ω) (h : R ≤ R'), R'.FG ∧
      ∃ τ : Sp R' ⟶ V.toScheme, τ ≫ V.ι = spMap (Subalgebra.inclusion h).toRingHom := by
  classical
  obtain ⟨x, hx⟩ := hV
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfV⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
      (a := x) (u := (V : Set (Sp R))) hx V.isOpen
  have hf0 : (f : Ω) ≠ 0 := by
    intro h0
    have : f = 0 := Subtype.ext h0
    subst this
    exact hxf (Ideal.zero_mem _)
  let R' : Subalgebra o Ω := R ⊔ Algebra.adjoin o (({(f : Ω)⁻¹} : Finset Ω) : Set Ω)
  have h : R ≤ R' := le_sup_left
  have hinv : (f : Ω)⁻¹ ∈ R' :=
    (le_sup_right : _ ≤ R') (Algebra.subset_adjoin (by simp))
  refine ⟨R', h, hR.sup (Subalgebra.fg_adjoin_finset _), ?_⟩
  have hu : IsUnit ((Subalgebra.inclusion h).toRingHom f) :=
    IsUnit.of_mul_eq_one (⟨(f : Ω)⁻¹, hinv⟩ : R') (Subtype.ext (mul_inv_cancel₀ hf0))
  refine ⟨IsOpenImmersion.lift V.ι (spMap (Subalgebra.inclusion h).toRingHom) ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨y, rfl⟩
  apply hfV
  intro hm
  exact y.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)

end GlobalTheory
