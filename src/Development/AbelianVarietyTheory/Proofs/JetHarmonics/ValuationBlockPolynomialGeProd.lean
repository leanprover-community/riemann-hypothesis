module

public import Formalism.LocalToGlobal.ProjectiveLattices.CrudeMin
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Integers
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem valuation_blockPoly_ge : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (Ty : Type) [Fintype Ty] [DecidableEq Ty] (r : Ty → ℕ) (n : ℕ) (β : (Σ τ : Ty, Fin (r τ)) → Fin n), Function.Injective β → ∀ (a : Ty → ℕ → ℕ), Crude.Dom r a → ∀ (yv : Letter Ty r n → O) (x : Ty → NNReal), (∀ τ, x τ ≤ 1) → (∀ τ (i : Fin (r τ)), x τ ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => yv ⟨τ, Fin.castLE i.isLt a, β ⟨τ, Fin.castLE i.isLt b⟩⟩).det)) → (∏ τ, x τ ^ (a τ 0) ≤ v (algebraMap O C (MvPolynomial.eval yv (Crude.crP r n O β a)))) ∧ ∀ mo ∈ (Crude.crP r n O β a).support, ∀ ℓ, mo ℓ ≠ 0 → ∃ i, β ⟨ℓ.1, i⟩ = ℓ.2.2 := by
  intro C _ v O _ _ _ Ty _ _ r n β _ a ha yv x hx hmin
  refine ⟨?_, fun mo hmo ℓ hℓ => ?_⟩
  · unfold Crude.crP
    rw [map_prod, map_prod, map_prod]
    refine Finset.prod_le_prod' fun τ _ => ?_
    rw [map_prod, map_prod, map_prod]
    have h1 : x τ ^ (a τ 0) ≤ ∏ kk : Fin (r τ), x τ ^ Crude.crExp r a τ kk := by
      rw [Finset.prod_pow_eq_pow_sum]
      refine pow_le_pow_of_le_one zero_le (hx τ) ?_
      rcases Nat.eq_zero_or_pos (r τ) with h0 | h0
      · haveI : IsEmpty (Fin (r τ)) := by rw [h0]; infer_instance
        simp
      · have := Crude.crExpSum a ha τ ⟨0, h0⟩
        simp only [Nat.zero_lt_succ, if_true] at this
        exact this.le
    refine h1.trans (Finset.prod_le_prod' fun kk _ => ?_)
    rw [map_pow, map_pow, map_pow]
    refine pow_le_pow_left₀ zero_le ?_ _
    have h2 : MvPolynomial.eval yv (Crude.crMinor r n O β τ kk).det =
        (Matrix.of fun a b : Fin (kk.val + 1) =>
          yv ⟨τ, Fin.castLE kk.isLt a, β ⟨τ, Fin.castLE kk.isLt b⟩⟩).det := by
      rw [RingHom.map_det]
      congr 1
      ext i j
      simp [Crude.crMinor, RingHom.mapMatrix_apply]
    rw [h2]
    exact hmin τ kk
  · exact MvPolynomial.mem_supported.1 (Crude.crP_mem_supported O β a)
      ((MvPolynomial.mem_vars_iff_mem_support ℓ).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hℓ⟩)

end GlobalTheory.CharDepth
