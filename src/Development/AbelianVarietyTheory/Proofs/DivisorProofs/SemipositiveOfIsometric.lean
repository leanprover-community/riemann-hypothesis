module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts

namespace GlobalTheory

namespace HermLB

theorem Isometric.semiPos : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    (L M : GlobalTheory.HermLB p) (D : ℕ), L.Isometric M → L.SemiPos D → M.SemiPos D := by
  intro k _ X p L M D h hL σ a c y hy ξ
  have hb := mem_pick (L.φ σ).isLB y
  have hL' := hL σ _ c y ⟨hy.1, hb⟩ ξ
  have e := h.hess_eq c hy.1 hy.2 hb
  have hM : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((M.φ σ).φ a (c.e.symm v) : ℂ)) (c.e y) ξ =
      ∑ j, ∑ l, c.hess (M.φ σ) a y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  have hL₂ : ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((L.φ σ).φ (pick (L.φ σ).isLB y) (c.e.symm v) : ℂ))
      (c.e y) ξ = ∑ j, ∑ l, c.hess (L.φ σ) (pick (L.φ σ).isLB y) y j l * ξ j * (starRingEnd ℂ) (ξ l) := rfl
  rw [hM, e, ← hL₂]
  exact hL'

end HermLB

end GlobalTheory
