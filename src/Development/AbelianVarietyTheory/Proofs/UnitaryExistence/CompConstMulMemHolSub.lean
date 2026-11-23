module

public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompRat

namespace GlobalTheory.CompRat

theorem const_of_idem_on {Y : Type} [TopologicalSpace Y] {s : Set Y} (hs : IsPreconnected s) {g : Y → ℂ}
    (hg : ContinuousOn g s) (hi : ∀ x ∈ s, g x * g x = g x) : ∃ w : ℂ, ∀ x ∈ s, g x = w := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact ⟨0, fun _ h => h.elim⟩
  refine ⟨g x0, fun x hx => ?_⟩
  have hfin : (g '' s).Finite := by
    refine (Set.toFinite ({0, 1} : Set ℂ)).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    have h := hi y hy
    have : g y * (g y - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  exact hs.constant_of_mapsTo hfin.isDiscrete hg (Set.mapsTo_image g s) hx hx0

theorem rdU_mul_apply' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (f f' : Rul Xo c) (k : U.Comp) (x : Frame (U.X k).Ψ r) :
    rdU U (f * f') k x = rdU U f k x * rdU U f' k x := by
  by_cases h : x ∈ (U.X k).dom
  · have e1 : ∀ g : Rul Xo c, rdU U g k x = toC (evR Xo c g (U.un k ⟨x, h⟩)) := fun g => dif_pos h
    rw [e1, e1, e1]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f f' (U.un k ⟨x, h⟩)
  · rw [rdU_mem_offZero U _ k x h, rdU_mem_offZero U f k x h, zero_mul]

end GlobalTheory.CompRat
