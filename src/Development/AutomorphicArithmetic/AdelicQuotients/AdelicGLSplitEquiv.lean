module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.adelicGL_split_equiv :
    SplitEquiv := by
  intro G₁ R G _ _ _ _ _ _ _ i d c hi hd hc hs hcomm hk
  have hd1 : ∀ x, d (i x) = 1 := fun x => (hk _).2 ⟨x, rfl⟩
  have h : ∀ g, ∃ x, i x = g * (c (d g))⁻¹ := fun g => by
    have h1 : d (g * (c (d g))⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    exact (hk _).1 h1
  choose f hf using h
  have hfc : Continuous f := by
    refine hi.continuous_iff.2 ?_
    have h2 : (i ∘ f) = fun g => g * (c (d g))⁻¹ := funext hf
    rw [h2]
    exact continuous_id.mul (hc.comp hd).inv
  let E : G₁ × R ≃* G :=
    { toFun := fun x => i x.1 * c x.2
      invFun := fun g => (f g, d g)
      left_inv := by
        rintro ⟨x, r⟩
        have hdr : d (i x * c r) = r := by rw [map_mul, hd1, hs, one_mul]
        refine Prod.ext (hi.injective ?_) hdr
        show i (f (i x * c r)) = i x
        rw [hf, hdr, mul_inv_cancel_right]
      right_inv := by
        intro g
        show i (f g) * c (d g) = g
        rw [hf, inv_mul_cancel_right]
      map_mul' := by
        rintro ⟨x, r⟩ ⟨y, s⟩
        show i (x * y) * c (r * s) = i x * c r * (i y * c s)
        rw [map_mul, map_mul, mul_assoc (i x) (c r), ← mul_assoc (c r), hcomm r (i y)]
        simp only [mul_assoc] }
  exact ⟨{ E with
    continuous_toFun := (hi.continuous.comp continuous_fst).mul (hc.comp continuous_snd)
    continuous_invFun := hfc.prodMk hd }, fun x => rfl⟩
