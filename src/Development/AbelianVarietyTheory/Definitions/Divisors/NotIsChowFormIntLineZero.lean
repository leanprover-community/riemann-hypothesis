module

public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.Test

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal


set_option autoImplicit false in
open MvPolynomial NumberField IsDedekindDomain Module Filter in
open scoped ENNReal in
theorem _root_.GlobalTheory.CompHt.Test.imageDeg_zero {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Field Ω] [Algebra K Ω] (D : ℕ) :
    _root_.GlobalTheory.CompHt.imageDeg (0 : V →ₗ[K] Ω) D = 0 := by
  by_contra hne
  obtain ⟨N, b, f, hf⟩ := (_root_.GlobalTheory.CompHt.imageDeg_pos_iff _ D).1 (Nat.pos_of_ne_zero hne)
  obtain ⟨y, hy, hI⟩ := hf.exists_point
  apply hy
  funext i
  have hX : (X i : MvPolynomial (Fin N) K) ∈ _root_.GlobalTheory.CompHt.imageIdeal (0 : V →ₗ[K] Ω) b := by
    unfold _root_.GlobalTheory.CompHt.imageIdeal
    rw [_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous _ (isHomogeneous_X K i)]
    simp
  simpa using hI _ hX

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end GlobalTheory.CompHt.Test
