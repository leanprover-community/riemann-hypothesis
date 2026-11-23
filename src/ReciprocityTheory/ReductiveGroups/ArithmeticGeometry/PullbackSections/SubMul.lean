module

public import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

def LieFacAddSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (x : ℝ)
    (a a' : (E →+* ℂ) × ℕ → ℕ), lieFac Dw x (a + a') = lieFac Dw x a * lieFac Dw x a'

def PnormMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la la' : Wt X.Ψ r)
    (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r), x ∈ X.dom →
      X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x

def SupCMulSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (σ : c.F →+* ℂ)
    (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), GoodEmb c σ → Even n → Even n' →
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ → supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) ≠ ⊤ →
      supC Xo c U x σ (a + a') (n + n') (f * g) ≤ supC Xo c U x σ a n f * supC Xo c U x σ a' n' g

def RecSubMulSt : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul (recPJ h j hj)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
