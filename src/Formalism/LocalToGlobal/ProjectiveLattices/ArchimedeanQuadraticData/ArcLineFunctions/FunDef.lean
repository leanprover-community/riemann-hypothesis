module

public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
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

@[expose] public section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

noncomputable def arcNum {K₁ : Type} [Field K₁] (s : ArcS Dw K₁) :
    MvPolynomial (ArcLt Dw) (LaurentSeries K₁) := by
  classical
  exact if h : ∃ P, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) P = s
    then h.choose else 0

variable {Xo : Moduli Dw l} {c : Coeff l}

noncomputable def cfOf {K₁ : Type} [Field K₁] [Algebra c.F (ArcS Dw K₁)]
    (yF : FrPt Xo c (ArcS Dw K₁)) (μ : ArcLt Dw →₀ ℕ) (j : ℤ) (F : Rul Xo c) : K₁ :=
  (AddMonoidAlgebra.coeff (arcNum (evR Xo c F yF)) μ).coeff j

end Formalism.L2.Pj.QAt
