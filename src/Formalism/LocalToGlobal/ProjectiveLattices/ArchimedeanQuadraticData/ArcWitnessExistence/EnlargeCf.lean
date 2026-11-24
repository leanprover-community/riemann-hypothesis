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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem arcDet_ne_zero (K₁ : Type) [Field K₁] : arcDet Dw K₁ ≠ 0 := by
  unfold arcDet
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  have h : Matrix.of (fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K₁))) =
      (MvPolynomial.rename (fun p : Fin (Dw.mult τ) × Fin (Dw.mult τ) => (⟨τ, p.1, p.2⟩ : ArcLt Dw))).mapMatrix
        (Matrix.mvPolynomialX (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (LaurentSeries K₁)) := by
    ext i k; simp [Matrix.mvPolynomialX]
  rw [h, ← AlgHom.map_det]
  intro h0
  have hinj : Function.Injective (MvPolynomial.rename
      (fun p : Fin (Dw.mult τ) × Fin (Dw.mult τ) => (⟨τ, p.1, p.2⟩ : ArcLt Dw)) :
      MvPolynomial _ (LaurentSeries K₁) → MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) :=
    MvPolynomial.rename_injective _ (fun p q hpq => by
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at hpq
      exact Prod.ext (congrArg Prod.fst hpq) (congrArg Prod.snd hpq))
  exact Matrix.det_mvPolynomialX_ne_zero (Fin (Dw.mult τ)) (LaurentSeries K₁) (hinj (h0.trans (map_zero _).symm))

end Formalism.L2.Pj.QAt
