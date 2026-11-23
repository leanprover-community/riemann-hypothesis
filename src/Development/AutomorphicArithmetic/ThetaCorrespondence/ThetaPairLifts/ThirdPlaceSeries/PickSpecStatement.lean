module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PickSpec
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_galois_rep_family_bounded_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    GalEx D → RowCusp D A.row → GlobalTheory.RowTie.ChebSplit D.nd → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ c1 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c1 l j).1 ≤ (b0 l j).1) →
      ∃ rho : RhoFam D T, (∀ i σ b, Continuous fun g =>
          ((rho i σ b g : GL (Fin D.R.r) (T.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (T.O0 i))) ∧
        ∀ i σ b, (∃ j, 1 ≤ j ∧ j ≤ D.R.m ∧ D.what₂.isot j σ ≠ ⊥) → D.nd.goodRow σ →
        ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = A.row.locR σ w) →
        ∀ (φ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
          (∀ z : ℤ_[T.l i], φ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
            algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) →
          (∀ x : ↥D.LL0, ι (φ ((if b then T.emb0 i else T.emb0b i) x)) = embLL0 D x) →
          IsRepOf D (T.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
            (mapRep (φ.comp (algebraMap (T.O0 i) (FractionRing (T.O0 i)))) (rho i σ b)) := by
  first | exact @_root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt | exact _root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt | (intros; apply _root_.GlobalTheory.HeightCounting.RowRhoInt.rho_rows_alt <;> assumption)
end
