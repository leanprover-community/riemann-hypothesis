module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtWeights
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

theorem _root_.GlobalTheory.T.exists_weight_data_integral_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE),
    (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) →
    ∃ c2 : Big D, ∀ (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
      (∀ (l : ℕ) [Fact l.Prime] j, (c2 l j).1 ≤ (b0 l j).1) →
      ∃ wt : WtData D T, ∀ i j b (hj : 1 ≤ j) (hjm : j ≤ D.R.m),
        (wt.rhoW i j b).IsIrreducible ∧ NX.IsAlgWeightF D.host.E D.R.nV (FractionRing (T.O i)) (wt.rhoW i j b) ∧
        (∀ k, (rhoKT D T wt i j b k).IsIrreducible) ∧
        (∀ t, ∃ lam : Fin D.R.nV → ℤ, NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam) ∧
        ∀ (t : D.what₂.Tau) (sh : ℂ) (lam : Fin D.R.nV → ℤ),
          D.naut.infG D.naut.etaT (embT D t) = {sh} → NX.HWAtF (NX.cE D) (wt.rhoW i j b).dual (kEmbT D T i b t) lam →
          NG.infOf lam = NG.paramV D.R (D.hc t) ⟨j - 1, by omega⟩ sh := by
  first | exact @_root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | exact _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt | (intros; apply _root_.GlobalTheory.HeightCounting.FormsStep.wt_weights_alt <;> assumption)
end
