module

public import Formalism.HermitianCurvature.StatementB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentComposition.Development
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.StatementFr
import Formalism.HermitianCurvature.StatementR
import Formalism.HermitianCurvature.StatementWd

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.PolyComp

open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose MvPolynomial

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ}

def scalTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, inLie k r X) : DTerm k r Wp Wq where
  coef g := P g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  coefAdj g := star (P g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
  word := w
  word_lie := hw
  adj_id := by
    intro x A B
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hsInner, PI.UnitaryGroupMassFormula.UsCompose.hsVec_smul,
      inner_smul_right, inner_smul_left, Complex.star_def, Complex.conj_conj]

end

end GlobalTheory.HatNF.PolyComp

namespace GlobalTheory.HatNF

open GlobalTheory.HatNF.PolyComp

end GlobalTheory.HatNF
