module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def rowsProj {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 ((U.submatrix s id).mulVec fun j => z j)


open Classical in
def VarietyProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B))

end

end GroundTheory.Heights₂.Heights
