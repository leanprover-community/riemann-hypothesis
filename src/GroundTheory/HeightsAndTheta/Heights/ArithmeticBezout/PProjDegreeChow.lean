module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjDegreeChow
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDomain
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjChowNonzero
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeLe
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSecDegreeGe
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem ProjDegreeChow.proof (h₁ : ProjSecDegree.Statement) (h₂ : ProjSecDomain.Statement)
    (h₃ : ProjChowNonzero.Statement) (h₄ : SecDegreeLe.Statement) (h₅ : SecDegreeGe.Statement) :
    ProjDegreeChow.Statement := by
  intro n e δ W f A hW hf hδ hA
  rw [h₁ n e W A]
  obtain ⟨hdom, hfin⟩ := h₂ n e W A hW.isPrime hA
  have hc := h₃ n e W f A hW hf hA
  have hsep : Algebra.IsSeparable (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
      (Vertical.SecAlg
        (W.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
        (projPar A)) :=
    ⟨fun x => PerfectField.separable_of_irreducible
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral x))⟩
  refine le_antisymm (h₄ ℂ _ n e δ W f (projPar A) hW hf hδ hfin hdom hsep fun h => hc ?_)
    (h₅ ℂ _ n e δ W f (projPar A) hW hf hδ hc).2
  rw [h, map_zero]

end

end GroundTheory.Heights₂.Heights
