module

public import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.FinalP
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.FactSplit
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.IndexWeightsDominance
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.JacobiMinorProof
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LemmaA2indepOf
import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.PathBasisOfCount
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top

open Formalism.InvariantFactorPaths.GelfandTsetlinBases

theorem psiWeight : PsiWeight := psi_weight
theorem fact_index_weights : IndexWeightsDominance := index_weights_dominance
theorem polBRank : PolBRank := polynomial_b_rank
theorem pathIdxFinite : PathIdxFinite := path_index_finite
theorem factBrk : FactBrk := fact_break
theorem factEV : FactEV := factEV_of fact_index_weights psiWeight
theorem lemmaA2indep : LemmaA2indep := lemmaA2indep_of factEV factBrk
theorem path_basis_theorem : PathBasisOfCount := path_basis_of_count lemmaA2indep pathIdxFinite polBRank

theorem psiPath_basis (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (R : Type) [CommRing R] :
    LinearIndependent R (fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) ∧
      Submodule.span R (Set.range fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) =
        polB R n N B := path_basis_theorem n N isVec B (countPAll n N isVec B) R
theorem factSplit : FactSplit := factSplit_valid

end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top
