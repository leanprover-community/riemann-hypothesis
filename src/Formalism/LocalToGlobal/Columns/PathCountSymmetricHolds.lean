module

public import Formalism.LocalToGlobal.Columns.CardFilterNeighboursEqPaths
public import Formalism.LocalToGlobal.Columns.CardPathsEqSubmodulePairs
public import Formalism.LocalToGlobal.Columns.MemOfSmulMemOfAddEqOne
public import Formalism.LocalToGlobal.Columns.NeighbourConjOfTopNeighbour
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem pathCount_symmetric_holds : DecorationPathSymmetry E n ST SG := by
  intro P Q hP hQ hSTP hSGP hSTQ hSGQ i j d f
  by_cases hQP : Q = P
  · subst hQP
    exact pathCount_symm_same_prime Q hP hSTP hSGP i j d f
  by_cases hQP' : Q = conjPrime₂ P
  · subst hQP'
    exact pathCount_conj_symm (P := P) hP hSTP hSGP (fun i j d f => pathCount_symm_same_prime P hP hSTP hSGP i j d f) i j d f
  exact pathCount_symm_distinct P Q hP hQ hQP hQP' hSTP hSGP hSTQ hSGQ i j d f

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S : GSD K}

theorem heckeOperators_commute (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : HeckeComm c S0 :=
  heckeComm_of_paths c S0 pathCount_symmetric_holds

end Formalism.L2.Col
