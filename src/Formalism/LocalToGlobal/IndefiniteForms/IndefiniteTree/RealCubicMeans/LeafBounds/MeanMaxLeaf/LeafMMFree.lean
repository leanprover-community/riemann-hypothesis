module

public import Formalism.HarderNarasimhan.StatementPl
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.IndefiniteTreeX
public import Formalism.PairingDivisors.StatementH
import Formalism.PairingDivisors.StatementN
public import Formalism.PairingDivisors.StatementX
import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

noncomputable section

open NumberField
open IsDedekindDomain
open Finset
open Formalism.PairingDivisionLocalBalance (Pl wt HtLe meanInf)
open Formalism.HN (muMaxDef htMap)
open Formalism.DivisionValues
open Formalism.L2.Indef
open Formalism.L2.Indef.Tree

namespace Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

def TestLatticeCondition {K : Type} [Field K] [NumberField K] [StarRing K] (n : ℕ) (X' : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (M : Submodule (𝓞 K) (Fin n → K)) (E : ℝ) : Prop :=
  M.FG ∧ M ≠ ⊥ ∧ (∀ v, IsUnit (X' v).det) ∧ muMaxDef (Pi.basisFun K (Fin n)) X' M ≤ E

end Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
