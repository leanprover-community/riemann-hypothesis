module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.inertPrime_not_dvd_relIndex_splitPlace : ∀ (D : D7) (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ Λ Λ' : AddSubgroup (WO S T), (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) → (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ', a • u ∈ Λ') → (∀ u ∈ Λ', u.map (infPart D) = 0) → (∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) → Λ.relIndex Λ' ≠ 0 → ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ Λ.relIndex Λ' := by
  first | exact @GlobalTheory.SplitIndex.not_dvd_relIndex | exact GlobalTheory.SplitIndex.not_dvd_relIndex | (intros; apply GlobalTheory.SplitIndex.not_dvd_relIndex <;> assumption)
