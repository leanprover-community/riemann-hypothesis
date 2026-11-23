module

public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.HeckeStdStatement
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverF
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverSplit
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdL
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions NumberField

namespace Formalism.L2

theorem linkEtaTw_main {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ReciprocityTheory.ChartRestriction.L3H.HeckeStdStatement)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M ∧ ∀ z : (Fm.D x i).host.E, (Fm.D x i).host.conj z = IsCMField.complexConj _ z) :
    LocsCoverTwF Fm := by
  obtain ⟨x0, hx⟩ := hfam
  refine linkEtaTw_of_statement Fm h ⟨x0, fun x hx' i => ?_⟩
  obtain ⟨M, T, HT, hstar⟩ := hx x hx' i
  exact ⟨M, T, HT, splitEx_of_star hstar⟩

end Formalism.L2
