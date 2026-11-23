module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.InvMemRl
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HostConj
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

theorem linkEtaTw_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.N.LocsCoverTw (Fm.D x i) :=
  locs_cover_twists_of_hecke Fm ReciprocityTheory.ChartRestriction.L3H.heckeStd hfam

theorem linkEta_closed {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (hfam : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ (M : MtFam (Fm.D x i)) (_ : NormalizedLocalCompatibility (Fm.D x i) M),
      HeckeTied (Fm.D x i) M) :
    Formalism.MainNotions.LinkEta Fm := by
  exact linkEtaTw_closed Fm hfam

end Formalism.L2
