module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import CompanionTheory.AutomorphicTheory.PlaceSeparation.IsOpenQuotientMapArt0
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

namespace PositivityTheory.Stage1.PM

theorem globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity :=
  CompanionTheory.FamInh.globalArtin

theorem rayClassFieldSt : GlobalTheory.Published.RayClassFieldSt :=
  GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt CompanionTheory.FamInh.globalArtin

theorem heckeLAdicCharacter : GlobalTheory.Published.HeckeLAdicCharacter :=
  GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter CompanionTheory.FamInh.globalArtin

end PositivityTheory.Stage1.PM
