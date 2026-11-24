module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.Development
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.DualOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bock
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.SecMapZero
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.Geo
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge Formalism.Per6 DeRhamPotentiallySemistable.DRPst

namespace CrystallineSemistableComparison

theorem zIn (h : FormalIn) (h4 : GlobalTheory.EtC.E4) (h8 : GlobalTheory.EtC.E8) : ZIn :=
  ⟨h.a6nat, h.a6ring, h.a9, h.et.a11, h4, h8, bock h, root h, sum h⟩

theorem etSide : EtaleSideSmoothAndSemistable := fun h l _ K _ =>
  ⟨adic h l K _ (fun _ hM => hM.1) (comp l K).1 fun M hM => geo l K M hM.1,
    adic h l K _ (fun _ hM => hM) (comp l K).2 fun M hM => geo l K M hM⟩

structure Chapters : Prop where
  rin : ∀ (l : ℕ) [Fact l.Prime], E.RIn l
  et : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), E.EtMap l K
  uniq : E.FirstChernUniqueEtale
  main : ∀ (l : ℕ) [Fact l.Prime], B.Main l
  compat : ∀ (l : ℕ) [Fact l.Prime], B.Compat l
  compatH : ∀ (l : ℕ) [Fact l.Prime], B.CompatH l
  c1 : ∀ (l : ℕ) [Fact l.Prime], B.FirstChernCompatible l
  p : BocksteinBaseChangeP

def CstSmooth : Prop := SmoothModelCrystalline ∧ DeRhamComparisonSmooth ∧ CrysPhi

end CrystallineSemistableComparison
