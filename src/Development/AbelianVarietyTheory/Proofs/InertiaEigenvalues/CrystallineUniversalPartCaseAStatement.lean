module

public import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.crystallineUniversalPart_caseA : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmUnivA D HW F Cm → DeltaInvariantLattices.P9 D HW F → LiftingTheory.ConclusionH D HW F → TruncatedSeriesCountingBounds.adm15 D → UnusedSlot80.UniversalComponentCaseA D HW F Cm := by
  first | exact @GlobalTheory.universalPart_caseA | exact GlobalTheory.universalPart_caseA | (intros; apply GlobalTheory.universalPart_caseA <;> assumption)
