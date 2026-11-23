module

public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Formalism.SharpRestriction.ParConsts
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
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
import Formalism.LocalToGlobal.PtKOfReal

@[expose] public section

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S

namespace Formalism.L2.Top4Wire2

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel}
  {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel}

abbrev NumFactsAt {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x) (Del h0 : ℕ) (lam0 C0 ce Sw C1 : ℝ) : Prop :=
  ∀ u, (ofRecord (Fm.D x i) (Fm.L x i) Del h0).NumFacts (letterOf (Fm.D x i) (Fm.L x i) Del h0 u) (Fm.L x i).Nc lam0 C0 ce Fm.Csz Sw C1

end Formalism.L2.Top4Wire2

end
