module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SymbolFormOfOrthogonality
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BlockForm
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFCoarse
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFTrueDeg
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockEqSum
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

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

theorem symbol_form_of_block_parts {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hK : RestKapNum) (hO : RestOPlus) : RestForm :=
  symbol_form_of_orthogonality (restBlockForm_of h52 hK) orthAt hO

theorem restKapNum_of {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hO : RestOPlus) : RestKapNum := by
  unfold RestKapNum TransportedAlt
  unfold RestOPlus TransportedAlt at hO
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := hO Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm hE1 hE2 hCm => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 Cm hE1 hE2 hCm
  refine ⟨T2, hT2, fun CYb Cde Ck CD Cb ha hb hc hd he => ?_⟩
  have hOP := h2 CYb Cde Ck CD Cb ha hb hc hd he
  exact kapNumAt_of h52 (trueDegAt_of hOP) (coarseMultAt_of hOP)

theorem restForm_of_oplus {D : Formalism.BasicNotions.D7} (h52 : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) (hO : RestOPlus) : RestForm :=
  symbol_form_of_block_parts h52 (restKapNum_of h52 hO) hO

end Formalism.MainNotions.ColumnSystems.Pf
