module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBoundStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TermSumBoundOfPairsAmplitudeStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.Core.Deg

theorem vanishingGramBoundWindow_of_termPairTypeBound (hT : GlobalTheory.TypeAsm.TypeP) : VanishingGramTermsBoundWindow := by
  intro Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨CH, Ch, Cp, hCH, hCh, hCp, H⟩ := hT Cg cb Cu cT CT C0 hcb hcT
  obtain ⟨C₀, H2⟩ := H (Cp + 4) le_rfl
  obtain ⟨C'₀, Cl₀, H3⟩ := H2 (max C₀ (2 * (CH + 1))) (le_max_left _ _)
  obtain ⟨Cl₁, H4⟩ := GlobalTheory.T.pairsAmplitudeBound_of_typeBound CH Ch Cp (max C₀ (2 * (CH + 1))) hCH hCh hCp (le_max_right _ _)
  refine ⟨max C'₀ 1, max Cl₀ Cl₁, fun C' Cl hC' hCl D large₂ X Y _ _ u hTies _ h0 hC hAbs => ?_⟩
  have hK2 : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 :=
    Formalism.MainNotions.NonGenericAndKTwoTheorems.Hyp_of D large₂ C' Cl Cg cb Cu cT CT C0 h0.2.1 h0.1 h0.2.2 ((le_max_right _ _).trans hC')
  have hType := H3 C' Cl ((le_max_left _ _).trans hC') ((le_max_left _ _).trans hCl) D large₂ X Y u hTies hK2 hC
  have hPairs := H4 C' Cl Cg cb Cu cT CT C0 D large₂ X Y u ((le_max_right _ _).trans hCl) hK2 hC hType
  exact GlobalTheory.T.deg_termSumBoundOfPairsAmplitude C' Cl Cg cb Cu cT CT C0 D large₂ X Y u hK2 hC hAbs hPairs

end GlobalTheory.Core.Deg
