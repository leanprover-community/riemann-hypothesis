module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionBlockEmb
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ContractionOfPairingLemmas
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsP
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetYNeZero
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ExplicitMapOntoTwoLetterSpace
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.InitialMinorLiftFirstEntry
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaNuNextAdd
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubCoeffP
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYDPsiMonomial
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TheoremIOfTwoLetterClausesContraction
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TopLinePOf
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TwoLetterLatticeGaussInverse
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
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DerivativeRepresentation

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem qPh_of_rest (hTau : TauP) (hSm : SmithP) : QPh :=
  qPh_of hTau hSm bilinP detFactsP numP detDivP

theorem contraction_of_pairing_GL (hPh : QPh) (hCO : CartanOnto) : ContractionStandardLattice :=
  contraction_of_pairing_lemmas hPh subCoeffP subMapP subRowP lamCoeffP lamEquivP lamMulP lamEvalP lamMemP
    (subMuP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) (topLineP_of explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hCO) liftP detDivP intCapP hwMulP

theorem theorem_I_of_contraction (D : Formalism.BasicNotions.D7) (hQ : ContractionStandardLattice) : SecondPartClosed D :=
  theorem_I_of_two_letter_clauses_contraction D explicit_map_injective explicit_map_onto_two_letter_space two_letter_lattice_gauss_inverse hQ

theorem theorem_I_of_pairing_GL (D : Formalism.BasicNotions.D7) (hPh : QPh) : SecondPartClosed D := by
  intro hA
  obtain ⟨T0, -, h0⟩ := hA 0 le_rfl
  obtain ⟨T1, -, h1⟩ := h0 T0 le_rfl
  obtain ⟨T2, -, h2⟩ := h1 T1 T1 T1 le_rfl le_rfl le_rfl
  obtain ⟨CA, Ckap, Ct, Cs, -, -, -, -, hB⟩ := h2 T2 le_rfl
  have hT : AdmT D := hB.2.2.2.2
  have h11 : GradedLatticeStable D := hT.2.2.2.2.2.2.1
  exact theorem_I_of_contraction D (contraction_of_pairing_GL hPh h11.2) hA

end Formalism.MainNotions.flipOneThree.Pf
