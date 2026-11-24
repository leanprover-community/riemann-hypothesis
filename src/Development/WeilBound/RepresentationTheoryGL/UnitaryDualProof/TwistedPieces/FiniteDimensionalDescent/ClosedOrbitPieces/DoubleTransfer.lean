module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.DoubleTransferAlt
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
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
import Mathlib.Data.Nat.Choose.Multinomial
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

noncomputable section

open PositivityTheory.PfBern.Frob PositivityTheory.RgUd.TP.Desc.Piece.Tr

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrDbl

theorem doubleTransfer : FrobeniusReciprocity → DoubleTransfer := by
  intro hF G _ _ _ _ _ _ _ _ _ H₁ H₂ _ _ hH₁ hH₂ hG hU₁ hU₂ X _ _ _ _ _ _ p₁ p₂ hc₁ hc₂ hp₁ hp₂ C hC hCinv hE₂ E hE
  obtain ⟨Fr₁, hs₁, -⟩ := hF G H₁ hH₁ hG hU₁ X p₁ hc₁ hp₁ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  obtain ⟨Fr₂, hs₂, -⟩ := hF G H₂ hH₂ hG hU₂ X p₂ hc₂ hp₂ 1 continuous_const
    (MeasureTheory.Measure.haar) (MeasureTheory.Measure.haar)
  set ξ := Fr₁.symm ⟨E, hE⟩
  have h2 : SupportedIn (↑ξ) C := (hs₂ ξ C hC hCinv).2 (hE₂ _ (Fr₂ ξ).2)
  have h1 := (hs₁ ξ C hC hCinv).1 h2
  simpa [ξ] using h1

end PositivityTheory.RgUd.TP.Desc.Piece.TrDbl
