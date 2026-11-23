module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocVanishOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMemUniRad
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalChangeOfVariables
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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

open MeasureTheory

namespace PositivityTheory.Rg.BcB.CV

theorem quotVanishL : GlobalTheory.CompanionTheory.LocVan.QuotVanish := by
  intro n _ _ μ _ d μd _ W₁ W₂ hs _ hW h1 h2 F hF hT hK h0
  letI : MeasurableSpace (nilrad W₁ W₂) := borel _
  haveI : BorelSpace (nilrad W₁ W₂) := ⟨rfl⟩
  haveI : LocallyCompactSpace (nilrad W₁ W₂) := (nilrad W₁ W₂).closed_of_finiteDimensional.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine GlobalTheory.CompanionTheory.QuotVan.quotVanish n μ d μd W₁ W₂ hW Measure.addHaar F hs h1 h2 hF hT hK fun q _ => ?_
  simp only [GlobalTheory.CompanionTheory.QuotVan.uOf_eq]
  exact h0 _ q

theorem locVanish : LocVanish := GlobalTheory.CompanionTheory.LocVan.locVanish_of GlobalTheory.CompanionTheory.LocVan.nilChange_of_flag quotVanishL

end PositivityTheory.Rg.BcB.CV
