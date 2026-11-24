module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtDpsi
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomologicalOfThree
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CochainExpansions.CochainHolds
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KugaGlueHolds
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

namespace PositivityTheory.Rg.Cz

theorem clozelCohomological : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of_three whitLie_holds kugaGlue_holds Coch.cochain_holds

end PositivityTheory.Rg.Cz
