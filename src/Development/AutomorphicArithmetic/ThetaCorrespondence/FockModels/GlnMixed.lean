module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationUnconditional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.IsZSegDetRep
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
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

open GlobalTheory.PRep GlobalTheory.SmGL

namespace UpperTheory.Lit.Mix

theorem geometricLemma : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_unconditional

theorem polynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.bernsteinZelevinskyFiniteness_holds PositivityTheory.RgGu.segmentRepresentation
    (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mixed {r : ℕ} (t : ℕ) {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible :=
  UpperTheory.Lit.Full.top geometricLemma GlobalTheory.bernsteinZelevinskyFiniteness_holds polynomialRing k r t V π χ s i u hs hu

theorem prod₂_detRep' (_H : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {r : ℕ} (t : ℕ)
    {π : Representation ℂ (GL (Fin r) k) V} (s : IsSmooth π) (i : π.IsIrreducible)
    (u : IsUnitarisable π) {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    (prod₂ π (detRep (Fin t) χ)).IsIrreducible := mixed t s i u hs hu

end UpperTheory.Lit.Mix

end
