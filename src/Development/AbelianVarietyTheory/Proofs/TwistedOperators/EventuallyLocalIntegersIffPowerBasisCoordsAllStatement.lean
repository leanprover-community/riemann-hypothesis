module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyLocalIntegersIffPowerBasisCoordsAll
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.eventually_localIntegers_iff_powerBasisCoords_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P, y ∈ intLoc F (Fld P) v ↔ GlobalTheory.TrUnitLat.coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v := by
  first | exact @GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all | exact GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all | (intros; apply GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all <;> assumption)
