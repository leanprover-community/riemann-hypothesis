module

public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

theorem _root_.GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : GenLat E n), Λ.Unimod → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = J • Submodule.span (𝓞 E) (detSet Λ.La) ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = Submodule.map (Algebra.linearMap (𝓞 E) E) (conjI J) ∧ ∀ h : Matrix (Fin n) (Fin n) E, Submodule.span (𝓞 E) (detSet (actLat h Λ).La) = Submodule.map (LinearMap.mulLeft (𝓞 E) h.det) (Submodule.span (𝓞 E) (detSet Λ.La)) := by
  first | exact @GlobalTheory.DetIdeal.detIdeal_selfDual | exact GlobalTheory.DetIdeal.detIdeal_selfDual | (intros; apply GlobalTheory.DetIdeal.detIdeal_selfDual <;> assumption)
