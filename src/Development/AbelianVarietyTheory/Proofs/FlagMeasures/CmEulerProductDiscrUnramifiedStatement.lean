module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

theorem _root_.GlobalTheory.T.cm_euler_product_discr_unramified : ∀ (I : AutInst) (M : ℕ), 2 ≤ M → HasProd (fun u : IsDedekindDomain.HeightOneSpectrum (𝓞 I.F) => 1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta I.F I.E u ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ M)⁻¹) (Formalism.HermitianLatticesTheory.lValEta I.E M)⁻¹ ∧ |(discr I.F : ℝ)| = (2 * Formalism.HermitianLatticesTheory.vInv I.E) ^ I.f ∧ ∀ u, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace I.F I.E u := by
  first | exact @GlobalTheory.DensityEuler.euler_product_discr_unramified | exact GlobalTheory.DensityEuler.euler_product_discr_unramified | (intros; apply GlobalTheory.DensityEuler.euler_product_discr_unramified <;> assumption)
