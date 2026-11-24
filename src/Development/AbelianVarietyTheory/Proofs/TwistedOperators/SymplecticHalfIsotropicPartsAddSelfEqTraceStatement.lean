module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticHalfIsotropicPartsAddSelfEqTrace
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.symplecticHalf_isotropicParts_add_self_eq_trace : ∀ (D : D7) (V W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → ∀ u y : Mx D W.rank r, symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) + symplOH V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y) = Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (HMul.hMul (GlobalTheory.MixModel.adj y) (HMul.hMul (GlobalTheory.MixModel.gA W) u)).trace) := by
  first | exact @GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self | exact GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self | (intros; apply GlobalTheory.IsoPartPairing.symplOH_isoPart_add_self <;> assumption)
