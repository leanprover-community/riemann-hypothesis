module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryIsometryIsotropicFrameLocalRing
import Formalism.LocalRingCardinality.DataHost
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

theorem _root_.GlobalTheory.T.exists_unitaryIsometry_isotropicFrame_localRing : ∀ (O : Type) [CommRing O] [IsLocalRing O] (s : O →+* O), (∀ x, s (s x) = x) → (∃ τ : O, τ + s τ = 1) → (∀ u : O, IsUnit u → s u = u → ∃ x : O, s x * x = u) → ∀ (n r : ℕ) (Q : Matrix (Fin n) (Fin n) O), Formalism.UG.cT s Q = Q → IsUnit Q → ∀ C C' : Matrix (Fin n) (Fin r) O, (∃ L : Matrix (Fin r) (Fin n) O, L * C = 1) → (∃ L : Matrix (Fin r) (Fin n) O, L * C' = 1) → Formalism.UG.cT s C * Q * C = 0 → Formalism.UG.cT s C' * Q * C' = 0 → ∃ k : GL (Fin n) O, Formalism.UG.cT s k.1 * Q * k.1 = Q ∧ k.1 * C = C' := by
  first | exact @GlobalTheory.WittFrame.exists_isometry_frame | exact GlobalTheory.WittFrame.exists_isometry_frame | (intros; apply GlobalTheory.WittFrame.exists_isometry_frame <;> assumption)
