module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingOpenOrbitUnfoldsToAdelicIntegral
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doubling_open_orbit_unfolds_to_adelic_integral : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ZetaConvH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) ∧ ∫ x, GlobalTheory.Eis.dblIntegrandQ V μ (fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y)) f₁ f₂ x ∂(autMeasure V m).prod (autMeasure V m) = zetaH D.sp.cm.sig (gram_hdbl V) m φ (GlobalTheory.Eis.petCoef V m f₁ f₂) := by
  first | exact @GlobalTheory.Core.Rk.OpenOrbit.open_orbit | exact GlobalTheory.Core.Rk.OpenOrbit.open_orbit | (intros; apply GlobalTheory.Core.Rk.OpenOrbit.open_orbit <;> assumption)
