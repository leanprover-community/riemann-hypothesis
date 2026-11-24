module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitMemSpanStaircaseIdealProducts
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin




theorem _root_.GlobalTheory.T.exists_unit_mem_span_staircaseIdeal_products : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ρ : ℕ) (p : Fin (2 * ρ + 2 - 1)) (q : Fin (2 * ρ + 1 - 1)), p.1 + q.1 = 2 * ρ → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ G.pl.S0 → ∃ u : 𝓞 D.host.F, u ∉ v.asIdeal ∧ ((u : D.host.F) : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t : D.host.E | ∃ a ∈ D.host.AA, ∃ c' ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) q, ∃ c ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) p, t = D.host.conj (a * c') * c} := by
  first | exact @GlobalTheory.StairUnit.exists_unit_mem_span | exact GlobalTheory.StairUnit.exists_unit_mem_span | (intros; apply GlobalTheory.StairUnit.exists_unit_mem_span <;> assumption)
