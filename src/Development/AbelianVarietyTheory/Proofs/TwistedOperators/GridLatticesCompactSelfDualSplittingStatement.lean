module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.grid_lattices_compact_selfDual_splitting : OnStd fun {D} _ _ {sc} {G} W F => (∀ i, i < D.R.m → FinLat (latRow G i) ∧ FinLat (latCore G i) ∧ FinLat (latBig G i) ∧ IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) ∧ (∀ ρ h, IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) ∧ (∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v ∧ MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v) ∧ IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) ∧ ∀ v, OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v) ∧ ∀ ρ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ ρ * (G.pl.stAbar sc ^ ρ)⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  first | exact @GlobalTheory.AscFin.GridLat.lattices_grid | exact GlobalTheory.AscFin.GridLat.lattices_grid | (intros; apply GlobalTheory.AscFin.GridLat.lattices_grid <;> assumption)
