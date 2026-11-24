module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MxAtOfMemDepLat

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

theorem _root_.GlobalTheory.T.lattice_scaling_at_S0 : All fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∀ u ∈ latRow G i, ∀ v ∈ G.pl.S0, ∀ y ∈ latV (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
  first | exact @GlobalTheory.DepthMap.smul_mulVec_mem_latV | exact GlobalTheory.DepthMap.smul_mulVec_mem_latV | (intros; apply GlobalTheory.DepthMap.smul_mulVec_mem_latV <;> assumption)
