module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
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

noncomputable section

namespace GlobalTheory.AscFin.OrbitAny

open GlobalTheory.FinPl.SplitOrbit

theorem orbitAny : ∀ (D : D7) (V₀ A L : HSp D) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (L₀ : Lat V₀) (LA : Lat A) (LL : Lat L) (v : GlobalTheory.FinPl.Pl D), IsSelfDualC V₀ L₀ → IsSelfDualC A LA → IsSelfDualC L LL → OrthAt o L₀ LA LL v → ∀ γ ∈ grpAt V₀ (· = v), (∀ a : AE D, a • ratV (vecB o ζ) ∈ latA V₀ L₀ (· = v) → mt V₀ γ⁻¹ *ᵥ (a • ratV (vecB o ζ)) ∈ latA V₀ L₀ (· = v)) → ∃ a ∈ grpAt A (· = v), ∃ κ, InK V₀ L₀ (· = v) κ ∧ γ = o.emb (a, 1) * κ := by
  intro D V₀ A L o ζ hζ L₀ LA LL v hL₀ hLA hLL hO γ hγ hz
  have hT := GlobalTheory.FinPl.TamePlaces.tame D v
  have hM := isSDAt_pre_unitary (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D V₀ L₀ v hL₀) γ⁻¹
  obtain ⟨hA, hsplit⟩ := split_of_le o hM (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D L LL v hLL) (line_le o hζ hO _ hz)
  obtain ⟨a, ha, hmv⟩ := GlobalTheory.T.selfDualLattices_single_orbit_tamePlace D A v _ _ hT (GlobalTheory.T.isSelfDualLatticeAtPlace_latticeCompletion D A LA v hLA) hA
  exact ⟨a, ha, (o.emb (a, 1))⁻¹ * γ, ⟨mul_mem (inv_mem (emb_mem_grpAt o ha)) hγ,
    moves_of_split o hO γ a hsplit hmv⟩, (mul_inv_cancel_left _ _).symm⟩

end GlobalTheory.AscFin.OrbitAny

end
