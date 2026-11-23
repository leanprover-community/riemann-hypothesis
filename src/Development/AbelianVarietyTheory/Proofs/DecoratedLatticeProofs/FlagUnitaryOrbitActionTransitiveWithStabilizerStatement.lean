module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnitaryOrbitActionTransitiveWithStabilizer
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

theorem _root_.GlobalTheory.T.flagUnitaryOrbitAction_transitive_with_stabilizer : ∀ (D : D7) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : IsBase W x₀), ∃ (_ : MulAction ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀)) (y₀ : Orb W x₀), y₀.1 = x₀ ∧ (∀ (γ : (NFlagQ V d.e).prod (GQ W)) (x : Orb W x₀), (rat (γ • x).1 : Mx D W.rank ρ) * blockX d γ.1.1.1 = mt W γ.1.2 * rat x.1) ∧ (∀ x : Orb W x₀, ∃ γ : (NFlagQ V d.e).prod (GQ W), γ • y₀ = x) ∧ ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)).comap (MonoidHom.inl _ _) = (GQ V ⊓ radX d).subgroupOf (flagN d) ∧ ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)).map (MonoidHom.snd _ _) = GQ W ⊓ Rgrp W (rat x₀) := by
  first | exact @GlobalTheory.OrbAct.action_transitive_stabiliser | exact GlobalTheory.OrbAct.action_transitive_stabiliser | (intros; apply GlobalTheory.OrbAct.action_transitive_stabiliser <;> assumption)
