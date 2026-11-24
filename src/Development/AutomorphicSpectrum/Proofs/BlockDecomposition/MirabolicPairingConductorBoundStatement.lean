module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_bound : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (g : GL (Fin (n + 1)) k) (v : V) (v' : V'), ∃ r : kˣ, ∀ t : kˣ, valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) → ∀ t' : kˣ, (∀ x ∈ box (n + 1) t, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t') → JJ ν ψ T B {x | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t'} v v' = JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | exact GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box | (intros; apply GlobalTheory.CompanionTheory.MirPair.JJ_preimage_box_eq_JJ_box <;> assumption)
