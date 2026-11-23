module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsBiSmooth
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RapidVal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftReductionToFockVectorsUniform
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubleLift_reduction_to_fockVectors_uniform : ∀ D : D7, BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ : GA D A → ℂ) (C : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C → IsBiSmooth C → ∃ (n : ℕ) (P : Fin n → PolF D S.rank A.rank) (P' : Fin n → PolF D A'.rank S.rank), ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → k.vac = k₀.vac → k'.vac = k₀'.vac → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → HasCen A χ φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C) = ∑ i, k'.lift ψ θ y z (P' i) (k.lift ψ θ x y (P i) φ) := by
  first | exact @GlobalTheory.SeeSaw.fockRed_uniform | exact GlobalTheory.SeeSaw.fockRed_uniform | (intros; apply GlobalTheory.SeeSaw.fockRed_uniform <;> assumption)
