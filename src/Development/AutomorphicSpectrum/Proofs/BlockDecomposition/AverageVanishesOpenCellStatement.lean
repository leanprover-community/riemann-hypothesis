module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCell
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.average_vanishes_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eO ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∉ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | exact GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.LocO.main <;> assumption)
