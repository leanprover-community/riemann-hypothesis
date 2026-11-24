module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductTorusWeightBlockTranslates
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
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.minorProduct_torusWeight_block_translates : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (τ : D.what₂.Tau), ∃ e : Fin m → ℕ, (∀ (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (l : Fin m → ℂ), (∀ ρ, ρ ≠ τ → c ρ = 1) → c τ = Matrix.diagonal l → MvPolynomial.aeval (fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D m n) ℂ)) (delta p q ap am : MvPolynomial (FVar D m n) ℂ) = (∏ a, l a ^ e a) • (delta p q ap am : MvPolynomial (FVar D m n) ℂ)) ∧ ∀ c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ ρ, ρ ≠ τ → c ρ = 1) → (∀ a b : Fin m, (b : ℕ) < p τ → p τ ≤ (a : ℕ) → c τ b a = 0) → ∀ s ∈ (MvPolynomial.aeval (fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D m n) ℂ)) (delta p q ap am : MvPolynomial (FVar D m n) ℂ)).support, ∑ a : Fin m, (a : ℕ) * e a ≤ ∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j) := by
  first | exact @GlobalTheory.MinorWeight.delta_torus_weight | exact GlobalTheory.MinorWeight.delta_torus_weight | (intros; apply GlobalTheory.MinorWeight.delta_torus_weight <;> assumption)
