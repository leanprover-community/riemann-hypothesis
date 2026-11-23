module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantGLOfEquivariantUnitaryCoefficientSpac
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism.BasicNotions Formalism.L2.DIV

theorem _root_.GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ), (∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))) v) = rhoK σ (fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)) (φ v)) → ∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v) := by
  first | exact @GlobalTheory.Branching.Family.equivariant_gl_of_unitary | exact GlobalTheory.Branching.Family.equivariant_gl_of_unitary | (intros; apply GlobalTheory.Branching.Family.equivariant_gl_of_unitary <;> assumption)
