module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariant
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.DIV

theorem _root_.GlobalTheory.T.exists_eq_smul_brStd_of_equivariant : ∀ {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1), 1 ≤ n → ∀ (Λ : ι → DomWeight N) (σ : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ, (∀ (g : ι → GL (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (g τ)) v) = rhoK σ g (φ v)) → ∃ c : ℂ, φ = c • Formalism.L2.Col.Br.brStd hN Λ σ := by
  first | exact @GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | exact GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant | (intros; apply GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant <;> assumption)
