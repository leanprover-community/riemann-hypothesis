module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReduction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.simpleModule_linkage_dualWeylLattice_reduction : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ → ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm → Embeds O N lam mu ϖ Gm → ∀ τ, (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) = ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  first | exact @GlobalTheory.CapelliLink.linkage | exact GlobalTheory.CapelliLink.linkage | (intros; apply GlobalTheory.CapelliLink.linkage <;> assumption)
