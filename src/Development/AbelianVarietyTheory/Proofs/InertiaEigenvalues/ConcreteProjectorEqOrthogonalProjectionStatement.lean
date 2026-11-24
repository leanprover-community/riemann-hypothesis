module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

theorem _root_.GlobalTheory.T.concreteProjector_eq_orthogonalProjection : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  first | exact @GlobalTheory.EtaJoin.concreteProj_orth | exact GlobalTheory.EtaJoin.concreteProj_orth | (intros; apply GlobalTheory.EtaJoin.concreteProj_orth <;> assumption)
