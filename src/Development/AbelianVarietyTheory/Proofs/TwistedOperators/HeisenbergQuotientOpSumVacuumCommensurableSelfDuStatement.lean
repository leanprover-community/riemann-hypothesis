module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDu
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  first | exact @GlobalTheory.SphTheta.sumOp_vacuum_lift | exact GlobalTheory.SphTheta.sumOp_vacuum_lift | (intros; apply GlobalTheory.SphTheta.sumOp_vacuum_lift <;> assumption)
