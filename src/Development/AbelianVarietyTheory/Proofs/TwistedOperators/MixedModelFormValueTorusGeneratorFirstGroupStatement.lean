module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPairingSingleNe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroup
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalThetaInertPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

@[expose] public section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → ℓ (ω (t, 1) s) = (-1) ^ n' * (q : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') := by
  first | exact @GlobalTheory.SphTheta.TorusFirst.value_torus_first | exact GlobalTheory.SphTheta.TorusFirst.value_torus_first | (intros; apply GlobalTheory.SphTheta.TorusFirst.value_torus_first <;> assumption)
