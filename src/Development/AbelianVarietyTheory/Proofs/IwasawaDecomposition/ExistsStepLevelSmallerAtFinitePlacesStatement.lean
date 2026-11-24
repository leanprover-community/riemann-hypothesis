module

public import Formalism.LocalToGlobal.Divisibility.Tuples
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStepLevelSmallerAtFinitePlaces
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_stepLevel_smaller_at_finite_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  first | exact @GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | exact GlobalTheory.StepLevelShrink.exists_stepLevel_shrink | (intros; apply GlobalTheory.StepLevelShrink.exists_stepLevel_shrink <;> assumption)
