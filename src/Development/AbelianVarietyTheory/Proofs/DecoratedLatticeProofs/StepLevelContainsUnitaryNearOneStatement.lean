module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepLevelContainsUnitaryNearOne
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

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem _root_.GlobalTheory.T.stepLevel_contains_unitary_near_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (Q : Finset (HeightOneSpectrum (𝓞 E))), ∃ d : ℕ, ∀ z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), z ∈ Formalism.UG.UPts σ J (FiniteAdeleRing (𝓞 F) F) → (∀ w ∉ Q, GlobalTheory.Mem.ColAd.locM w z = 1) → (∀ w ∈ Q, GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z - 1) ∧ GlobalTheory.Mem.ColAd.Sm Valued.v (WithZero.exp (-(d : ℤ))) (GlobalTheory.Mem.ColAd.locM w z⁻¹ - 1)) → z ∈ S.U := by
  first | exact @GlobalTheory.LevelApprox.mem_U_of_near_one | exact GlobalTheory.LevelApprox.mem_U_of_near_one | (intros; apply GlobalTheory.LevelApprox.mem_U_of_near_one <;> assumption)
