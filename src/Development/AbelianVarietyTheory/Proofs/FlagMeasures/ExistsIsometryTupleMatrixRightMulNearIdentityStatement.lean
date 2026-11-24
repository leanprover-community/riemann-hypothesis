module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryTupleMatrixRightMulNearIdentity
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

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.exists_isometry_tupleMatrixRightMul_near_identity : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N e : ℕ, ∃ i0 : ℕ, ∀ i ≥ i0, ∀ x : Fin m → Fin n → E, (∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) → gramT L Hm x = Γ → ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = rmul x A a := by
  first | exact @GlobalTheory.HL.RStab.exists_isometry_rmul | exact GlobalTheory.HL.RStab.exists_isometry_rmul | (intros; apply GlobalTheory.HL.RStab.exists_isometry_rmul <;> assumption)
