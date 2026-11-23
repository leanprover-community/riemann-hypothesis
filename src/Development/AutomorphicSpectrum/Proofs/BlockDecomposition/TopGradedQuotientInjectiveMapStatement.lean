module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedQuotientInjectiveMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

theorem _root_.GlobalTheory.T.top_graded_quotient_injective_map : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (r : ℤ), r = d → d + 1 ≤ s →
    letI := (strV q W).toAlgebra
    ∃ φ : HQ (KS q s {W}) r (r + 1) d →ₗ[K] Γ(X, W), Function.Injective φ ∧ ∀ (y : Γ(X, W)) (c : HQ (KS q s {W}) r (r + 1) d),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (E.form σ id (ε y)) c → φ c = y := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_map | exact GlobalTheory.CompanionTheory.ConeLocal.coef_map | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_map <;> assumption)
