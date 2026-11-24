module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
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

theorem _root_.GlobalTheory.T.local_frame_taylor_class_eq : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ), 2 ≤ s → ∀ {V V' : X.Opens} (hVV : V ≤ V') {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s t E ε →
    ∀ (p : Fin d → (sP (KS q s {V})).A.obj E.D → (sP (KS q s {V})).A.obj E.D), Taylor (sFil (KS q s {V})) E p →
    ∀ (σ : ∀ T, E.D ⟶ T) (g : Γ(X, V')), IsUnit g → ∀ (ĝ : ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
      (∀ T, Ideal.Quotient.mk T.obj.J (ĝ T) = ev T.obj (ks_in q s V' _ T.property) g) →
      ∃ h : ∀ T, (sP (KS q s {V})).A.obj T, (∀ T, h T ∈ (sP (KS q s {V})).J.S T) ∧ ∀ u : ComposableArrows (KS q s {V}).FullSubcategory 1,
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s ĝ) u) -
          (∑ i, E.form σ ![i] (Ring.inverse (ε (rs hVV g)) * p i (ε (rs hVV g))) u +
            (h (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)))) ∈
          (sFil (KS q s {V}) 2).S _ := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main | exact GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main <;> assumption)
