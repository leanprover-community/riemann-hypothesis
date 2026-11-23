module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GradedChartDegrees.ThickeningIdealNilpotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLiftTensorCompat
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Diso GlobalTheory.CompanionTheory.DisoHm

theorem _root_.GlobalTheory.T.chart_lift_tensor_compat : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (h : OL l O) {W : X.Opens} {d : ℕ} (c : Coord q W d) (m : ℕ)
    (cL : Chart (pdm h m) l q (κm l O m) W d)
    (hcL : ∀ i, ev cL.D cL.inV (c.t i) = Ideal.Quotient.mk _ (cL.t i))
    (cO : Chart (dividedPowersBot O) 0 q (Ideal.Quotient.mk ⊥) W d),
    letI := (strV q W).toAlgebra
    ∀ (e : O ⊗[O] Γ(X, W) ≃+* cO.D.B), (∀ r, e (r ⊗ₜ 1) = cO.D.i r) → (∀ i, e (1 ⊗ₜ c.t i) = cO.t i) →
      (∀ f, ev cO.D cO.inV f = Ideal.Quotient.mk _ (e (1 ⊗ₜ f))) →
      ∀ (hT : Good (l := l) cO.D m) (σ : cL.D ⟶ GObj h cO.D m hT),
        (∀ i, σ.φ (cL.t i) = Ideal.Quotient.mk _ (cO.t i)) → Function.Bijective σ.φ := by
  first | exact @GlobalTheory.CompanionTheory.DisoHm.cmp_bij | exact GlobalTheory.CompanionTheory.DisoHm.cmp_bij | (intros; apply GlobalTheory.CompanionTheory.DisoHm.cmp_bij <;> assumption)
