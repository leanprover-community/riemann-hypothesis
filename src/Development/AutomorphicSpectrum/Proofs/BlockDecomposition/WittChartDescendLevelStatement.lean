module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittChartDescendLevel
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

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

theorem _root_.GlobalTheory.T.witt_chart_descend_level : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ} (c' : Chart (Wc.pd l k (n + 1)) l q ((Wc.res l k (n + 1)).comp ρ) W d), ∃ (c : Chart (Wc.pd l k n) l q ((Wc.res l k n).comp ρ) W d) (e : c.D ≅ (qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D), (∀ i, e.hom.φ (c.t i) = Ideal.Quotient.mk _ (c'.t i)) ∧ (FlatT ((qF (F := B.schFn q) (ρ := ρ) hn).obj c'.D) → FlatT c.D) := by
  first | exact @GlobalTheory.CompanionTheory.ChartRed.chart_q | exact GlobalTheory.CompanionTheory.ChartRed.chart_q | (intros; apply GlobalTheory.CompanionTheory.ChartRed.chart_q <;> assumption)
