module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeFiltrationQuotient
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

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

theorem _root_.GlobalTheory.T.truncated_envelope_filtration_quotient : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → ∀ (b : ℕ →₀ B) (r : ℕ), r ≤ s → ∀ c : B, (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ↔ ∀ k, b k ∈ fil δ (r - k)) ∧ (Ideal.Quotient.mk (fil (eta δ) (max s 1)) (b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1)) ∈ fil δ' r ⊔ Ideal.span {Ideal.Quotient.mk (fil (eta δ) (max s 1)) (algebraMap B (pq B).P c)} ↔ ∀ k, b k ∈ fil δ (r - k) ⊔ Ideal.span {c}) := by
  first | exact @GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | exact GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit | (intros; apply GlobalTheory.CompanionTheory.SiteTrCrit.tr_crit <;> assumption)
