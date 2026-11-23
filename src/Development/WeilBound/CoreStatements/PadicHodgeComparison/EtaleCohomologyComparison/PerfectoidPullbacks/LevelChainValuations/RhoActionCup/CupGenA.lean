module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.CupZnApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProductStatement
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
set_option autoImplicit false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
theorem cup_genA {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
    (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
    (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j) (hG : (chainOf hL M s hQ rH).Good)
    (hP : (cupOf hL M s hQ rH).Good) {i j : ℕ} (x : ∀ n, M.Hc false n i) (y : ∀ n, M.Hc false n j) (z : ∀ n, M.Hc false n (i + j))
    (f : Module.Dual K (HdR M.q i) →+ L.B) (g : Module.Dual K (HdR M.q j) →+ L.B) (h : Module.Dual K (HdR M.q (i + j)) →+ L.B)
    (hx : (chainOf hL M s hQ rH).Rho x f) (hy : (chainOf hL M s hQ rH).Rho y g) (hz : (chainOf hL M s hQ rH).Rho z h)
    (hc : ∀ n, z n = cupS M n i j (x n) (y n)) {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i))
    (b' : Module.Basis (Fin e') K (HdR M.q j)) (φ : Module.Dual K (HdR M.q (i + j))) :
    h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K L.B (φ (cupK M.q rfl (b s) (b' s'))) := by
  obtain rfl : z = fun n => cupS M n i j (x n) (y n) := funext hc
  have H : h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K L.B (φ (cupR M i j (b s) (b' s'))) :=
    GlobalTheory.T.realization_cup_product (chainOf hL M s hQ rH) hG (cupOf hL M s hQ rH) hP x y f g h hx hy hz b b' φ
  simp only [cupR_eq] at H
  exact H

end CrystallineSemistableComparison.Pb.Kap
