module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomLevGood
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DPullCEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InclRedM
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
set_option linter.unusedVariables false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
  (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
  (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T))
  (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j)
  (rH' : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s') none ((l : L.A) ^ n) j)

theorem homS_good_of_inclHM (hr : ∀ n j x, inclHM M h n j (rH' n j x) = rH n j x) :
    (homS hL M h hQ hQ' rH rH').Good := by
  constructor
  · rfl
  · intro c
    rfl
  · intro a
    rfl
  · intro k
    rfl
  · intro n j x
    rfl
  · intro n j x
    exact hr n j x
  · intro n j z
    exact GlobalTheory.CompanionTheory.RedPull.incl_redM
      (ts_le L.γ M.p l h {⊤}) none ((l : L.A) ^ n) j z
  · intro j z
    exact bMap_incl hL M h hQ hQ' j z
  · intro j v
    exact GlobalTheory.CompanionTheory.MuThick.muB_incl
      L.γB M.q 1 s s' {⊤} (ts_le L.γB M.q 1 h {⊤}) j v

end

end CrystallineSemistableComparison.Pb.Kap
