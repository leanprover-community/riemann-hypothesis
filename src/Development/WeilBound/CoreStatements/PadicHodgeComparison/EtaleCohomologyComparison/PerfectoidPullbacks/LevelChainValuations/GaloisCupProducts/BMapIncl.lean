module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.NmK
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.ReductionChangeLevel
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ChainOf
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CrSEqOne
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section



open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

namespace LevelChangeComparison

end LevelChangeComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

section
variable (S : LevSys (per l K)) (hS : S.Good) (m : ℕ) (M : Model l K)

def nmLevA : NMor (S.L (m + 1)).γ M.p (κA (OK l K) (S.L (m + 1)).I) (S.L m).γ M.p (κA (OK l K) (S.L m).I) (S.dA m) :=
  nmK (S.L (m + 1)).γ (S.L m).γ M.p M.p (S.dA m) (hS.ddp m) (hS.dO m) (𝟙 M.X) (Category.id_comp _)

def nmLevB : NMor (S.L (m + 1)).γB M.q (κA K (S.L (m + 1)).IB) (S.L m).γB M.q (κA K (S.L m).IB) (S.dB m) :=
  nmK (S.L (m + 1)).γB (S.L m).γB M.q M.q (S.dB m) (hS.ddpB m) (hS.dK m) (𝟙 M.gen) (Category.id_comp _)

namespace LevelChangeComparison

end LevelChangeComparison

end

theorem bMap_incl {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) {s s' : ℕ} (h : s ≤ s')
    (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
    (hQ' : ∀ T, QB L M s' T → QA L M s' (((nmB M hL).mor 0).obj T)) (j : ℕ) (z : HO (QA L M s') j) :
    (incl (ts_le L.γB M.q 1 h {⊤})).o.pull j (bMap M s' hL hQ' j z) =
      bMap M s hL hQ j ((incl (ts_le L.γ M.p l h {⊤})).o.pull j z) := by
  have e₁ := CrystallineSemistableComparison.pull_pull L.ι (smB M s' hL hQ').o (incl (ts_le L.γB M.q 1 h {⊤})).o j z
  have e₂ := CrystallineSemistableComparison.pull_pull L.ι (incl (ts_le L.γ M.p l h {⊤})).o (smB M s hL hQ).o j z
  exact e₁.trans (Eq.trans rfl e₂.symm)

end CrystallineSemistableComparison.Pb.Kap
