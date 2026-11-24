module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
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

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem algebraMap_pInv {l : ℕ} [Fact l.Prime] (z : ↥(algebraMap (BdRp l) (BdR l)).range) :
    algebraMap (BdRp l) (BdR l) (pInv l z) = z.1 :=
  congrArg Subtype.val ((RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).apply_symm_apply z)

theorem iota_lam_eq_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (c : (per l K).A) (y : (per l K).P), (y : (per l K).B) = (per l K).i c →
      (lev h k).ι ((lev h k).lam c) = (lev h k).toB y := by
  intro c y hy
  have h1 : (lev h k).ι ((lev h k).lam c) = pk l k (ACris.iota ℂ_[l] l c) := rfl
  have h2 : (lev h k).toB y = pk l k (pInv l y) := rfl
  rw [h1, h2]
  congr 1
  apply IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  exact hy.symm.trans (algebraMap_pInv y).symm

end GlobalTheory.CompanionTheory.LatC
