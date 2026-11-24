module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.RationalSuccAbove.RatSuccAboveSucc
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

noncomputable section

namespace PositivityTheory.KB

theorem sChain_of : SChain := by
  have hbd : ∀ (G : Type) [Group G] (m : ℕ), bd G m = SimplicialChains.ibd G m := fun _ _ _ => rfl
  have hcm : ∀ (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ), cmap f m = SimplicialChains.icmap f m :=
    fun _ _ _ _ _ _ => rfl
  refine ⟨fun G _ m z => ?_, fun G H _ _ f m z => ?_, fun G H K _ _ _ f g m z => ?_,
    fun G _ g m z hz => ?_⟩
  · rw [hbd, hbd]
    exact SimplicialChains.ibd_ibd m z
  · rw [hbd, hbd, hcm, hcm]
    exact SimplicialChains.ibd_icmap f m z
  · rw [hcm, hcm, hcm]
    exact SimplicialChains.icmap_comp f g m z
  · unfold IsBd
    unfold IsCyc at hz
    rw [hbd] at hz ⊢
    rw [hcm]
    exact SimplicialChains.conj_bd g m z hz

end PositivityTheory.KB
