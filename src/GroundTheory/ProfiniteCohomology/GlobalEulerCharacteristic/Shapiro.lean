module

public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
public import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.ShapiroRatio
public import GroundTheory.ProfiniteCohomology.RealPlaces.VanishingMackeyTransfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  {L : FiniteSubfield} [Fact (K ≤ L)]
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
  (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

theorem exists_gsEulerRatio_coind_eq :
    ∃ ιrL : ∀ w : {w : InfinitePlace L.1 // w.IsReal}, ℚ̄ →ₐ[L.1] AlgebraicClosure w.1.Completion,
      ∀ (B : Rep.{0} (ULift.{0} ℤ) (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)))
        [IsDiscreteRep B] [Finite B],
        gsEulerRatio S (Rep.coind (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype B)
            ιr =
          @gsEulerRatio L (placesOver S) (Rep.res (gsBaseChange S hL).symm.toMulEquiv.toMonoidHom B)
            (IsDiscreteRep.res (continuous_mulEquiv_toMonoidHom (gsBaseChange S hL).symm) B) ιrL := by
  choose mem hmem using realMemberPlace_surjective S ιr hL
  choose ιrL e he using fun w => exists_real_data_of_eq S ιr hL (mem w) w
    ((coe_realMemberPlace S ιr hL (mem w)).symm.trans (congrArg Subtype.val (hmem w)))
  exact ⟨ιrL, fun B _ _ => gsEulerRatio_coind_eq_of S hL ιr B ιrL mem hmem e he⟩

end

end GroundTheory.ProfCoh
