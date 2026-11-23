module

public import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G

variable {p n' : ℕ} {W Qq Os Ks O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing Os] [IsDomain Os] [IsDiscreteValuationRing Os] [Field Ks] [Algebra Os Ks]
  [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ιs : Qq →+* Ks} {σ : Qq ≃+* Qq} {js : W →+* Os} {ws : Os}

structure ExtOf (Os Ks O Kf : Type) [CommRing Os] [Field Ks] [Algebra Os Ks] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf] where
  φ : Os →+* O
  φK : Ks →+* Kf
  comm : ∀ x : Os, φK (algebraMap Os Ks x) = algebraMap O Kf (φ x)
  fin : φ.Finite
  frac : IsFractionRing O Kf
  complete : IsAdicComplete (IsLocalRing.maximalIdeal O) O

theorem setting_ext (h : UnramifiedQuadraticSetting p n' W Qq Os Ks ιs σ js ws) (X : ExtOf Os Ks O Kf) :
    HidaSetting p n' W Qq O Kf (X.φK.comp ιs) σ (X.φ.comp js) (X.φ ws) := by
  exact
    { prime := h.1.prime
      five_le := h.1.five_le
      two_le := h.1.two_le
      even := h.1.even
      frac_alt := h.1.frac_alt
      frac_O := X.frac
      p_unif := h.1.p_unif
      res_card := h.1.res_card
      eq_sum_herm_smul_frame_of_inW := h.1.eq_sum_herm_smul_frame_of_inW
      frob := h.1.frob
      period := h.1.period
      ι_comp := by
        intro x
        simp only [RingHom.comp_apply]
        rw [h.1.ι_comp, X.comm]
      finite := X.fin.comp h.1.finite
      complete_O := X.complete
      w_sq := by rw [← map_pow, h.1.w_sq, map_natCast] }

end Formalism.L2.G
