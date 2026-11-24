module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartIncOrd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
    [(W.map (chartX I t e)).IsPrime]
    [(W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime]
    (x : MvPolynomial (Fin n) F),
    Ring.ord (Localization.AtPrime (W.map (chartX I t e)))
        (algebraMap (ChartInc I t e) _ (chartX I t e x)) =
      Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
        (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) x))

section Inhabitants

theorem isPrime_map_of_sup_ker {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (K : Ideal R) (h : (K ⊔ RingHom.ker f).IsPrime) : (K.map f).IsPrime := by
  have e : K.map f = (K ⊔ RingHom.ker f).map f := by
    rw [Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker f).mpr le_rfl, sup_bot_eq]
  rw [e]
  exact Ideal.map_isPrime_of_surjective hf le_sup_right

end Inhabitants

end

end GroundTheory.Heights₂.Heights
