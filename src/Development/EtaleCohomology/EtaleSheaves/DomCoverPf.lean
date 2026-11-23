module

public import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonDenom
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC

namespace LateralTheory.E.DomCoverPf

theorem aicFrac (R L : Type) [CommRing R] [CommRing L] (φ : R →+* L) (hR : AIC R)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) : AIC L :=
  _root_.UpperTheory.Reformulated.B.Qn19.aicFrac R L φ hR h

def IdemCover : Prop := ∀ (C : CommRingCat.{0}), ∃ (D : CommRingCat.{0}) (g : C ⟶ D),
  g.hom.IsIntegral ∧ t_E3Cut.SpS g ∧ ∀ (r : Ideal D) [r.IsPrime], IsDomain (Localization.AtPrime r) ∧
    ∀ z : Localization.AtPrime r, ∃ a b : C, IsUnit (algebraMap D (Localization.AtPrime r) (g.hom b)) ∧
      z * algebraMap D (Localization.AtPrime r) (g.hom b) = algebraMap D (Localization.AtPrime r) (g.hom a)

theorem DomCover_of (h2 : IdemCover) : t_E3Cut.DomCover := by
  intro C hC
  obtain ⟨D, g, hi, hs, hr⟩ := h2 C
  refine ⟨D, g, hi, hs, fun r _ => ⟨(hr r).1, ?_⟩⟩
  exact aicFrac C (Localization.AtPrime r) ((algebraMap D (Localization.AtPrime r)).comp g.hom) hC (hr r).2

end LateralTheory.E.DomCoverPf
