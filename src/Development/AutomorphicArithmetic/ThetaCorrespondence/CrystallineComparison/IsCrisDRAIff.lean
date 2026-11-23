module

public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {A B P D : Type} [CommRing A] [CommRing B] [CommRing P] [CommRing D]
  [Algebra A B] [Algebra P D]

def IsCrisDRA (ι : A →+* P) (f : B →+* D) : Prop :=
  ∀ x : A, f (algebraMap A B x) = algebraMap P D (ι x)

theorem isCrisDRA_iff (cA : A ≃+* ACris.ACris ℂ_[l] l) (cBc : B ≃+* Formalism.Per6.Bcris l) (cP : P ≃+* Formalism.Per6.BdRp l)
    (cD : D ≃+* Formalism.Per6.BdR l) (ι : A →+* P)
    (hB : ∀ x : A, cBc (algebraMap A B x) = Formalism.Per6.cB l (cA x))
    (hD : ∀ y : P, cD (algebraMap P D y) = algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cP y))
    (hι : ∀ x : A, cP (ι x) = ACris.iota ℂ_[l] l (cA x)) (f : B →+* D) :
    IsCrisDRA ι f ↔ Formalism.Per6.IsCrisDR l ((cD.toRingHom.comp f).comp cBc.symm.toRingHom) := by
  constructor
  · intro hf x6
    obtain ⟨x, rfl⟩ := cA.surjective x6
    have h1 : cBc.symm (Formalism.Per6.cB l (cA x)) = algebraMap A B x := by
      rw [← hB x, RingEquiv.symm_apply_apply]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [h1, hf x, hD, hι]
  · intro hf x
    apply cD.injective
    have h2 := hf (cA x)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h2
    rw [← hB x, RingEquiv.symm_apply_apply] at h2
    rw [h2, hD, hι]

end Formalism.BasicNotions.CmpTie.Incl
