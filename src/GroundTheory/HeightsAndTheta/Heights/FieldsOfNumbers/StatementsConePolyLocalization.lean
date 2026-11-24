module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalFlat
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

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u

theorem isPrime_map_C_mvPolynomial {A : Type*} [CommRing A] (σ : Type*) (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

section Cone

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

def coneVarMap (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime] (hPW : P ≤ W) (v : ∀ k, ι k) :
    MvPolynomial K (degZeroLoc P {W}) →ₐ[degZeroLoc P {W}] coneLocal P W hPW :=
  aeval fun k => algebraMap (MRing ι F ⧸ P) (coneLocal P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩))

end Cone

def ConePolyLocalization.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∃ (_ : IsLocalRing (degZeroLoc P {W})),
      letI := (coneVarMap P W hPW v).toRingHom.toAlgebra
      haveI := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
      IsLocalization.AtPrime (coneLocal P W hPW)
        ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
