module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
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

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiProjPrime)

noncomputable section

section Objects

variable {K : Type} [Fintype K] (ι : K → Type)

abbrev segreIdx : Unit ⊕ K → Type := Sum.elim (fun _ : Unit => ∀ k, ι k) ι

variable (R : Type*) [CommRing R]

def segreIncl : MRing ι R →ₐ[R] MRing (segreIdx ι) R :=
  rename fun v => (⟨Sum.inr v.1, v.2⟩ : Σ k, segreIdx ι k)

variable {ι R}

def segreY (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  X (⟨Sum.inl (), c⟩ : Σ k, segreIdx ι k)

def segreMon (c : ∀ k, ι k) : MRing (segreIdx ι) R :=
  ∏ k, X (⟨Sum.inr k, c k⟩ : Σ k, segreIdx ι k)

variable (ι R)

def segreRels : Set (MRing (segreIdx ι) R) :=
  {g | ∃ c d : ∀ k, ι k, g = segreY c * segreMon d - segreY d * segreMon c}

def segreLiftVal (W : Ideal (MRing ι R)) : (Σ k, segreIdx ι k) → Polynomial (MRing ι R ⧸ W)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (Ideal.Quotient.mk W (∏ k, X ⟨k, c k⟩))
  | ⟨Sum.inr k, i⟩ => Polynomial.C (Ideal.Quotient.mk W (X ⟨k, i⟩))

def segreLiftMap (W : Ideal (MRing ι R)) :
    MRing (segreIdx ι) R →ₐ[R] Polynomial (MRing ι R ⧸ W) :=
  aeval (segreLiftVal ι R W)

def segreLift (W : Ideal (MRing ι R)) : Ideal (MRing (segreIdx ι) R) :=
  RingHom.ker (segreLiftMap ι R W)

end Objects

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
