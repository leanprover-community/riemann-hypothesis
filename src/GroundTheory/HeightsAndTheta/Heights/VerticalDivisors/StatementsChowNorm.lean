module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
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

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

section Generic

variable (k : Type*) [Field k] (e n : ℕ)

abbrev GenParField : Type _ := FractionRing (MvPolynomial (Par e n) k)

def genPar : Par e n → GenParField k e n :=
  fun p => algebraMap (MvPolynomial (Par e n) k) (GenParField k e n) (X p)

abbrev GenSec {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) k)) : Type _ :=
  SecAlg (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n)

end Generic

def ChowNormFormGeneric.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite (GenParField k e n) (GenSec k e Q) ∧
        ∃ c : GenParField k e n, c ≠ 0 ∧
          specRest (algebraMap k (GenParField k e n)) g (genPar k e n) =
            C c * normForm (GenSec k e Q)
              (secCoord (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n)))) (genPar k e n))

def SecAlgFieldChange.Statement : Prop :=
  ∀ (E₀ E : Type) [Field E₀] [Field E] (φ : E₀ →+* E) (n e : ℕ)
    (Q₀ : Ideal (MvPolynomial (Fin n) E₀)) (y₀ : Par e n → E₀), Module.Finite E₀ (SecAlg Q₀ y₀) →
      Module.Finite E (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀)) ∧
        (normForm (SecAlg Q₀ y₀) (secCoord Q₀ y₀)).map φ =
          normForm (SecAlg (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))
            (secCoord (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀))

def SecAlgFinite.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), AlgebraicIndependent k y → IsProjPrime Q → IsChowForm Q (e + 1) g →
      Module.Finite E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y)

def GenSecDomain.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      IsDomain (GenSec k e Q)

def GenSecSeparable.Statement : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Algebra.IsSeparable (GenParField k e n) (GenSec k e Q)

def ChowSecDvd.Statement : Prop :=
  ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (n e : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) (g : MvPolynomial (Fin (e + 1) × Fin n) k)
    (y : Par e n → E), IsProjPrime Q → IsChowForm Q (e + 1) g →
      ∃ m : ℕ, 0 < m ∧
        (∑ j, X j * C (secCoord (Q.map (MvPolynomial.map (algebraMap k E))) y j)) ∣
          ((specRest (algebraMap k E) g y).map
            (algebraMap E (SecAlg (Q.map (MvPolynomial.map (algebraMap k E))) y))) ^ m

def NormFormIrreducible.Statement : Prop :=
  ∀ (E L : Type) [Field E] [CommRing L] [IsDomain L] [Algebra E L] [Module.Finite E L]
    [Algebra.IsSeparable E L] (n : ℕ) (x : Fin n → L) (t : Fin n → E),
    Algebra.adjoin E (Set.range x) = ⊤ → ∑ j, algebraMap E L (t j) * x j = 1 →
      Irreducible (normForm (R := E) L x)

def GenChowIrreducible.Statement : Prop :=
  ∀ (k : Type) [Field k] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      Irreducible (specRest (algebraMap k (GenParField k e n)) g (genPar k e n))

def NormFormDvd.Statement : Prop :=
  ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A]
    (n : ℕ) (x : Fin n → A) (p : MvPolynomial (Fin n) R),
      (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) ∣ p.map (algebraMap R A) →
        normForm A x ∣ p ^ Module.finrank R A

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Vertical
