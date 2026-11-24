module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Kum

namespace UpperTheory.V.CF

section Art

variable (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]

end Art

section Tower

variable (k K H : Type) [Field k] [Field K] [Field H] [Algebra k K] [Algebra K H] [Algebra k H] [IsScalarTower k K H]

def relIncl : Gal(H/K) →* Gal(H/k) := AlgEquiv.restrictScalarsHom k

def resTo [Normal k K] : Gal(H/k) →* Gal(K/k) := AlgEquiv.restrictNormalHom K

theorem resTo_commutes [Normal k K] (σ : Gal(H/k)) (x : K) :
    algebraMap K H (resTo k K H σ x) = σ (algebraMap K H x) := AlgEquiv.restrictNormal_commutes σ K x

theorem resTo_surjective [Normal k K] [Normal k H] : Function.Surjective (resTo k K H) :=
  AlgEquiv.restrictNormalHom_surjective H

theorem range_relIncl [Normal k K] : (relIncl k K H).range = (resTo k K H).ker := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap K H).injective
    rw [resTo_commutes]
    simp [relIncl]
  · intro h
    rw [MonoidHom.mem_ker] at h
    have hc : ∀ x : K, σ (algebraMap K H x) = algebraMap K H x := by
      intro x
      rw [← resTo_commutes, h]
      rfl
    refine ⟨{ σ with commutes' := hc }, ?_⟩
    ext y
    rfl

end Tower

def UnramAt (L : Type) [Field L] [NumberField L] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → (p : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1

def phi (p : ℕ) (P : Type) [Group P] : Subgroup P := Subgroup.closure (Set.range fun g : P => g ^ p) ⊔ commutator P

def aug (R G : Type) [CommRing R] [Group G] : MonoidAlgebra R G →ₐ[R] R := MonoidAlgebra.lift R R G 1

theorem aug_single (R G : Type) [CommRing R] [Group G] (g : G) (r : R) : aug R G (MonoidAlgebra.single g r) = r := by
  simp [aug]

def augIdeal (R G : Type) [CommRing R] [CommGroup G] : Ideal (MonoidAlgebra R G) :=
  Ideal.span (Set.range fun g : G => MonoidAlgebra.of R G g - 1)

def pStar (p : ℕ) : ℤ := (-1) ^ (p / 2) * p

end UpperTheory.V.CF

end
