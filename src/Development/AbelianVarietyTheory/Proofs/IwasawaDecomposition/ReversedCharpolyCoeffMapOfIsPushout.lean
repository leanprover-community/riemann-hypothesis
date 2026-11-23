module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapNormCoeff
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyMulBaseChangeFiniteMapOfIsPushoutStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpolyBaseChangeIntegrallyClosedStatement
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

open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.NormalDescent

theorem reverse_map_of_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem normCoeff_map_of_isPushout {A B A' B' : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [CommRing A']
    [IsDomain A'] [IsIntegrallyClosed A'] [CommRing B'] (φ : A →+* B) (α : A →+* A') (β : B →+* B') (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hα : Function.Injective α) (hφ : φ.Finite) (hφ' : φ'.Finite) (b : B) (k : ℕ) :
    α (normCoeff φ hφ b k) = normCoeff φ' hφ' (β b) k := by
  have hbc := @GlobalTheory.T.charpolyMulBaseChangeFinite_map_of_isPushout
  have hint := @GlobalTheory.T.exists_charpoly_baseChange_integrallyClosed
  let ι : FractionRing A →+* FractionRing A' := IsLocalization.map (FractionRing A') α
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective α hα)
  have hι : ∀ a : A, ι (algebraMap A (FractionRing A) a) = algebraMap A' (FractionRing A') (α a) :=
    fun a => IsLocalization.map_eq _ _
  have hc := hbc φ α β φ' H hφ hφ' ι hι b
  have spec : ∀ {R S : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing S] (ψ : R →+* S)
      (hψ : ψ.Finite) (s : S), algebraMap R (FractionRing R) (normCoeff ψ hψ s k) =
        (charK ψ hψ (FractionRing R) s).reverse.coeff k := by
    intro R S _ _ _ _ ψ hψ s
    obtain ⟨P, hP⟩ := hint (K := FractionRing R) ψ hψ s
    refine algebraMap_normCoeff ψ hψ s k ⟨P.reverse.coeff k, ?_⟩
    rw [← hP, reverse_map_of_injective _ (IsFractionRing.injective R (FractionRing R)), coeff_map]
  apply IsFractionRing.injective A' (FractionRing A')
  rw [← hι, spec, spec, hc, reverse_map_of_injective ι ι.injective, coeff_map]

end GlobalTheory.NormalDescent
