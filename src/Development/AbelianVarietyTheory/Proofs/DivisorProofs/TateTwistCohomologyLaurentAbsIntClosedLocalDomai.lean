module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyIndEtaleBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyLaurentPolynomialOfIsAlgCloseStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.GmAic

theorem pull_spMap_bijective (R : Type) [CommRing R] {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A')
    (F : Shv R) (n : ℤ) : Function.Bijective (pull R (spMap (e : A →+* A')) F n) := by
  have key : ∀ {B B' : Type} [CommRing B] [CommRing B'] (g : B ≃+* B') (x : H R (sp B') F n),
      pull R (spMap (g : B →+* B')) F n (pull R (spMap (g.symm : B' →+* B)) F n x) = x := by
    intro B B' _ _ g x
    rw [← pull_comp]
    have h : spMap (g : B →+* B') ≫ spMap (g.symm : B' →+* B) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Spec.map_comp]
      have h' : CommRingCat.ofHom (g.symm : B' →+* B) ≫ CommRingCat.ofHom (g : B →+* B') = 𝟙 _ := by
        ext y; simp
      rw [h', Spec.map_id, CategoryTheory.Functor.map_id]
    rw [h, pull_id]
  refine ⟨fun x y hxy => ?_, fun x => ⟨_, key e x⟩⟩
  have hx := key e.symm x
  have hy := key e.symm y
  simp only [RingEquiv.symm_symm] at hx hy
  rw [← hx, ← hy, hxy]

def laurentEquiv (hC3 : C3) (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T)
    (hq : IsUnit (q : T)) (n i : ℤ) :
    Ht q (sp (LaurentPolynomial T)) n i ≃+ Ht q (sp (LaurentPolynomial (FractionRing T))) n i := by
  haveI : IsScalarTower T (Polynomial T) (LaurentPolynomial T) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Polynomial.toLaurent_C]
      rfl
  haveI : Algebra.Etale (Polynomial T) (LaurentPolynomial T) :=
    Algebra.Etale.of_isLocalizationAway (Polynomial.X : Polynomial T)
  have h1 := hC3 q T hA hq (LaurentPolynomial T) i n
  let e : TensorProduct T (FractionRing T) (LaurentPolynomial T) ≃+* LaurentPolynomial (FractionRing T) :=
    (AddMonoidAlgebra.scalarTensorEquiv (M := ℤ) T (FractionRing T)).toRingEquiv
  exact (AddEquiv.ofBijective _ h1).trans (AddEquiv.ofBijective _ (pull_spMap_bijective _ e (tw q i) n))

theorem main : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial T)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial T)) 1 i ≃+ ZMod q) := by
  intro q _ T _ _ _ hA hq n i
  haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
  have hqK : IsUnit (q : FractionRing T) := by
    simpa using hq.map (algebraMap T (FractionRing T))
  obtain ⟨h2, _⟩ := GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed q (FractionRing T) hqK n i
  obtain ⟨_, ⟨e1⟩⟩ := GlobalTheory.T.tateTwistCohomology_laurentPolynomial_of_isAlgClosed q (FractionRing T) hqK 1 i
  refine ⟨fun hn => ?_, ⟨(laurentEquiv GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq 1 i).trans e1⟩⟩
  haveI := h2 hn
  exact (laurentEquiv GlobalTheory.T.etale_cohomology_ind_etale_base_change q T hA hq n i).injective.subsingleton

end GlobalTheory.EtC.GmAic

end
