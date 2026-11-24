module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialRelationLinearHeckeStableStatement
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.H3.LamStab

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, Betti.slP_X, map_add (f := _), map_smul]
    simp [MvPolynomial.smul_eq_C_mul]

theorem opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opP S m (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opP R m F z) := by
  funext z
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, polySlash_map]

theorem sum_opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} (s : Finset ι)
    (m : ι → Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    (∑ j ∈ s, opP S (m j)) (fun z => MvPolynomial.map φ (F z)) =
      fun z => MvPolynomial.map φ ((∑ j ∈ s, opP R (m j)) F z) := by
  funext z

  simp only [LinearMap.sum_apply, Finset.sum_apply, opP_map, map_sum]

theorem opL_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (N l : ℕ) (T : Letter)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opL S N l T (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opL R N l T F z) := by
  cases T with
  | T q =>
    simp only [opL, LinearMap.add_apply, sum_opP_map, opP_map]
    funext z; simp
  | U => simp only [opL, sum_opP_map]
  | D d => simp only [opL, opP_map]

end GlobalTheory.KZ.H3.LamStab


open GlobalTheory.KZ.H3 GlobalTheory.KZ.H3.LamStab in
theorem GlobalTheory.KZ.H3.lam_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)),
    p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l _ E _ _ T p hp
  let Φ : ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) →ₗ[E]
      ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
    LinearMap.prodMap (X.opV N l E T) (opL E N l T)
  have key : abelian₂ X l E ≤ (abelian₂ X l E).comap Φ := by
    unfold abelian₂
    rw [Submodule.span_le]
    rintro q ⟨b, F, hR, rfl⟩
    refine Submodule.subset_span ⟨X.op N l T b, opL ℤ_[l] N l T F,
      (GlobalTheory.T.kummerPotentialRelation_linear_hecke_stable Ω ε X l).2.2.2.2 N T b F hR, ?_⟩
    simp only [Φ, LinearMap.prodMap_apply, Tower.opV, LinearMap.baseChange_tmul, opL_map]
  exact key hp
