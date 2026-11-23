module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RetractAcyc

def resMapRetractHomotopy (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M) :
    Homotopy (resMap R i ≫ resMap R r) (𝟙 (res R M)) := by
  have H : Homotopy (InjectiveResolution.desc i (injectiveResolution M') (injectiveResolution M) ≫
      InjectiveResolution.desc r (injectiveResolution M) (injectiveResolution M'))
      (𝟙 (injectiveResolution M).cocomplex) :=
    (InjectiveResolution.descCompHomotopy i r _ _ _).symm.trans
      (by rw [h]; exact InjectiveResolution.descIdHomotopy _ _)
  have H2 := H.extend ComplexShape.embeddingUpNat
  rw [HomologicalComplex.extendMap_comp, HomologicalComplex.extendMap_id] at H2
  exact H2

theorem post_post_of_retract (R : Type) [CommRing R] {M M' : Shv R} (i : M ⟶ M') (r : M' ⟶ M) (h : i ≫ r = 𝟙 M)
    (K : Cx R) (n : ℤ) (x : HK R K M n) : HK.post R K r n (HK.post R K i n x) = x := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  have Hh := resMapRetractHomotopy R i r h
  change CohomologyClass.mk (zcomp (zcomp α (Cocycle.ofHom (resMap R i)) (add_zero n))
    (Cocycle.ofHom (resMap R r)) (add_zero n)) = CohomologyClass.mk α
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨α.1.comp (Cochain.ofHomotopy Hh) (by omega), ?_⟩
  rw [δ_comp _ _ _ (n + 1) 0 n (by omega) rfl (by omega), Cocycle.δ_eq_zero, δ_ofHomotopy]
  ext p q hpq
  simp [zcomp, Cochain.comp_v _ _ (add_zero n) p q q hpq (add_zero q)]

theorem subsingleton_of_retract : ∀ (R : Type) [CommRing R] (M M' : Shv R) (i : M ⟶ M') (r : M' ⟶ M), i ≫ r = 𝟙 M →
    ∀ (K : Cx R) (n : ℤ), Subsingleton (HK R K M' n) → Subsingleton (HK R K M n) := by
  intro R _ M M' i r h K n hs
  exact (Function.LeftInverse.injective (g := HK.post R K r n) (f := HK.post R K i n)
    (post_post_of_retract R i r h K n)).subsingleton

end GlobalTheory.EtC.RetractAcyc
