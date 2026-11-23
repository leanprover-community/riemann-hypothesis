module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.Tactic.Linter.Style
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

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.SwapInt

theorem isIntegral_map_semilinear {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] [Algebra O S]
    [Algebra O S'] (κ : O →+* O) (ψ : S →+* S')
    (hψ : ∀ o, ψ (algebraMap O S o) = algebraMap O S' (κ o)) {y : S} (h : IsIntegral O y) :
    IsIntegral O (ψ y) := by
  obtain ⟨p, hm, hp⟩ := h
  refine ⟨p.map κ, hm.map κ, ?_⟩
  rw [eval₂_map]
  have e : (algebraMap O S').comp κ = ψ.comp (algebraMap O S) := by
    ext o; simp [hψ]
  rw [e, ← hom_eval₂, hp, map_zero]

noncomputable def conjO (K : UQ) : K.O →+* K.O where
  toFun o := Classical.choose (K.c_int o)
  map_one' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 1)]; simp
  map_mul' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a * b)), map_mul, map_mul, map_mul,
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]
  map_zero' := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int 0)]; simp
  map_add' a b := by
    apply IsFractionRing.injective K.O K.E
    rw [← Classical.choose_spec (K.c_int (a + b)), map_add (f := _), map_add (f := _), map_add (f := _),
      ← Classical.choose_spec (K.c_int a), ← Classical.choose_spec (K.c_int b)]

theorem conjO_spec (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm

theorem sigma_algebraMap {K : UQ} (B : InvAlg K) (o : K.O) :
    B.σ (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) := by
  rw [IsScalarTower.algebraMap_apply K.O K.E B.A, B.σ_alg, ← conjO_spec,
    ← IsScalarTower.algebraMap_apply K.O K.E B.A]

end GlobalTheory.UnitLemma.SwapInt


open GlobalTheory.UnitLemma.SwapInt in
theorem GlobalTheory.UnitLemma.InvAlg.isIntegral_mk_comap_sigma_iff :
    ∀ (K : UQ) (B : InvAlg K) (m : MaximalSpectrum B.A) (x : B.A),
      IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap B.σ) x) ↔
        IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (B.σ x)) := by
  intro K B m x
  let σr : B.A →+* B.A := B.σ
  let ψ := Ideal.quotientMap m.asIdeal σr (le_refl (m.asIdeal.comap σr))
  have hm : m.asIdeal ≤ (m.asIdeal.comap σr).comap σr := by
    intro y hy
    simp only [Ideal.mem_comap]
    show B.σ (B.σ y) ∈ m.asIdeal
    rw [B.σ_σ]; exact hy
  let φ := Ideal.quotientMap (m.asIdeal.comap σr) σr hm
  have key : ∀ o : K.O, σr (algebraMap K.O B.A o) = algebraMap K.O B.A (conjO K o) :=
    sigma_algebraMap B
  constructor
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk (m.asIdeal.comap σr) x) := h
    have := isIntegral_map_semilinear (conjO K) ψ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [ψ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : ψ (Ideal.Quotient.mk (m.asIdeal.comap σr) x) = Ideal.Quotient.mk m.asIdeal (σr x) :=
      Ideal.quotientMap_mk
    rw [e2] at this
    exact this
  · intro h
    have h' : IsIntegral K.O (Ideal.Quotient.mk m.asIdeal (σr x)) := h
    have := isIntegral_map_semilinear (conjO K) φ (fun o => by
      rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap]
      simp only [φ]
      rw [Ideal.quotientMap_mk, key]) h'
    have e2 : φ (Ideal.Quotient.mk m.asIdeal (σr x)) = Ideal.Quotient.mk (m.asIdeal.comap σr) (σr (σr x)) :=
      Ideal.quotientMap_mk
    have e : σr (σr x) = x := B.σ_σ x
    rw [e2, e] at this
    exact this
