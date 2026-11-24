module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Valuation.ValuationSubring
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.UnramDiscr


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω)
    {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h : IsIntegral A x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact y.2


open NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.UnramDiscr.embedding_eq {K Ω : Type*} [Field K] [NumberField K]
    [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω)
    (hd : ¬ A.valuation ((discr K : ℤ) : Ω) < 1)
    (f g : K →+* Ω) (h : ∀ x : 𝓞 K, A.valuation (f x - g x) < 1) : f = g := by
  classical
  by_contra hfg
  set ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  have hcard : Fintype.card ι = Fintype.card (K →ₐ[ℚ] Ω) := by
    rw [AlgHom.card, ← RingOfIntegers.rank K, Module.finrank_eq_card_chooseBasisIndex]
  let e : ι ≃ (K →ₐ[ℚ] Ω) := Fintype.equivOfCardEq hcard
  let b := integralBasis K
  have hint : ∀ (φ : K →+* Ω) (x : 𝓞 K), φ x ∈ A := fun φ x =>
    _root_.GlobalTheory.UnramDiscr.mem_of_isIntegral A
      ((RingOfIntegers.isIntegral_coe x).map φ.toIntAlgHom)
  let N : Matrix ι ι A := Matrix.of fun i j => ⟨e j (b i), by
    rw [integralBasis_apply]; exact hint (e j).toRingHom _⟩
  have hM : ((discr K : ℤ) : Ω) = ((N.det ^ 2 : A) : Ω) := by
    have hdet := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ Ω b e
    rw [← coe_discr] at hdet
    have hN : A.subtype.mapMatrix N = Algebra.embeddingsMatrixReindex ℚ Ω b e := by
      ext i j
      simp [N, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
    rw [map_intCast, ← hN, ← RingHom.map_det] at hdet
    rw [hdet]
    simp
  have hF : f.toRatAlgHom ≠ g.toRatAlgHom := by
    intro hc
    apply hfg
    ext x
    exact congrArg (fun φ : K →ₐ[ℚ] Ω => φ x) hc
  have hres : ((IsLocalRing.residue A).mapMatrix N).det = 0 := by
    apply Matrix.det_zero_of_column_eq (i := e.symm f.toRatAlgHom) (j := e.symm g.toRatAlgHom)
    · simpa using hF
    · intro k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, N, Matrix.of_apply]
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
      simpa [b, integralBasis_apply] using h (RingOfIntegers.basis K k)
  rw [← RingHom.map_det, IsLocalRing.residue_eq_zero_iff] at hres
  apply hd
  rw [hM, ← A.valuation_lt_one_iff]
  exact Ideal.pow_mem_of_mem _ hres 2 (by norm_num)

end GlobalTheory.UnramDiscr
