module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.exists_integral_block_iwasawa_decomposition :
    ∀ {A F : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Algebra A F] [IsFractionRing A F] {n : ℕ} (bl ty : Fin n → Bool) (g : GL (Fin n) F), (∀ i j, bl i ≠ ty j → g i j = 0) → ∃ (w : GL (Fin n) A) (b : GL (Fin n) F), (∀ i j, j < i → b i j = 0) ∧ GeneralLinearGroup.map (algebraMap A F) w = g * b ∧ ∀ i j, bl i ≠ ty j → w i j = 0 := by
  intro A F _ _ _ _ _ _ n bl ty g hg
  obtain ⟨k, b0, hb0, hgkb⟩ := GlobalTheory.ValIwasawa.iwasawa A F n g
  haveI : Invertible (b0 : Matrix (Fin n) (Fin n) F) := Units.invertible b0
  have hctri : ((b0 : Matrix (Fin n) (Fin n) F)⁻¹).BlockTriangular id :=
    Matrix.blockTriangular_inv_of_blockTriangular hb0
  set c : Matrix (Fin n) (Fin n) F := (b0 : Matrix (Fin n) (Fin n) F)⁻¹ with hcdef
  have hgc : (g : Matrix (Fin n) (Fin n) F) * c = (GeneralLinearGroup.map (algebraMap A F) k : Matrix (Fin n) (Fin n) F) := by
    have h1 : g * b0⁻¹ = GeneralLinearGroup.map (algebraMap A F) k := mul_inv_eq_iff_eq_mul.mpr hgkb
    have h2 := congrArg (fun x : GL (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h1
    simpa [Units.val_mul, Matrix.coe_units_inv, hcdef] using h2
  let c' : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => if ty i = ty j then c i j else 0
  have hc'tri : c'.BlockTriangular id := by
    intro i j hij
    simp only [c', Matrix.of_apply]
    split_ifs
    · exact hctri hij
    · rfl
  have hgc' : ∀ i j, ((g : Matrix (Fin n) (Fin n) F) * c') i j = if bl i = ty j then algebraMap A F ((k : Matrix (Fin n) (Fin n) A) i j) else 0 := by
    intro i j
    rw [Matrix.mul_apply]
    split_ifs with hij
    · rw [← GeneralLinearGroup.map_apply, ← hgc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rfl
      · rw [hg i l (fun h => hl (h.symm.trans hij)), zero_mul, zero_mul]
    · refine Finset.sum_eq_zero fun l _ => ?_
      simp only [c', Matrix.of_apply]
      split_ifs with hl
      · rw [hg i l (fun h => hij (h.trans hl)), zero_mul]
      · rw [mul_zero]
  let kw : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => if bl i = ty j then (k : Matrix (Fin n) (Fin n) A) i j else 0
  have hmap : (algebraMap A F).mapMatrix kw = (g : Matrix (Fin n) (Fin n) F) * c' := by
    ext i j
    rw [hgc' i j]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, kw, Matrix.of_apply]
    split_ifs
    · rfl
    · exact map_zero _
  have hdetc : c'.det = c.det := by
    rw [Matrix.det_of_upperTriangular hc'tri, Matrix.det_of_upperTriangular hctri]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [c']
  have hcunit : IsUnit c.det := by
    have := Matrix.isUnits_det_units b0⁻¹
    rwa [Matrix.coe_units_inv] at this
  have hc'unit : IsUnit c'.det := hdetc ▸ hcunit
  have hdetk : kw.det = (k : Matrix (Fin n) (Fin n) A).det := by
    apply IsFractionRing.injective A F
    rw [RingHom.map_det, RingHom.map_det, hmap, Matrix.det_mul, hdetc, ← Matrix.det_mul, hgc]
    rfl
  have hkunit : IsUnit kw.det := hdetk ▸ Matrix.isUnits_det_units k
  refine ⟨GeneralLinearGroup.mk'' kw hkunit, GeneralLinearGroup.mk'' c' hc'unit, ?_, ?_, ?_⟩
  · intro i j hij
    exact hc'tri hij
  · apply Units.ext
    rw [Units.val_mul]
    exact hmap
  · intro i j hij
    show kw i j = 0
    simp [kw, hij]
