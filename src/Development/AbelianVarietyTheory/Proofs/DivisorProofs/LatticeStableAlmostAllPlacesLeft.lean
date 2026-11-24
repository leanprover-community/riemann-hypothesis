module

import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetAdelicUnitaryPreservesLatticeAlmostA
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

open scoped TensorProduct
open Matrix
namespace GlobalTheory.AdelMatLat

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (v : Fin n → E) : ∃ d : ℤ, d ≠ 0 ∧ d • v ∈ L := by
  apply GlobalTheory.LatAlmostAll.exists_int_smul_mem <;> assumption

theorem exists_int_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsFullLattice E) (N : Matrix (Fin n) (Fin n) E) : ∃ D : ℤ, D ≠ 0 ∧ ∀ x ∈ L, D • (N *ᵥ x) ∈ L := by
  apply GlobalTheory.LatAlmostAll.exists_int_mulVec_mem <;> assumption

theorem incM_zsmul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m k : Type}
    (D : ℤ) (V : Matrix m k E) : incM F (D • V) = (algebraMap F (AF F) (D : F)) • incM F V := by
  ext i j
  simp only [incM, Matrix.map_apply, Matrix.smul_apply, map_zsmul, algebraMap_smul, Int.cast_smul_eq_zsmul]

theorem smul_incM_mul_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (c : AF F) (N : Matrix (Fin n) (Fin n) E) (D : ℤ) (hD0 : D ≠ 0)
    (hD : ∀ x ∈ X.L, D • (N *ᵥ x) ∈ X.L) (w : Pl (F := F))
    (hw : evFin F w (c * algebraMap F (AF F) (D : F)⁻¹) ∈ w.adicCompletionIntegers F) :
    ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hint, x, hx, y, hy, rfl⟩ := hz
    have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD0
    have heq : (c • incM F N) * (a • incM F (Matrix.vecMulVec x y)) =
        ((c * algebraMap F (AF F) (D : F)⁻¹) * a) • incM F (Matrix.vecMulVec (D • (N *ᵥ x)) y) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_vecMulVec, incM_zsmul, smul_smul,
        ← Matrix.mul_vecMulVec]
      have hm : incM F (N * Matrix.vecMulVec x y) = incM F N * incM F (Matrix.vecMulVec x y) := by
        simp only [incM, Matrix.map_mul]
      rw [hm]
      congr 1
      rw [mul_right_comm, mul_assoc c, ← map_mul, inv_mul_cancel₀ hDF, map_one, mul_one]
    rw [heq]
    refine AddSubgroup.subset_closure ⟨_, ?_, ?_, _, hD x hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u a, ha u hu, mul_zero]
    · rw [map_mul]
      exact mul_mem hw hint
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem finite_not_integral {F : Type} [Field F] [NumberField F] (c : AF F) :
    {w : Pl (F := F) | evFin F w c ∉ w.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.1 c.2.2

theorem finite_bad_smul_incM {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsFullLattice E) (c : AF F) (N : Matrix (Fin n) (Fin n) E) :
    {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, (c • incM F N) * γ ∈ latAtV X Y w}.Finite := by
  obtain ⟨D, hD0, hD⟩ := exists_int_mulVec_mem X.L hX N
  refine (finite_not_integral (c * algebraMap F (AF F) (D : F)⁻¹)).subset ?_
  intro w hw hint
  exact hw (smul_incM_mul_stable X Y c N D hD0 hD w hint)

theorem almost_all_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : Spc F E n) (Y : Spc F E d), X.L.IsFullLattice E → ∀ M : Matrix (Fin n) (Fin n) (AE F E),
    Set.Finite {w : Pl (F := F) | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w} := by
  intro F E _ _ _ _ _ n d X Y hX M
  let bad : Matrix (Fin n) (Fin n) (AE F E) → Set (Pl (F := F)) :=
    fun M => {w | ¬ ∀ γ ∈ latAtV X Y w, M * γ ∈ latAtV X Y w}
  have hadd : ∀ M M', (bad M).Finite → (bad M').Finite → (bad (M + M')).Finite := by
    intro M M' h h'
    refine (h.union h').subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, not_or, bad, Set.mem_setOf_eq, not_not] at hc hw
    exact hw fun γ hγ => by rw [Matrix.add_mul]; exact add_mem (hc.1 γ hγ) (hc.2 γ hγ)
  have hzero : (bad 0).Finite := by
    refine Set.finite_empty.subset fun w hw => hw fun γ _ => ?_
    rw [Matrix.zero_mul]; exact zero_mem _
  have hsingle : ∀ i j (t : AE F E), (bad (Matrix.single i j t)).Finite := by
    intro i j t
    induction t using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact hzero
    | tmul a e =>
      have h : Matrix.single i j (a ⊗ₜ[F] e) = a • incM F (Matrix.single i j e) := by
        ext k l
        simp only [incM, Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply]
        split_ifs <;> simp [inclR, TensorProduct.smul_tmul']
      rw [h]
      exact finite_bad_smul_incM X Y hX a _
    | add t t' ht ht' => rw [Matrix.single_add]; exact hadd _ _ ht ht'
  show (bad M).Finite
  rw [Matrix.matrix_eq_sum_single M]
  exact Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun i _ =>
    Finset.sum_induction _ (fun M => (bad M).Finite) hadd hzero fun j _ => hsingle i j _

end GlobalTheory.AdelMatLat

end
