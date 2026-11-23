module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ExistsIntegralBlockIwasawaDecomposition
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FlagFDiagonalise
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem flagBasis_diag_mul {F : Type} [Field F] {n : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem flagBasis_conj {F : Type} [Field F] {n : ℕ} (b t : GL (Fin n) F)
    (hb : ∀ i j, j < i → b i j = 0) (ht : ∀ i j, j < i → t i j = 0) :
    (∀ i j, j < i → (b⁻¹ * t * b : GL (Fin n) F) i j = 0) ∧
      ∀ i, (b⁻¹ * t * b : GL (Fin n) F) i i = t i i := by
  have hbm : (b : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => hb i j h
  have htm : (t : Matrix (Fin n) (Fin n) F).BlockTriangular id := fun i j h => ht i j h
  have hbi : ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).BlockTriangular id := by
    letI := b.invertible
    rw [Matrix.coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hbm
  have hdiag : ∀ i, ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i *
      (b : Matrix (Fin n) (Fin n) F) i i = 1 := by
    intro i
    rw [← flagBasis_diag_mul hbi hbm, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_apply_eq]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact ((hbi.mul htm).mul hbm) hij
  · rw [Units.val_mul, Units.val_mul, flagBasis_diag_mul (hbi.mul htm) hbm,
      flagBasis_diag_mul hbi htm, mul_right_comm, hdiag, one_mul]

theorem UpperTheory.V.Pa.Det.flagBasis :
    ∀ {K H : Type} [Field K] [Group H] {n a : ℕ} (r : H →* GL (Fin n) (PowerSeries K)) (ψ : Fin n → H →* (PowerSeries K)ˣ), (∀ g, mat r g ∈ Ev (PowerSeries K) (PowerSeries K) n a) → Function.Injective ψ → HasFlag (pushRep (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) r) (fun i => pushCh (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) (ψ i)) → ∃ (w : GL (Fin n) (PowerSeries K)) (ty : Fin n → Bool), (∀ i j : Fin n, decide ((i : ℕ) < a) ≠ ty j → w i j = 0) ∧ ∀ g, (∀ i j, j < i → (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j = 0) ∧ ∀ i, (w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i i = (ψ i g : PowerSeries K) := by
  intro K H _ _ n a r ψ hev hinj hflag
  set ι := algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) with hι
  have hιi : Function.Injective ι := IsFractionRing.injective _ _
  haveI : Infinite (FractionRing (PowerSeries K)) := by
    refine Infinite.of_injective (fun m : ℕ => ι (PowerSeries.X ^ m)) ?_
    intro m k hmk
    have h := congrArg (fun p => PowerSeries.coeff (R := K) m p) (hιi hmk)
    simp only [PowerSeries.coeff_X_pow, if_true] at h
    by_contra hne
    rw [if_neg hne] at h
    exact one_ne_zero h
  have hev' : ∀ g, mat (pushRep ι r) g ∈ Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a := by
    intro g
    have hg := hev g
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
    have h0 := (Submodule.mem_bot _).1 ((hg i j).2 h)
    have e : mat (pushRep ι r) g i j = ι (mat r g i j) := rfl
    rw [e, h0, map_zero]
    exact Submodule.zero_mem _
  have hψ : Function.Injective (fun i => pushCh ι (ψ i)) := by
    intro i j hij
    apply hinj
    ext g
    have := congrArg (fun f : H →* (FractionRing (PowerSeries K))ˣ => ((f g : (FractionRing (PowerSeries K))ˣ) : FractionRing (PowerSeries K))) hij
    rw [hιi this]
  obtain ⟨w0, ty, hw0, htri⟩ := Det.flagF (pushRep ι r) (fun i => pushCh ι (ψ i)) hev' hψ hflag
  obtain ⟨w, b, hb, hwb, hw⟩ :=
    Det.exists_integral_block_iwasawa_decomposition (A := PowerSeries K) (fun i : Fin n => decide ((i : ℕ) < a)) ty w0 hw0
  refine ⟨w, ty, hw, fun g => ?_⟩
  have hmap : GeneralLinearGroup.map ι (w⁻¹ * r g * w) = b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b := by
    rw [map_mul, map_mul, map_inv, hwb, _root_.mul_inv_rev]
    simp only [pushRep, MonoidHom.comp_apply, mul_assoc]
  have hent : ∀ i j, ι ((w⁻¹ * r g * w : GL (Fin n) (PowerSeries K)) i j) =
      (b⁻¹ * (w0⁻¹ * pushRep ι r g * w0) * b : GL (Fin n) (FractionRing (PowerSeries K))) i j := by
    intro i j
    rw [← hmap]
    rfl
  obtain ⟨hc1, hc2⟩ := flagBasis_conj b (w0⁻¹ * pushRep ι r g * w0) hb (htri g).1
  refine ⟨fun i j hij => hιi ?_, fun i => hιi ?_⟩
  · rw [hent, hc1 i j hij, map_zero]
  · rw [hent, hc2 i, (htri g).2 i]
    rfl
