module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFiltrationSpanDeRhamLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusActionMulOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusBasisTensorLatticeFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordinatesEqOfEisensteinPowMulInverseMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationVStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisinStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfMutualSpanOfIndepStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis {R W : Type} [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w) (eD : R)
    (hbij : Function.Bijective (act eD)) (F : ℤ → W → Prop) (hshift : ∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y))
    {ι : Type} [Fintype ι] [DecidableEq ι] (β β₀ : ℕ) (g h b : ι → W) (hg : ∀ i, act (eD ^ β₀) (g i) = h i)
    (hspan : ∀ w, F ((β₀ + β : ℕ) : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i))
    (hb0 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k))
    (hbi : ∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) :
    ∃ f : ι → W, (∀ i, act (eD ^ β) (f i) = g i) ∧ (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (f i)) ∧
      ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  have hcomm : ∀ (d d' : R) (w : W), act d (act d' w) = act d' (act d w) := by
    intro d d' w
    rw [← hmul, ← hmul, mul_comm]
  have hpow : ∀ (n : ℕ) (w : W), act (eD ^ n) w = (act eD)^[n] w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, hone]; rfl
    | succ n ih => intro w; rw [pow_succ', hmul, ih, Function.iterate_succ_apply']
  have hinj : ∀ n : ℕ, Function.Injective (act (eD ^ n)) := by
    intro n x x' hxx
    rw [hpow, hpow] at hxx
    exact (hbij.1.iterate n) hxx
  have hsh : ∀ (n : ℕ) (w : W) (j : ℤ), F j w ↔ F (j + n) (act (eD ^ n) w) := by
    intro n
    induction n with
    | zero => intro w j; rw [pow_zero, hone, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro w j
      rw [ih w j, hshift (act (eD ^ n) w) (j + n), pow_succ', hmul, Nat.cast_succ, ← add_assoc]
  have hsingle : ∀ (v : ι → W) (i : ι), ∑ k, act ((Pi.single i (1 : R) : ι → R) k) (v k) = v i := by
    intro v i
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, AddMonoidHom.zero_apply])
      (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, hone]
  let ginv : W → W := (Equiv.ofBijective _ hbij).symm
  have hginv : ∀ x, act eD (ginv x) = x := fun x => (Equiv.ofBijective _ hbij).apply_symm_apply x
  have h1 : ∀ i, act (eD ^ β) (ginv^[β] (g i)) = g i := by
    intro i
    rw [hpow]
    exact Function.RightInverse.iterate hginv β _
  have h2 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (ginv^[β] (g i)) := by
    have hf : ∀ i, act (eD ^ (β₀ + β)) (ginv^[β] (g i)) = h i := by
      intro i
      rw [pow_add, hmul, hpow β, Function.RightInverse.iterate hginv β, hg]
    intro v
    rw [hsh (β₀ + β) v 0, zero_add, hspan]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, hinj (β₀ + β) ?_⟩

      rw [hd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩

      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
  refine ⟨fun i => ginv^[β] (g i), h1, h2, ?_⟩
  refine GlobalTheory.T.linearIndependent_of_mutual_span_of_indep R W act hmul hone ι b _ hbi ?_ ?_
  · intro i
    exact (hb0 _).1 ((h2 _).2 ⟨Pi.single i 1, (hsingle (fun i => ginv^[β] (g i)) i).symm⟩)
  · intro k
    exact (h2 _).1 ((hb0 _).2 ⟨Pi.single k 1, (hsingle b k).symm⟩)


private theorem mulVec_smul_single_one_apply {R ι : Type} [CommSemiring R] [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (r : R) (i j : ι) :
    (M *ᵥ (r • Pi.single i 1)) j = r * M j i := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_single_one]
  rfl

private theorem map_pow_mul_of_eq {R S : Type} [Semiring R] [Semiring S]
    (f : R →+* S) (z y : R) (w : S) (n m : ℕ) (h : f y = f z ^ m * w) :
    f (z ^ n * y) = f z ^ (n + m) * w := by
  rw [map_mul, map_pow, h, pow_add, mul_assoc]

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.BKGal.JumpDR.basis_images : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI Td hC X hX act hA β y hy
  have hAct := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  have hE := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  have hExp := P.exists_exponents
  refine hExp.elim fun α h => h.elim fun β0 hBounds => ?_
  have hLM1 : ∀ v ∈ P.M, E ↥LL.1 l e ^ (β0 + β) • v ∈ P.L := by
    intro v hv
    have := P.L.smul_mem (⟨_, pow_mem (E_mem l e _) β⟩ : A ↥(OL LL) ↥LL.1) (hBounds.2 v hv)
    rw [pow_add, mul_comm, mul_smul]
    exact this
  have hβ1 : ∀ τ j i, E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1 := by
    intro τ j i
    let v : ι → (↥LL.1)⟦X⟧ := Pi.single i 1
    have hv : (fun _ : ZMod a => v) ∈ P.M :=
      (mem_tot (P := fun _ => Mc ↥(OL LL) ↥LL.1 ι)).2 fun _ =>
        (mem_vecs (B := A ↥(OL LL) ↥LL.1)).2 fun k => by
          change (Pi.single i (1 : (↥LL.1)⟦X⟧) : ι → (↥LL.1)⟦X⟧) k ∈ A ↥(OL LL) ↥LL.1
          by_cases hk : k = i
          · rw [hk, Pi.single_eq_same]
            exact one_mem _
          · rw [Pi.single_eq_of_ne hk]
            exact zero_mem _
    have hw := (mem_tot (P := P.extc (A ↥(OL LL) ↥LL.1))).1 (hLM1 _ hv) τ
    have hmem := (mem_vecs (B := A ↥(OL LL) ↥LL.1)).1 (P.mem_extc_iff.1 hw) j
    exact (congrArg (fun z : (↥LL.1)⟦X⟧ => z ∈ A ↥(OL LL) ↥LL.1)
      (mulVec_smul_single_one_apply (P.mxInv τ) (E ↥LL.1 l e ^ (β0 + β)) i j)).mp hmem
  let eHat := Ehat ↥(OL LL) ↥LL.1 l e
  let loc := algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
  let yScaled (τ : ZMod a) (j i : ι) := eHat ^ β0 * y τ j i
  have hy1 (τ : ZMod a) (j i : ι) :=
    map_pow_mul_of_eq loc eHat (y τ j i) (hat ↥(OL LL) l e (P.mxInv τ j i)) β0 β (hy τ j i)
  have hyA := GlobalTheory.T.coordinates_eq_of_eisensteinPow_mul_inverse_matrix l a e ϖ LL ι P
    (β0 + β) yScaled hy1 hβ1
  let iD := ϖ.iD (thetaW a LL) ↥LL.1
  let constantEhat : ZMod a → Ahat ↥(OL LL) ↥LL.1 l e := fun _ => eHat
  let eD := iD constantEhat
  let x (j : ι) := X (jB (Pi.single j 1))
  let c (j i : ι) (τ : ZMod a) : A ↥(OL LL) ↥LL.1 :=
    ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩
  let d (j i : ι) := iD (fun τ => y τ j i)
  let d' (j i : ι) := toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (c j i))
  let g (i : ι) := ∑ j, act (d j i) (x j)
  let h (i : ι) := ∑ j, act (d' j i) (x j)
  have hcoeff (j i : ι) : eD ^ β0 * d j i = d' j i := by
    have hpt : constantEhat ^ β0 * (fun τ => y τ j i) =
        fun τ => ofA ↥(OL LL) ↥LL.1 l e (c j i τ) :=
      funext fun τ => hyA τ j i
    calc
      _ = iD (constantEhat ^ β0) * d j i :=
        congrArg (fun z => z * d j i) (map_pow iD constantEhat β0).symm
      _ = iD (constantEhat ^ β0 * (fun τ => y τ j i)) :=
        (map_mul iD (constantEhat ^ β0) (fun τ => y τ j i)).symm
      _ = iD (fun τ => ofA ↥(OL LL) ↥LL.1 l e (c j i τ)) := congrArg iD hpt
      _ = _ := PiSys.iD_ofA (thetaW a LL) ↥LL.1 ϖ (c j i)
  have hg (i : ι) : act (eD ^ β0) (g i) = h i :=
    (map_sum (act (eD ^ β0)) (fun j => act (d j i) (x j)) (Finset.univ : Finset ι)).trans
      (Finset.sum_congr rfl fun j _ =>
        (hAct.1 (eD ^ β0) (d j i) (x j)).symm.trans (congrArg (fun z => act z (x j)) (hcoeff j i)))
  have hspan := GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice hF l a e ϖ LL hl2 ι P T I
    jB Pl AI Td hC X hX act hA α (β0 + β) hBounds.1 hLM1 hβ1
  have hBasis := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  refine hBasis.elim fun b => ?_
  have hb := GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b
  exact GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis act hAct.1 hAct.2 eD hE.1
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) =>
      v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j)
    hE.2 β β0 g h
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) hg hspan hb.1 hb.2

end
