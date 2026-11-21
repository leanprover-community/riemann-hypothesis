import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThA
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixW_C
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesCompactOfLocalBounds

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

section GlobalTheory

variable {R : Type}

theorem block_matrix_apply_top_right (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (Fin.castAdd n i) (Fin.natAdd n j) = b i j := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₂]

theorem submatrix_fromBlocks_mul [Ring R] (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one [Ring R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  delta GlobalTheory.StdUnn.blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

end GlobalTheory

theorem adj_neg_one : adj (-1 : Mx D n n) = -1 := by
  show (Matrix.map (-1 : Mx D n n) ⇑(Formalism.L2.Theta.cA D)).transpose = -1
  rw [show Matrix.map (-1 : Mx D n n) ⇑(Formalism.L2.Theta.cA D) = (Formalism.L2.Theta.cA D).mapMatrix (-1) from rfl,
    map_neg, map_one, Matrix.transpose_neg, Matrix.transpose_one]

private theorem blk4_neg_one_lemma {R : Type} [Ring R] :
    blk4 (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = -1 := by
  rw [← block_matrix_one (R := R) (n := n)]
  delta GlobalTheory.StdUnn.blk4
  rw [show Matrix.fromBlocks (-1 : Matrix (Fin n) (Fin n) R) 0 0 (-1) = -Matrix.fromBlocks 1 0 0 1 by
    rw [Matrix.fromBlocks_neg, neg_zero]]
  exact congrFun (congrFun (Matrix.submatrix_neg _) _) _

theorem mat_ww {w : G D p} (hw : IsW w) :
    mat (w * w)⁻¹ = blk4 ((-1 : GL (Fin p) (AE D)) : Matrix _ _ _) 0 0 (adj (((-1 : GL (Fin p) (AE D))⁻¹ : GL _ _) : Matrix _ _ _)) := by
  have hM : mat (w * w) = -1 := by
    rw [mat_mul, show mat w = blk4 0 1 (-1) 0 from hw, submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero]
    exact blk4_neg_one_lemma
  have h1 := mat_mul_inv (w * w)
  rw [hM, neg_one_mul, neg_eq_iff_eq_neg] at h1
  rw [h1, inv_neg_one, Units.val_neg, Units.val_one, adj_neg_one, blk4_neg_one_lemma]

theorem good_neg {S : Finset (Pl D)} {e : AE D} {f : Mx D ρ p → ℂ} (hf : Good S e f) (c : ℂ) :
    Good S e (fun z => c * f (-z)) := by
  delta PositivityTheory.Rg.Rsw.L.Good at hf ⊢
  intro x
  beta_reduce
  have hi : IntOff S (-x) ↔ IntOff S x := by
    delta PositivityTheory.Rg.Rsw.L.IntOff
    constructor
    · intro H v hv i j
      have h1 := neg_mem (H v hv i j)
      rwa [Matrix.neg_apply, map_neg, neg_neg] at h1
    · intro H v hv i j
      rw [Matrix.neg_apply, map_neg]
      exact neg_mem (H v hv i j)
  have h := hf (-x)
  by_cases hx : IntOff S x
  · rw [if_pos hx, h, if_pos (hi.2 hx), smul_neg]
  · rw [if_neg hx, h, if_neg (fun H => hx (hi.1 H)), mul_zero]

theorem kOff_entry {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) (k l : Fin (n + n)) :
    (∀ w, compInf D.host.F D.host.E w (mat g k l) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) k l) ∧
    (∀ v ∈ S, cv D v (mat g k l) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) k l) ∧
    (∀ v ∉ S, cv D v (mat g k l) ∈ intLoc D.host.F D.host.E v) := by
  exact ⟨fun w => kOff_inf hg w k l, fun v hv => kOff_at hg hv k l, fun v hv => (kOff_int hg hv k l).1⟩

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {ρ p n : ℕ}

instance finDim (D : D7) : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _

structure GoodPl (χ : (AE D)ˣ →* Circle) (b₀ : HermE D ρ) (v : Pl D) : Prop where
  good : LFixW.IsGood D.host.F D.host.E v
  unr : ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1
  bint : ∀ i j, inclR (Fv D.host.F v) (b₀.1 i j) ∈ intLoc D.host.F D.host.E v

theorem eventually_unr {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) :
    ∀ᶠ v in cofinite, ∀ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u = 1 := by
  classical
  let m : Pl D → (AE D)ˣ := fun v =>
    if h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 then h.choose else 1
  have hm : ∀ v, m v ∈ GlobalTheory.ThK.unitsAt D.host.E v := fun v => by
    simp only [m]
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_mem _
  filter_upwards [GlobalTheory.ThK.ConeEulerChr.eventually_chr_eq_one (ν := χ) hχ.1 m (Eventually.of_forall hm)] with v hv u hu
  by_contra hne
  have h : ∃ u ∈ GlobalTheory.ThK.unitsAt D.host.E v, χ u ≠ 1 := ⟨u, hu, hne⟩
  have e : m v = h.choose := dif_pos h
  exact h.choose_spec.2 (e ▸ hv)

theorem eventually_goodPl {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (b₀ : HermE D ρ) :
    ∀ᶠ v in cofinite, GoodPl χ b₀ v := by
  filter_upwards [LFixW.eventually_good (F := D.host.F) (E := D.host.E), eventually_unr hχ,
    eventually_all.2 fun i => eventually_all.2 fun j =>
      GlobalTheory.AdelicU.SelfDual.eventually_mem_intLoc (F := D.host.F) (b₀.1 i j)] with v h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem adj_apply (x : Mx D ρ p) (i : Fin p) (j : Fin ρ) : adj x i j = cA D (x j i) := rfl

theorem cv_cA (v : Pl D) (x : AE D) : cv D v (cA D x) = sigR (Fv D.host.F v) D.sp.cm.sig (cv D v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (cA D), map_add (cv D v), map_add (cv D v), hx, hy, map_add (sigR (Fv D.host.F v) D.sp.cm.sig)]

theorem one_cn {R : Type} [Ring R] (i j : Fin n) :
    (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) (Fin.castAdd n i) (Fin.natAdd n j) = 0 := by
  rw [← block_matrix_one (R := R), block_matrix_apply_top_right, Matrix.zero_apply]

theorem unip_one {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {b₀ : HermE D ρ} {S : Finset (Pl D)}
    (hS : ∀ v ∉ S, GoodPl χ b₀ v)
    (hker : ∀ y : AF D.host.F, y.1 = 0 → (∀ v ∈ S, y.2 v = 0) →
      (∀ v ∉ S, y.2 v ∈ v.adicCompletionIntegers D.host.F) → ψ y = 1)
    {g : G D p} (hg : g ∈ KOff D p S) {b : Mx D p p} (hb : mat g = blk4 1 b 0 1) {y : Mx D ρ p} (hy : IntOff S y) :
    ψ (halfTr (b * pr b₀ y y).trace) = 1 := by
  have hbe : ∀ i j, b i j = mat g (Fin.castAdd p i) (Fin.natAdd p j) := fun i j => by rw [hb, block_matrix_apply_top_right]
  have hbInf : ∀ w i j, compInf D.host.F D.host.E w (b i j) = 0 := fun w i j => by
    rw [hbe, (kOff_entry hg _ _).1 w, one_cn]
  have hbS : ∀ v ∈ S, ∀ i j, cv D v (b i j) = 0 := fun v hv i j => by
    rw [hbe, (kOff_entry hg _ _).2.1 v hv, one_cn]
  have hbI : ∀ v ∉ S, ∀ i j, cv D v (b i j) ∈ intLoc D.host.F D.host.E v := fun v hv i j => by
    rw [hbe]; exact (kOff_entry hg _ _).2.2 v hv
  have hPI : ∀ v ∉ S, ∀ k i, cv D v (pr b₀ y y k i) ∈ intLoc D.host.F D.host.E v := by
    intro v hv k i
    simp only [pr, Matrix.mul_apply, map_sum, map_mul]
    refine sum_mem fun l _ => mul_mem ?_ (sum_mem fun m _ => mul_mem ?_ (hy v hv m i))
    · rw [adj_apply, cv_cA]; exact sigR_mem_intLoc _ (hy v hv l k)
    · rw [Matrix.map_apply]; exact (hS v hv).bint l m
  have hX : ∀ (R : Type) [CommRing R] (f : AE D →+* R), f (b * pr b₀ y y).trace =
      ∑ i, ∑ k, f (b i k) * f (pr b₀ y y k i) := fun R _ f => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]
  have hXinf : ∀ w, compInf D.host.F D.host.E w (b * pr b₀ y y).trace = 0 := fun w => by
    rw [hX]; simp [hbInf]
  have hXS : ∀ v ∈ S, cv D v (b * pr b₀ y y).trace = 0 := fun v hv => by
    rw [hX]; simp [hbS v hv]
  have hXI : ∀ v ∉ S, cv D v (b * pr b₀ y y).trace ∈ intLoc D.host.F D.host.E v := fun v hv => by
    rw [hX]; exact sum_mem fun i _ => sum_mem fun k _ => mul_mem (hbI v hv i k) (hPI v hv k i)
  apply hker
  · refine funext fun w => ?_
    change evInf D.host.F w (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evInf_apply w (trA _), LFixW.trA_fst, hXinf, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) = 0
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, hXS v hv, map_zero, mul_zero]
  · intro v hv
    change evFin D.host.F v (algebraMap D.host.F (AF D.host.F) (1 / 2) * trA (b * pr b₀ y y).trace) ∈ _
    rw [map_mul, LFixW.evFin_apply v (trA _), LFixW.trA_snd, AlgHom.commutes, one_div]
    exact mul_mem (hS v hv).good.half (LFixW.trace_mem (hS v hv).good (hXI v hv))

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end
