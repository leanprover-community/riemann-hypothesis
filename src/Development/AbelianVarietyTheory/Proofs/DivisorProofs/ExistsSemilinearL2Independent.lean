import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CnormMapConjMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdZeroOfPetAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarCuspFormIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvertibleSectionValuationNonnegStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyWeightSectionProductsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmPointNonvanishingSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroEvalFrNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedSectionExponentShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenomFramePolynomialsCmPoint

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

namespace GlobalTheory.HSApp.GapArith

theorem gap_add {N : ℕ} (v w : Fin N → ℤ) (k : ℕ) : gap (v + w) k = gap v k + gap w k := by
  unfold gap
  split_ifs
  · simp only [Pi.add_apply]; ring
  · simp

theorem gap_nsmul {N : ℕ} (n : ℕ) (v : Fin N → ℤ) (k : ℕ) : gap (n • v) k = (n : ℤ) * gap v k := by
  unfold gap
  split_ifs
  · simp only [Pi.smul_apply, nsmul_eq_mul]; ring
  · simp



end GlobalTheory.HSApp.GapArith
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.PetRep
open MeasureTheory

section Gen

open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

end Gen

set_option maxHeartbeats 2000000 in

theorem adelMeas_one_of_good {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (h : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    AdelMeas Y.U σ (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) := by
  obtain ⟨th, hr, hth, hd⟩ := h.dictU σ hσ
  have hN : 0 < D.host.g 0 * D.host.g 1 * Y.d.pd := by
    rw [h.pd]
    exact Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) (pow_pos (by norm_num) _)
  have hL := GlobalTheory.DictLocTest.locClause_of_unif_places hd (fun k hk => ((h.levelK k).1 hk).1)
    (GlobalTheory.LevelNbhd.level_mul_inf_mem_nhds D _ _ Y.Kf hN h.levelK) (fun c τ => ⟨_, hth c τ⟩)
  exact adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ)
    (GlobalTheory.PetDef.adelAut_of_gamma (fun k la γ hγ => GlobalTheory.CovTop.Model.chi_eq_one h σ hσ k la γ hγ) hd
      (GlobalTheory.PetDef.muUnit_one Y h σ hσ) hL continuous_const)

end GlobalTheory.CovTop.PetRep
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
namespace GlobalTheory.WtMatchArith

theorem add_le_of_gap {n : ℕ} (f : Fin n → ℤ) (hf : ∀ k : ℕ, k + 1 < n → 1 ≤ GlobalTheory.CompHS.gap f k) :
    ∀ (d i : ℕ) (h : i + d < n), f ⟨i + d, h⟩ + d ≤ f ⟨i, by omega⟩ := by
  intro d
  induction d with
  | zero => intro i h; simp
  | succ d ih =>
    intro i h
    have h1 := hf (i + d) (by omega)
    unfold GlobalTheory.CompHS.gap at h1
    rw [dif_pos (by omega)] at h1
    have h2 := ih i (by omega)
    have e : (⟨i + d + 1, by omega⟩ : Fin n) = ⟨i + (d + 1), h⟩ := Fin.ext (by simp; omega)
    rw [e] at h1
    push_cast
    linarith

theorem le_of_gap {n : ℕ} (f : Fin n → ℤ) (hf : ∀ k : ℕ, k + 1 < n → 1 ≤ GlobalTheory.CompHS.gap f k)
    (i j : Fin n) (hij : i ≤ j) : f j ≤ f i := by
  have h := add_le_of_gap f hf ((j : ℕ) - i) i (by omega)
  have e1 : (⟨(i : ℕ) + ((j : ℕ) - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  have e2 : (⟨(i : ℕ), by omega⟩ : Fin n) = i := rfl
  rw [e1, e2] at h
  have : (0 : ℤ) ≤ (((j : ℕ) - i : ℕ) : ℤ) := Int.natCast_nonneg _
  linarith

theorem exists_shift {p q : ℕ} (f : Fin (p + q) → ℤ) (hf : ∀ k : ℕ, k + 1 < p + q → 1 ≤ GlobalTheory.CompHS.gap f k)
    (N M k : ℕ) (hN : 0 < N) (hk : 2 * M + N ≤ k + 1) :
    ∃ w : ℤ, (∀ i : Fin (p + q), (i : ℕ) < p → 0 ≤ ((k : ℤ) + 1) * f i + N * w - M) ∧
      (∀ i : Fin (p + q), p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * f i) - N * w - M) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  set B : ℤ := ∑ i, |f i| with hB
  have hBi : ∀ i, |f i| ≤ B := fun i => Finset.single_le_sum (f := fun i => |f i|) (fun j _ => abs_nonneg (f j))
    (Finset.mem_univ i)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => abs_nonneg (f j)
  by_cases hp : p = 0
  · refine ⟨-(((k : ℤ) + 1) * B + M), fun i hi => by omega, fun i _ => ?_⟩
    have h1 := (abs_le.1 (hBi i)).2
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * B := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : (0 : ℤ) ≤ ((k : ℤ) + 1) * B := mul_nonneg (by linarith) hB0
    have h4 : ((k : ℤ) + 1) * B + M ≤ N * (((k : ℤ) + 1) * B + M) := le_mul_of_one_le_left (by linarith) hN'
    linarith
  by_cases hq : q = 0
  · refine ⟨((k : ℤ) + 1) * B + M, fun i _ => ?_, fun i hi => by omega⟩
    have h1 := (abs_le.1 (hBi i)).1
    have h2 : ((k : ℤ) + 1) * (-B) ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : (0 : ℤ) ≤ ((k : ℤ) + 1) * B := mul_nonneg (by linarith) hB0
    have h4 : ((k : ℤ) + 1) * B + M ≤ N * (((k : ℤ) + 1) * B + M) := le_mul_of_one_le_left (by linarith) hN'
    linarith
  set X : ℤ := ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ - M with hX
  refine ⟨-(X / N), fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : f ⟨p - 1, by omega⟩ ≤ f i := le_of_gap f hf i _ (by simp [Fin.le_def]; omega)
    have h2 : ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 := Int.emod_nonneg X (by omega : (N : ℤ) ≠ 0)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    linarith
  · have h1 : f i ≤ f ⟨p, by omega⟩ := le_of_gap f hf _ i (by simp [Fin.le_def]; omega)
    have hg := hf (p - 1) (by omega)
    unfold GlobalTheory.CompHS.gap at hg
    rw [dif_pos (by omega)] at hg
    have e : (⟨p - 1 + 1, by omega⟩ : Fin (p + q)) = ⟨p, by omega⟩ := Fin.ext (by simp; omega)
    rw [e] at hg
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * (f ⟨p - 1, by omega⟩ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 := Int.emod_lt_of_pos X (by omega : (0 : ℤ) < N)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    have hk' : (2 * M + N : ℤ) ≤ k + 1 := by exact_mod_cast hk
    nlinarith

end GlobalTheory.WtMatchArith

namespace GlobalTheory.WtMatchArith

open GlobalTheory.AllWt in

theorem exists_dom_exponents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), GapGe 1 la → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  intro E _ _ _ H Dw la hla N M k hN hk
  have key : ∀ σ : Psi H, ∃ w : ℤ,
      (∀ i : Fin (Dw.p + Dw.q), (i : ℕ) < Dw.p → 0 ≤ ((k : ℤ) + 1) * la σ i + N * w - M) ∧
      (∀ i : Fin (Dw.p + Dw.q), Dw.p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * la σ i) - N * w - M) :=
    fun σ => exists_shift (la σ) (fun j hj => hla σ j hj) N M k hN hk
  choose w hwb hws using key
  have hantiσ : ∀ (σ : Psi H) (i j : Fin (Dw.p + Dw.q)), i ≤ j → la σ j ≤ la σ i :=
    fun σ => le_of_gap (la σ) (fun j hj => hla σ j hj)
  set val : (E →+* ℂ) × ℕ → ℤ := fun x => ((k : ℤ) + 1) * (wtOf Dw la 0).1 x +
    (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 x with hval
  have vbig : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.p),
      val (σ.1, i) = ((k : ℤ) + 1) * la σ ⟨i, by omega⟩ + (N * w σ - M) := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_big _ _ σ i hi, wtOf_big _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
  have vsmall : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.q),
      val (conjEmb σ.1, i) = -(((k : ℤ) + 1) * la σ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩) - N * w σ - M := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_small _ _ σ i hi, wtOf_small _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
    ring

  have split : ∀ τ : E →+* ℂ, (∃ σ : Psi H, σ.1 = τ ∧ Dw.mult τ = Dw.p) ∨
      (∃ σ : Psi H, conjEmb σ.1 = τ ∧ Dw.mult τ = Dw.q) := by
    intro τ
    by_cases h : τ (H.rt : E) = H.rt0
    · exact Or.inl ⟨⟨τ, h⟩, rfl, by simp [Datum.mult, h]⟩
    · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, conjEmb_conjEmb τ, by simp [Datum.mult, h]⟩
  have nonneg : ∀ (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → 0 ≤ val (τ, i) := by
    intro τ i hi
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hi; rw [vbig σ i hi]; have := hwb σ ⟨i, by omega⟩ hi; linarith
    · rw [hm] at hi; rw [vsmall σ i hi]; exact hws σ _ (by simp)
  have mono : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → val (τ, j) ≤ val (τ, i) := by
    intro τ i j hij hj
    have hk0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hj
      rw [vbig σ i (by omega), vbig σ j hj]
      have := hantiσ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega)
      nlinarith
    · rw [hm] at hj
      rw [vsmall σ i (by omega), vsmall σ j hj]
      have := hantiσ σ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
        (by simp [Fin.le_def]; omega)
      nlinarith
  refine ⟨w, fun x => if x.2 < Dw.mult x.1 then (val x).toNat else 0, ⟨fun τ => ?_, even_two_mul M⟩, ?_⟩
  · intro i j hij
    simp only
    split_ifs with hj hi hi
    · exact Int.toNat_le_toNat (mono τ i j hij hj)
    · omega
    · exact Nat.zero_le _
    · exact le_refl _
  · funext x
    rcases x with _ | ⟨τ, i⟩
    · simp [ex, exOf, exZ, wtOf]
    · have hi : (i : ℕ) < Dw.mult τ := i.2
      show (((if (i : ℕ) < Dw.mult τ then (val (τ, (i : ℕ))).toNat else 0 : ℕ)) : ℤ) = _
      rw [if_pos hi, Int.toNat_of_nonneg (nonneg τ i hi)]
      rw [Pi.add_apply, Pi.smul_apply]
      show _ = (k + 1) • (wtOf Dw la 0).1 (τ, (i : ℕ)) +
        (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 (τ, (i : ℕ))
      rw [nsmul_eq_mul]
      simp only [hval]
      push_cast
      ring

end GlobalTheory.WtMatchArith
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parallel_weight_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), GapGe 1 la → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  atlas_forward_decl GlobalTheory.WtMatchArith.exists_dom_exponents
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.WtMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_mem_secZ {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (n : ℕ) :
    f ^ n ∈ GlobalTheory.AllWt.secZ Xo c (n • ex) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ n ih => rw [pow_succ, succ_nsmul]; exact GlobalTheory.AllWt.mul_mem_secZ ih hf

theorem nsmul_exOf_zero_one (m : ℕ) : m • GlobalTheory.AllWt.exOf Dw 0 1 = GlobalTheory.AllWt.exOf Dw 0 m := by
  induction m with
  | zero => rw [zero_smul]; funext i; rw [Nat.cast_zero, GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf_zero]; cases i <;> rfl
  | succ m ih =>
    rw [succ_nsmul, ih, ← GlobalTheory.AllWt.exOf_add, add_zero]; push_cast; rfl

theorem val_pow_succ_nonneg {la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : IsVal la v) {f : Rul Xo c} (hf : 0 ≤ v f) (n : ℕ) : 0 ≤ v (f ^ (n + 1)) := by
  induction n with
  | zero => rw [pow_one]; exact hf
  | succ n ih => rw [pow_succ, hv.mul]; exact add_nonneg ih hf

set_option maxHeartbeats 800000 in

theorem exists_pow_mul_mem_cusp : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  intro hP D T j Y e o hY hE la hla f hf
  obtain ⟨u, u', t₁, hu, ht₁, huu, hu'⟩ := GlobalTheory.T.exists_invertible_section_valuation_nonneg hP D T j Y e o hY hE
  obtain ⟨N, hN, hU2⟩ := GlobalTheory.T.exists_parallel_weight_invertible_section hP D T j Y e o hY hE
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 4 * (Module.finrank ℚ D.host.E * D.R.r) + 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ := GlobalTheory.T.eventually_weight_section_products hP D T j Y e o hY hE la f hf (u ^ M) (u' ^ M) (t₁ ^ M) _ (pow_mem_secZ hu M)
    (pow_ne_zero _ ht₁) (by rw [← mul_pow, huu, smul_pow, one_pow])
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max K (2 * M + N) := ⟨_, rfl⟩
  obtain ⟨w, a, hDom, hex⟩ := GlobalTheory.T.exists_parallel_weight_decomposition _ _ _ la hla N M k hN (by omega)
  obtain ⟨φ, φ', t₂, hφ, ht₂, hφφ, hφ', hφb⟩ := hU2 w
  refine ⟨k, a, 2 * M, u ^ M * φ, u' ^ M * φ', t₁ ^ M * t₂, hDom, by omega, ?_, mul_ne_zero (pow_ne_zero _ ht₁) ht₂, ?_, ?_⟩
  · refine hK k (hk ▸ le_max_left _ _) φ φ' t₂ _ hφ ht₂ hφφ hφb a (2 * M) hDom ?_
    rw [← GlobalTheory.AllWt.secZ_nat, hex]
    have h1 : f ^ (k + 1) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ ((k + 1) • GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) :=
      pow_mem_secZ (GlobalTheory.AllWt.cuspW_le_secZ _ hf) (k + 1)
    have h2 := GlobalTheory.AllWt.mul_mem_secZ h1 (GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ hu M) hφ)
    convert h2 using 2
    rw [nsmul_exOf_zero_one, ← GlobalTheory.AllWt.exOf_add, zero_add, add_zero]
  · rw [mul_mul_mul_comm, ← mul_pow, huu, hφφ, smul_pow, one_pow, smul_mul_smul_comm, one_mul]
  · intro la' v hv
    have hV := isVal_valSet la' v hv
    rw [hV.mul]
    rw [hM]
    exact add_nonneg (val_pow_succ_nonneg hV (hu' la' v hv) _) (hφ' la' v hv)

end GlobalTheory.WtMatch
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_power_cusp_multiplier : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  atlas_forward_decl GlobalTheory.WtMatch.exists_pow_mul_mem_cusp
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SupSpanDeep

set_option maxHeartbeats 800000 in

theorem span_latW_eq_top : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ),
    Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la →
    FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) →
    Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) : Set (Y.V (wtOf _ la 0))) = ⊤ := by
  intro hP D T j Y e o hY hE la hla _
  refine eq_top_iff.2 fun f _ => ?_
  obtain ⟨k, a, n, g, h, t, hdom, hn, hmem, ht, hgh, hh⟩ := GlobalTheory.T.exists_power_cusp_multiplier hP D T j Y e o hY hE la hla f.1 f.2
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.T.exists_scalar_cusp_form_integral hP D T j Y e o hY hE a n hdom hn _ hmem
  have key : ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la',
      0 ≤ v ((s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1))) := by
    intro la' v hv
    have hV := isVal_valSet la' v hv
    have e1 : (s • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1) * g)) * h = (s * t) • ((f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)) := by
      rw [smul_mul_assoc, mul_assoc, hgh, mul_smul_comm, mul_one, smul_smul]
    rw [← e1, hV.mul]
    exact add_nonneg (hsv la' v hv) (hh la' v hv)
  obtain ⟨s', hs', h'⟩ := GlobalTheory.SupFull.exists_smul_nonneg_of_pow (valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂))
    (fun la => isVal_valSet la) {(f : Rul Y.d.Xo₂ Y.d.c₂) ^ (k + 1)}
    (by rintro g' rfl; exact ⟨s * t, mul_ne_zero hs ht, key⟩) (f : Rul Y.d.Xo₂ Y.d.c₂) k
    (Submodule.subset_span rfl)
  have hmem' : s' • f ∈ GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) :=
    GlobalTheory.AllWt.mem_supLat.2 fun la v hv => h' la v hv
  rw [← inv_smul_smul₀ hs' f]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem')

end GlobalTheory.SupSpanDeep
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_lattice_span_eq_top : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la → FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0) : Set (Y.V (wtOf _ la 0))) = ⊤ := by
  atlas_forward_decl GlobalTheory.SupSpanDeep.span_latW_eq_top
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_point_nonvanishing_section : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la →
    ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 →
    ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K),
      z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  first | exact @GlobalTheory.CovDetect.exists_good_cmPt_frame_ne_zero | exact GlobalTheory.CovDetect.exists_good_cmPt_frame_ne_zero | (intros; apply GlobalTheory.CovDetect.exists_good_cmPt_frame_ne_zero <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_section_exponent_shift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ)
    (k : (E →+* ℂ) → ℕ) (a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ), e none = 0 →
    (∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ)) →
    ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∃ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      G.IsHomogeneous (∑ b, ∑ i, a b i) ∧
      ∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K) (s : Kˣ),
        (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : K) y₀ y' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y := by
  first | exact @GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ | exact GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ | (intros; apply GlobalTheory.FieldPolyZ.exists_isHomogeneous_secZ <;> assumption)
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.LatFull.CMInt

theorem exists_frame_denom_intWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ)
    (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → ∀ la : GlobalTheory.AllWt.Weight Dw, GapGe 1 la →
    ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0),
      (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz y hy la _hla
  classical
  set e : Formalism.L2.Pj.Ix Dw → ℤ := GlobalTheory.AllWt.exOf Dw la 0 with he
  have he0 : e none = 0 := by
    simp [he, GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf, exZ]
  let k : (E →+* ℂ) → ℕ := fun b => ∑ i : Fin (Dw.mult b), (-(e (some ⟨b, i⟩))).toNat
  let a : ∀ b : E →+* ℂ, Fin (Dw.mult b) → ℕ := fun b i => (e (some ⟨b, i⟩) + (k b : ℤ)).toNat
  have hak : ∀ (b : E →+* ℂ) (i : Fin (Dw.mult b)), e (some ⟨b, i⟩) + (k b : ℤ) = (a b i : ℤ) := by
    intro b i
    have h1 : (-(e (some ⟨b, i⟩))).toNat ≤ k b :=
      Finset.single_le_sum (f := fun i : Fin (Dw.mult b) => (-(e (some ⟨b, i⟩))).toNat)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [a]
    omega
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_commonDenom_framePolynomials_cmPoint E H Dw l Xo c z f La hz e k he0
  obtain ⟨g, s, hg, hgs⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c z.K z.y y).1 (hy.trans hz.2.2.2.1.symm)
  let Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) z.K := fun b => (g b).transpose
  have hYd : ∀ b, (Y b).det ≠ 0 := fun b => by
    simp only [Y, Matrix.det_transpose]; exact (hg b).ne_zero
  have hgY : (fun b => (Y b).transpose) = g := funext fun b => Matrix.transpose_transpose _
  have htK : (t : z.K) ≠ 0 := fun h => ht0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨N₀, hN₀, hint⟩ := GlobalTheory.LatFull.CMInt.exists_denom_eval
    (fun _ : Formalism.L2.LamCM.FrVar Dw.mult →₀ ℕ => FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 z.K)) ((t : z.K)⁻¹))
    (fun v : Formalism.L2.LamCM.FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ b, ∑ i, a b i)
  refine ⟨N₀ * ∏ b, (Y b).det ^ k b, mul_ne_zero hN₀ (Finset.prod_ne_zero_iff.2 fun b _ => pow_ne_zero _ (hYd b)),
    fun F hF hv => ?_⟩
  obtain ⟨G, hGh, hG⟩ := GlobalTheory.T.weighted_section_exponent_shift E H Dw l Xo c z.K z.y e k a he0 hak F hF
  have h1 := hG y Y s hYd (by rw [hgY]; exact hgs)
  have h2 : N₀ * (∏ b, (Y b).det ^ k b) * evR Xo c F y = N₀ * Formalism.L2.LamCM.evalFr G Y := by
    rw [mul_assoc, h1]
  rw [h2]
  refine hint G hGh fun μ => ?_
  rw [FractionalIdeal.mem_spanSingleton]
  refine ⟨⟨_, ht F hF hv G (fun y' Y' s' hY' h' => hG y' Y' s' hY' h') μ⟩, ?_⟩
  change (t : z.K) * MvPolynomial.coeff μ G * (t : z.K)⁻¹ = _
  field_simp

end GlobalTheory.LatFull.CMInt
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_valuation_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ)
    (La : ℝ), z.Good f La → ∀ y : FrPt Xo c z.K, y.x = z.x → ∀ la : GlobalTheory.AllWt.Weight Dw, GapGe 1 la →
    ∃ N : z.K, N ≠ 0 ∧ ∀ F ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf Dw la 0),
      (∀ v, ∀ w ∈ valSet Xo c (algCls Xo c) v, 0 ≤ w F) → IsIntegral ℤ (N * evR Xo c F y) := by
  atlas_forward_decl GlobalTheory.LatFull.CMInt.exists_frame_denom_intWt
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.SupFG

set_option maxHeartbeats 1000000 in

theorem latW_fg : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la →
    FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0)).FG := by
  intro hP D T j Y e o hG hE la hgap hfd
  letI := T.Q.H.starRing
  refine GlobalTheory.fg_of_integral_functionals Y.d.c₂.F (Y.V (wtOf _ la 0)) _ fun x hx => ?_
  obtain ⟨z, La, y, hz, hyx, hne⟩ := GlobalTheory.T.exists_cm_point_nonvanishing_section hP D T j Y e o hG hE la hgap (fun _ => rfl) x.1 x.2
    (fun h => hx (Subtype.ext h))
  obtain ⟨N, hN, hint⟩ := GlobalTheory.T.exists_denominator_valuation_bound _ _ _ _ _ _ z _ La hz y hyx la hgap
  refine ⟨z.K, inferInstance, inferInstance, inferInstance,
    { toFun := fun F => N * evR Y.d.Xo₂ Y.d.c₂ F.1 y
      map_add' := fun F G => ?_
      map_smul' := fun s F => ?_ }, mul_ne_zero hN hne, fun F hF => hint F.1 (GlobalTheory.AllWt.cuspW_le_secZ _ F.2) hF⟩
  · rw [← mul_add]
    exact congrArg _ (evalAt_add _ _ F.1 G.1 y)
  · have e1 : evR Y.d.Xo₂ Y.d.c₂ (s • F).1 y = algebraMap Y.d.c₂.F z.K s * evR Y.d.Xo₂ Y.d.c₂ F.1 y :=
      evalAt_smul _ _ s F.1 y
    rw [e1, RingHom.id_apply, Algebra.smul_def, mul_left_comm]

end GlobalTheory.CovTop.SupFG
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_lattice_finitely_generated : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la → FiniteDimensional Y.d.c₂.F (Y.V (wtOf _ la 0)) → (GlobalTheory.AllWt.latW Y.U (wtOf _ la 0)).FG := by
  atlas_forward_decl GlobalTheory.CovTop.SupFG.latW_fg
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.HSApp

section Gen

open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {D : D7}

set_option maxHeartbeats 2000000 in

theorem exists_semilinear_L2_independent (hS : Out.SecBaseChangeSt) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
    (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (V : HSp D)
    (dict : Formalism.L2.Theta.GA D V → Σ k, Frame ((U σ).X k).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)
    (hmu1 : ∀ g, ‖mu g‖ = 1) (hm : Formalism.L2.Pj.AdelMeas U σ V dict mu) (hae : Formalism.L2.Pj.AeDom U σ V dict mu)
    (hd : ∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom)
    (hunit : ∀ g τ i, ‖dmin ((U σ).X (dict g).1).Gm (dict g).2 τ i‖ = 1) (G : WTZ E) (x : ℝ) :
    ∃ Φ : GlobalTheory.AllWt.cuspW Xo c U G →+ Lp ℂ 2 (muQ1 V), (∀ (a : c.F) f, Φ (a • f) = σ a • Φ f) ∧
      (∀ f : GlobalTheory.AllWt.cuspW Xo c U G, GlobalTheory.AllWt.petAt (U σ) x V dict (muQ1 V) G (f : Rul Xo c) = ‖Φ f‖) ∧
      ∀ (n : ℕ) (e : Fin n → GlobalTheory.AllWt.cuspW Xo c U G), LinearIndependent c.F e →
        LinearIndependent ℂ (fun i => Φ (e i)) := by
  have hhol : ∀ f : GlobalTheory.AllWt.cuspW Xo c U G,
      rdU (U σ) (f : Rul Xo c) ∈ holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f =>
    (GlobalTheory.AllWt.mem_cuspW.1 f.2).2 σ hσ
  have heq : ∀ P : FDSec (U σ).X,
      eLpNorm (onQ V (adel V dict mu P)) 2 (muQ1 V) =
        GlobalTheory.AllWt.petE V dict (muQ1 V) (GlobalTheory.AllWt.modelWt (U σ) G) P := by
    intro P
    unfold GlobalTheory.AllWt.petE
    refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
    show ‖mu q.out * P (dict q.out).1 (dict q.out).2‖ = _
    rw [norm_mul, hmu1, one_mul, Real.norm_of_nonneg (GlobalTheory.AllWt.ptN_nonneg _ _ _), GlobalTheory.AllWt.ptN,
      pnorm_eq_of_unit _ _ _ _ (hunit q.out)]
  have hmem : ∀ P : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G),
      MemLp (onQ V (adel V dict mu (P : FDSec (U σ).X))) 2 (muQ1 V) := fun P =>
    ⟨aesm_of_holSub hm _ P.2, by
      rw [heq]
      exact lt_top_iff_ne_top.2 (GlobalTheory.AllWt.petE_ne_top V dict (muQ1 V) prob_le_one hd P.2)⟩
  let L : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) →ₗ[ℂ] Lp ℂ 2 (muQ1 V) :=
    { toFun := fun P => (hmem P).toLp _
      map_add' := fun P Q => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_add, map_add, map_add]))
      map_smul' := fun a P => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by rw [Submodule.coe_smul, map_smul, map_smul])) }
  have hL : ∀ P, L P = (hmem P).toLp _ := fun _ => rfl
  let R : GlobalTheory.AllWt.cuspW Xo c U G → holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G) := fun f => ⟨_, hhol f⟩
  have hRadd : ∀ f g, R (f + g) = R f + R g := fun f g => Subtype.ext (by
    show rdU (U σ) ((f + g : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = rdU (U σ) (f : Rul Xo c) + rdU (U σ) (g : Rul Xo c)
    rw [Submodule.coe_add, map_add])
  have hRsm : ∀ (a : c.F) f, R (a • f) = σ a • R f := fun a f => Subtype.ext (by
    show rdU (U σ) ((a • f : GlobalTheory.AllWt.cuspW Xo c U G) : Rul Xo c) = σ a • rdU (U σ) (f : Rul Xo c)
    rw [Submodule.coe_smul, map_smulₛₗ])
  let cf : ℝ := GlobalTheory.AllWt.lieFacZ Dw x G
  have hcf : 0 < cf := GlobalTheory.AllWt.lieFacZ_pos x G
  refine ⟨AddMonoidHom.mk' (fun f => (cf : ℂ) • L (R f)) (fun f g => by rw [hRadd, map_add, smul_add]),
    fun a f => ?_, fun f => ?_, fun n e he => ?_⟩
  · show (cf : ℂ) • L (R (a • f)) = σ a • ((cf : ℂ) • L (R f))
    rw [hRsm, map_smul, smul_comm]
  · show _ = ‖(cf : ℂ) • L (R f)‖
    rw [norm_smul, hL, Lp.norm_toLp, heq, Complex.norm_real, Real.norm_of_nonneg hcf.le]
    rfl
  · have hb : LinearIndependent c.F (fun i => (e i : Rul Xo c)) :=
      he.map' (GlobalTheory.AllWt.cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := GlobalTheory.reading_linearIndependent_secZ hS (U σ) hU _ n _
      (fun i => GlobalTheory.AllWt.cuspW_le_secZ G (e i).2) hb
    rw [Fintype.linearIndependent_iff] at hc ⊢
    intro w hw
    refine hc w ?_
    have h1 : (cf : ℂ) • L (∑ i, w i • R (e i)) = 0 := by
      have hw' : ∑ i, w i • ((cf : ℂ) • L (R (e i))) = 0 := hw
      rw [map_sum, Finset.smul_sum, ← hw']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [L.map_smul]
      exact smul_comm _ _ _
    have h2 : L (∑ i, w i • R (e i)) = 0 :=
      (smul_eq_zero.1 h1).resolve_left (Complex.ofReal_ne_zero.2 hcf.ne')
    have h3 : onQ V (adel V dict mu ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) :
        FDSec (U σ).X)) =ᵐ[muQ1 V] 0 := by
      refine (MemLp.coeFn_toLp (hmem _)).symm.trans ?_
      rw [← hL, h2]
      exact Lp.coeFn_zero _ _ _
    have h4 := hae _ _ (∑ i, w i • R (e i)).2 h3
    have h5 : ((∑ i, w i • R (e i) : holSub (U σ).X (GlobalTheory.AllWt.modelWt (U σ) G)) : FDSec (U σ).X) =
        ∑ i, w i • rdU (U σ) (e i : Rul Xo c) := by
      rw [Submodule.coe_sum]
      rfl
    rw [h5] at h4
    funext k z
    by_cases hz : z ∈ ((U σ).X k).dom
    · exact h4 k z hz
    · simp [Finset.sum_apply, rdU, hz]

end Gen

set_option maxHeartbeats 2000000 in

theorem hasGram_nrm_of_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hY : Y.Good e o)
    (G : WTZ D.host.E) : GlobalTheory.AllWt.HasGram (Y.nrm G) := by
  haveI := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY G
  refine GlobalTheory.HSApp.hasGram_of_inner Y.d.c₂.F (Y.V G) (Y.nrm G) fun v => ?_
  have hσ' : GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) := Formalism.L2.Pj.goodEmb_goodOf _ _
  have hd : ∀ g, (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).2 ∈
      ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding)).X (Y.dict (Formalism.L2.Pj.goodOf Y.d.c₂ v.embedding) g).1).dom :=
    fun g => ((hY.dictU _ hσ').choose_spec.choose_spec.2).2.2.2.1 g
  have hex := exists_semilinear_L2_independent GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ' (hY.unf _ hσ')
    (D.sp.W j) (Y.dict _) (fun _ => (1 : ℂ)) (fun _ => norm_one)
    (GlobalTheory.CovTop.PetRep.adelMeas_one_of_good Y hY _ hσ') (GlobalTheory.PetDef.aeDom_good Y hY _ hσ') hd (hY.unit _ hσ') G (xiR D)
  refine ⟨_, inferInstance, inferInstance, Classical.choose hex, ?_, fun x => (Classical.choose_spec hex).2.1 x,
    (Classical.choose_spec hex).2.2⟩
  by_cases h : GoodEmb Y.d.c₂ v.embedding
  · left
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (if_pos h))
  · right
    intro a x
    refine ((Classical.choose_spec hex).1 a x).trans ?_
    exact congrArg (· • Classical.choose hex x) (congrArg (fun τ : Y.d.c₂.F →+* ℂ => τ a) (if_neg h))

set_option maxHeartbeats 1000000 in

theorem goodAt_of_gapGe : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la → Y.GoodAt (wtOf _ la 0) := by
  intro hP D T j Y e o hY hf la hla
  have hfd := GlobalTheory.Deep.finiteDimensional_V_of_good D T j Y e o hY (wtOf _ la 0)
  exact ⟨hasGram_nrm_of_good D T j Y e o hY _, GlobalTheory.T.weight_lattice_finitely_generated hP D T j Y e o hY hf la hla hfd,
    GlobalTheory.T.weight_lattice_span_eq_top hP D T j Y e o hY hf la hla hfd⟩


end GlobalTheory.HSApp
end
end
