import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionDerivativeAtOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KActionSkewAdjointL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContaining
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PhiCentreEigenfunctionDiscreteSeries
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjGelfValOfIsHerm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LowerIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone

section
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.LieAct

variable {n : ℕ}

theorem SmF_ext {a b : SmF n} (h : ∀ g ∈ GLs n, a.1 g = b.1 g) : a = b := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact h g hg
  · rw [a.2.2 g hg, b.2.2 g hg]

theorem Rd_DR (X Y : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (DR Y h).1 g = Rd X (Rd Y h.1) g := by
  have hev : (DR Y h).1 =ᶠ[nhds g] Rd Y h.1 := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact DR_apply Y h hy
  simp only [Rd]
  rw [hev.fderiv_eq]

theorem DR_add (X Y : Mat n) : DR (X + Y) = DR X + DR Y := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, DR_apply _ _ hg, Rd, Matrix.mul_add, map_add]

theorem DR_smul (r : ℝ) (X : Mat n) : DR ((r : ℂ) • X) = (r : ℂ) • DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  have e : g * ((r : ℂ) • X) = r • (g * X) := by
    ext a b
    simp [Matrix.mul_apply, Finset.mul_sum, Complex.real_smul, mul_left_comm]
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, DR_apply _ _ hg, Rd, e, map_smul,
    Complex.real_smul, smul_eq_mul]

theorem DR_bracket (X Y : Mat n) : DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X := by
  refine LinearMap.ext fun h => SmF_ext fun g hg => ?_
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, DR_apply _ _ hg, Rd_DR _ _ _ hg]
  exact (GlobalTheory.CompanionTheory.RCalc.Rd_bracket X Y h.2.1 hg).symm

theorem DR_lie (n : ℕ) : (∀ X Y : Mat n, DR (X + Y) = DR X + DR Y) ∧
    (∀ (r : ℝ) (X : Mat n), DR ((r : ℂ) • X) = (r : ℂ) • DR X) ∧
    (∀ X Y : Mat n, DR (X * Y - Y * X) = DR X * DR Y - DR Y * DR X) :=
  ⟨DR_add, DR_smul, DR_bracket⟩

end GlobalTheory.CompanionTheory.ModelS.LieAct
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_real_lie_hom : ∀ (n : ℕ), (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X + Y) = GlobalTheory.CompanionTheory.ModelS.DR X + GlobalTheory.CompanionTheory.ModelS.DR Y) ∧ (∀ (r : ℝ) (X : Mat n), GlobalTheory.CompanionTheory.ModelS.DR ((r : ℂ) • X) = (r : ℂ) • GlobalTheory.CompanionTheory.ModelS.DR X) ∧ (∀ X Y : Mat n, GlobalTheory.CompanionTheory.ModelS.DR (X * Y - Y * X) = GlobalTheory.CompanionTheory.ModelS.DR X * GlobalTheory.CompanionTheory.ModelS.DR Y - GlobalTheory.CompanionTheory.ModelS.DR Y * GlobalTheory.CompanionTheory.ModelS.DR X) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.LieAct.DR_lie
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_mem_Eqv (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) :
    h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  intro hh p hp g hg
  have hpg : p * g ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.mul_mem_GLs hp.1 hg
  rw [DR_apply X h hpg, DR_apply X h hg]
  have dg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hg
  have dpg := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 hpg
  have ev : (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) =ᶠ[nhds g] fun y => φ p • h.1 y := by
    filter_upwards [GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds hg] with y hy
    exact hh p hp y hy
  have e1' : fderiv ℝ (fun y => h.1 (GlobalTheory.CompanionTheory.RCalc.mulL p y)) g (g * X)
      = fderiv ℝ h.1 (p * g) (p * (g * X)) :=
    GlobalTheory.CompanionTheory.RCalc.fderiv_comp_clm (GlobalTheory.CompanionTheory.RCalc.mulL p) dpg (g * X)
  rw [ev.fderiv_eq] at e1'
  have e2' := GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply dg (φ p) (g * X)
  simp only [Rd]
  rw [Matrix.mul_assoc, ← e1']
  exact e2'

end GlobalTheory.CompanionTheory.ModelS
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_preserves_equivariant : ∀ (n : ℕ) (lev : Fin n → ℕ) (φ : Mat n → ℂ) (X : Mat n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n), h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ → GlobalTheory.CompanionTheory.ModelS.DR X h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.DR_mem_Eqv
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS

theorem DR_one_of_eqv (n : ℕ) (lev : Fin n → ℕ) (f h : SmF n) (_hf : f ∈ Eqv lev f.1) (_hf1 : f.1 1 = 1)
    (hh : h ∈ Eqv lev f.1) (X : Mat n) (hX : ∀ a b, lev a < lev b → X a b = 0) :
    (DR X h).1 1 = (DR X f).1 1 * h.1 1 := by
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have dh := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth h.2.1 h1).hasFDerivAt
  have df := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth f.2.1 h1).hasFDerivAt
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    simp only [one_smul] at this
    exact this
  have hc0 : (1 : Mat n) = (fun t : ℝ => (1 : Mat n) + t • X) 0 := by simp
  have Dh := dh.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0
  have Df := (df.comp_hasDerivAt_of_eq (0 : ℝ) hc hc0).mul_const (h.1 1)
  have hev : ∀ᶠ t : ℝ in nhds 0, (1 : Mat n) + t • X ∈ GLs n :=
    hc.continuousAt.eventually_mem (by
      have hm : (1 : Mat n) + (0 : ℝ) • X = 1 := by simp
      rw [hm]
      exact GlobalTheory.CompanionTheory.RCalc.isOpen_GLs.mem_nhds h1)
  have heq : (h.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) =ᶠ[nhds 0]
      fun t => (f.1 ∘ fun t : ℝ => (1 : Mat n) + t • X) t * h.1 1 := by
    filter_upwards [hev] with t ht
    have hp : (1 : Mat n) + t • X ∈ Pb lev := by
      refine ⟨ht, fun a b hab => ?_⟩
      have hne : a ≠ b := fun e => (e ▸ hab : lev a < lev a).false
      simp [hX a b hab, Matrix.one_apply_ne hne]
    have := hh _ hp 1 h1
    simpa using this
  have key := (Dh.congr_of_eventuallyEq heq.symm).unique Df
  rw [DR_apply _ _ h1, DR_apply _ _ h1]
  show fderiv ℝ h.1 1 (1 * X) = fderiv ℝ f.1 1 (1 * X) * h.1 1
  rw [one_mul]
  exact key

end GlobalTheory.CompanionTheory.ModelS
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_lower_block_at_one : ∀ (n : ℕ) (lev : Fin n → ℕ) (f h : GlobalTheory.CompanionTheory.ModelS.SmF n), f ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → f.1 1 = 1 → h ∈ GlobalTheory.CompanionTheory.ModelS.Eqv lev f.1 → ∀ X : Mat n, (∀ a b, lev a < lev b → X a b = 0) → (GlobalTheory.CompanionTheory.ModelS.DR X h).1 1 = (GlobalTheory.CompanionTheory.ModelS.DR X f).1 1 * h.1 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.DR_one_of_eqv
end

section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_at_one : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), GlobalTheory.CompanionTheory.ModelS.fRaw lam lev 1 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.fRaw_one | exact GlobalTheory.CompanionTheory.ModelS.fRaw_one | (intros; apply GlobalTheory.CompanionTheory.ModelS.fRaw_one <;> assumption)
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.FMul

open GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem ini_injective (j : Fin n) : Function.Injective (ini j) :=
  Fin.castLE_injective _

theorem rows_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    (p * g).submatrix (ini j) id = p.submatrix (ini j) (ini j) * g.submatrix (ini j) id := by
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, id]
  symm
  refine Fintype.sum_of_injective (ini j) (ini_injective j) _ _ ?_ (fun i => rfl)
  intro k hk
  have hjk : j < k := by
    by_contra h
    have h' : (k : ℕ) ≤ j := by
      have := not_lt.1 h
      exact Fin.le_def.1 this
    exact hk ⟨⟨k, by omega⟩, by ext; rfl⟩
  have haj : ini j a ≤ j := by
    have := a.isLt
    rw [Fin.le_def]
    show (a : ℕ) ≤ j
    omega
  rw [hz _ _ haj hjk, zero_mul]

theorem lm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    lm j (p * g) = lm j p * lm j g := by
  have h : (p * g).submatrix (ini j) (ini j) =
      p.submatrix (ini j) (ini j) * g.submatrix (ini j) (ini j) := by
    ext a c
    exact congrFun (congrFun (rows_mul j p g hz) a) (ini j c)
  rw [lm, h, Matrix.det_mul, lm, lm]

theorem gm_mul (j : Fin n) (p g : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j (p * g) = lm j p * star (lm j p) * gm j g := by
  rw [gm, rows_mul j p g hz, Matrix.conjTranspose_mul]
  have h : p.submatrix (ini j) (ini j) * g.submatrix (ini j) id *
      ((g.submatrix (ini j) id)ᴴ * (p.submatrix (ini j) (ini j))ᴴ) =
      p.submatrix (ini j) (ini j) * (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ) *
        (p.submatrix (ini j) (ini j))ᴴ := by
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, lm, gm]
  ring

theorem gm_one (j : Fin n) : gm j (1 : Mat n) = 1 := by
  have h : ((1 : Mat n).submatrix (ini j) id) * ((1 : Mat n).submatrix (ini j) id)ᴴ = 1 := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one,
      ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.mul_one,
      Matrix.submatrix_one _ (ini_injective j)]
  rw [gm, h, Matrix.det_one]

theorem gm_left (j : Fin n) (p : Mat n) (hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0) :
    gm j p = lm j p * star (lm j p) := by
  have := gm_mul j p 1 hz
  rwa [Matrix.mul_one, gm_one, mul_one] at this

theorem dif_eq_zero (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hl : IsLev lam lev) (j : Fin n) (h : (j : ℕ) + 1 < n)
    (he : lev j = lev ⟨j + 1, h⟩) : dif (muZ lam lev) j = 0 ∧ dif (yZ lam lev) j = 0 := by
  obtain ⟨-, hl⟩ := hl
  have hlam := hl _ _ he
  have hmu : muZ lam lev j = muZ lam lev ⟨j + 1, h⟩ := by
    simp only [muZ, hlam, he]
  have hy : yZ lam lev j = yZ lam lev ⟨j + 1, h⟩ := by
    simp only [yZ, hlam, hmu]
  constructor
  · simp only [dif, dif_pos h, hmu, sub_self]
  · simp only [dif, dif_pos h, hy, sub_self]

theorem fRaw_mul : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
    ∀ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∀ g ∈ GLs n,
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev (p * g) = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev p * GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g := by
  intro n lam _ lev hl p hp g hg
  obtain ⟨hp1, hp2⟩ := hp
  have hpg : p * g ∈ GLs n := by
    show (p * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hp1 hg
  simp only [fRaw, Set.indicator_of_mem hpg, Set.indicator_of_mem hp1, Set.indicator_of_mem hg]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hgood : ∀ a b : Fin n, a ≤ j → j < b → lev a < lev b
  · have hz : ∀ a b : Fin n, a ≤ j → j < b → p a b = 0 := fun a b h1 h2 => hp2 a b (hgood a b h1 h2)
    rw [lm_mul j p g hz, gm_mul j p g hz, ← gm_left j p hz, mul_zpow, mul_zpow, mul_mul_mul_comm]
  · push_neg at hgood
    obtain ⟨a, b, haj, hjb, hba⟩ := hgood
    have hmono := hl.1
    have hb : (j : ℕ) < b := Fin.lt_def.1 hjb
    have h : (j : ℕ) + 1 < n := by have := b.isLt; omega
    have h1 : lev j ≤ lev ⟨j + 1, h⟩ := hmono (Fin.le_def.2 (by simp))
    have h2 : lev ⟨j + 1, h⟩ ≤ lev b := hmono (Fin.le_def.2 (by simpa using hb))
    have h3 : lev a ≤ lev j := hmono haj
    have he : lev j = lev ⟨j + 1, h⟩ := by omega
    obtain ⟨d1, d2⟩ := dif_eq_zero lam lev hl j h he
    simp only [d1, d2, zpow_zero, mul_one]

end GlobalTheory.CompanionTheory.ModelS.FMul
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inducedFunction_parabolic_equivariant : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∀ g ∈ GLs n, GlobalTheory.CompanionTheory.ModelS.fRaw lam lev (p * g) = GlobalTheory.CompanionTheory.ModelS.fRaw lam lev p * GlobalTheory.CompanionTheory.ModelS.fRaw lam lev g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.FMul.fRaw_mul
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_Pb_mul_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n,
    ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  intro n lev hlev g hg
  have hdet : g.det ≠ 0 := hg
  have hu : IsUnit gᴴ := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (by simpa using hdet)
  obtain ⟨k, hk, b, hb, ht⟩ := GlobalTheory.CompanionTheory.QR.exists_unitary_mul_blockTriangular gᴴ hu
  have hg' : g = bᴴ * kᴴ := by
    rw [← Matrix.conjTranspose_mul, ← hb, Matrix.conjTranspose_conjTranspose]
  have hkH : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have := (Matrix.mem_unitaryGroup_iff').1 hk
    simpa [Matrix.star_eq_conjTranspose] using this
  refine ⟨bᴴ, ⟨?_, ?_⟩, ⟨kᴴ, hkH⟩, hg'⟩
  · intro h0
    apply hdet
    rw [hg', Matrix.det_mul]
    have h0' : (bᴴ).det = 0 := h0
    rw [h0', zero_mul]
  · intro a c hac
    have hlt : a < c := by
      by_contra hn
      exact absurd (hlev (not_lt.1 hn)) (not_le.2 hac)
    have : b c a = 0 := ht hlt
    simp [Matrix.conjTranspose_apply, this]

end GlobalTheory.CompanionTheory.ModelS
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_parabolic_unitary : ∀ (n : ℕ) (lev : Fin n → ℕ), Monotone lev → ∀ g ∈ GLs n, ∃ p ∈ GlobalTheory.CompanionTheory.ModelS.Pb lev, ∃ k : Matrix.unitaryGroup (Fin n) ℂ, g = p * k.1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.exists_Pb_mul_unitary
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem exists_rightInvariant_measure_unitaryGroup
    (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
    [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] :
    ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ),
      IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
    GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  let μ : Measure (Matrix.unitaryGroup (Fin n) ℂ) := Measure.haarMeasure ⊤
  refine ⟨μ.inv, inferInstance, inferInstance, inferInstance⟩

end GlobalTheory.CompanionTheory.ModelS
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_unitary_group : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)], ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ), IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup
end

section
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.SkewInt

open scoped Matrix.Norms.Operator in

theorem exp_entry_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n) i j)
      ((NormedSpace.exp (t • X) * X : Mat n) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt t h

theorem exp_hasDerivAt {n : ℕ} (X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • X) : Mat n)) (NormedSpace.exp (t • X) * X) t := by
  have : HasDerivAt (fun s : ℝ => (fun i j => (NormedSpace.exp (s • X) : Mat n) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp (t • X) * X : Mat n) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry_hasDerivAt X t i j
  exact this

theorem curve_hasDerivAt {n : ℕ} (k X : Mat n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => k * (NormedSpace.exp (s • X) : Mat n)) (k * NormedSpace.exp (t • X) * X) t := by
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ k)
  have h := L.hasFDerivAt.comp_hasDerivAt t (exp_hasDerivAt X t)
  have e : L (NormedSpace.exp (t • X) * X) = k * NormedSpace.exp (t • X) * X := by
    rw [Matrix.mul_assoc]
    rfl
  exact h.congr_deriv e

theorem exp_mem_unitary {n : ℕ} {X : Mat n} (hX : Xᴴ = -X) (t : ℝ) :
    (NormedSpace.exp (t • X) : Mat n) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul,
    star_trivial, hX, smul_neg, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))

theorem integral_Rd_skew : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  intro n _ _ κ _ _ u hu X hX
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let kt : ℝ → Matrix.unitaryGroup (Fin n) ℂ := fun t => ⟨NormedSpace.exp (t • X), exp_mem_unitary hX t⟩
  have hval : ∀ (y : Matrix.unitaryGroup (Fin n) ℂ) (t : ℝ),
      y.1 * (NormedSpace.exp (t • X) : Mat n) = (y * kt t).1 := fun _ _ => rfl
  have hcv : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => k.1 := continuous_subtype_val
  have hRd := GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hu
  have cU : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => u k.1 :=
    hu.continuousOn.comp_continuous hcv unit_mem
  have cR : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => Rd X u k.1 :=
    hRd.continuousOn.comp_continuous hcv unit_mem
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn cR.continuousOn
  have key := GlobalTheory.CompanionTheory.RCalc.ByParts.integral_deriv_eq_zero (μ := κ) (V := ℂ)
    (F := fun t y => u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (F' := fun t y => Rd X u (y.1 * (NormedSpace.exp (t • X) : Mat n)))
    (K := Set.univ) isCompact_univ (ε := 1) one_pos C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa using key
  · intro t _
    simp only [hval]
    exact cU.comp (continuous_mul_right (kt t))
  · simp only [hval]
    exact cR.comp (continuous_mul_right (kt 0))
  · intro y t _
    have hg : y.1 * (NormedSpace.exp (t • X) : Mat n) ∈ GLs n := by
      rw [hval]
      exact unit_mem _
    have h := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth hu hg).hasFDerivAt.comp_hasDerivAt t
      (curve_hasDerivAt y.1 X t)
    exact h
  · intro y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y hy
    exact absurd (Set.mem_univ y) hy
  · intro t _ y _
    simp only [hval]
    exact hC _ (Set.mem_univ _)
  · intro t _
    simp only [hval]
    have h0 : kt 0 = 1 := by
      apply Subtype.ext
      simp [kt]
    rw [h0]
    simp only [mul_one]
    exact integral_mul_right_eq_self (fun y : Matrix.unitaryGroup (Fin n) ℂ => u y.1) (kt t)

end GlobalTheory.CompanionTheory.ModelS.SkewInt
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_derivative_eq_zero : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsMulRightInvariant] (u : Mat n → ℂ), ContDiffOn ℝ ∞ u (GLs n) → ∀ X : Mat n, Xᴴ = -X → ∫ k : Matrix.unitaryGroup (Fin n) ℂ, Rd X u k.1 ∂κ = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.SkewInt.integral_Rd_skew
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ModelS.L2InnerProduct

theorem isCompact_unitary_set (n : ℕ) :
    IsCompact ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) := by
  have hK : IsCompact (Set.pi Set.univ
      (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :
        Set (Matrix (Fin n) (Fin n) ℂ)) :=
    isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hC : IsClosed ((Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))) :=
    isClosed_unitary (R := Matrix (Fin n) (Fin n) ℂ)
  refine hK.of_isClosed_subset hC ?_
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i j
  exact entry_norm_bound_of_unitary hx i j

theorem compactSpace_unitary (n : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitary_set n)

theorem continuous_restrict {n : ℕ} (x : SmF n) :
    Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => x.1 k.1 :=
  x.2.1.continuousOn.comp_continuous continuous_subtype_val unit_mem

section

variable {n : ℕ} [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)]
  (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ]

theorem integrable_integrand (x y : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => conj (x.1 k.1) * y.1 k.1) κ := by
  haveI := compactSpace_unitary n
  exact ((Complex.continuous_conj.comp (continuous_restrict x)).mul
    (continuous_restrict y)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_normSq (x : SmF n) :
    Integrable (fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2) κ := by
  haveI := compactSpace_unitary n
  exact ((continuous_restrict x).norm.pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem ipK_self (x : SmF n) :
    ipK κ x x = ((∫ k, ‖x.1 k.1‖ ^ 2 ∂κ : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  unfold ipK
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [Complex.conj_mul']

theorem ipK_conj (x y : SmF n) : conj (ipK κ y x) = ipK κ x y := by
  unfold ipK
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_comm]

theorem ipK_add_left (x y z : SmF n) : ipK κ (x + y) z = ipK κ x z + ipK κ y z := by
  unfold ipK
  rw [← integral_add (integrable_integrand κ x z) (integrable_integrand κ y z)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [add_mul]

theorem ipK_smul_left (c : ℂ) (x y : SmF n) : ipK κ (c • x) y = conj c * ipK κ x y := by
  unfold ipK
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp [mul_assoc]

theorem eq_zero_of_ipK_self [κ.IsOpenPosMeasure] (x : SmF n) (h : ipK κ x x = 0)
    (k : Matrix.unitaryGroup (Fin n) ℂ) : x.1 k.1 = 0 := by
  rw [ipK_self, Complex.ofReal_eq_zero] at h
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => by positivity) (integrable_normSq κ x)).1 h
  have hc : Continuous fun k : Matrix.unitaryGroup (Fin n) ℂ => ‖x.1 k.1‖ ^ 2 :=
    (continuous_restrict x).norm.pow 2
  have := (hc.ae_eq_iff_eq κ continuous_zero).1 hae
  simpa using congrFun this k

end

theorem ipK_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  intro n _ _ κ _ _
  refine ⟨ipK_conj κ, fun x => ?_, ipK_add_left κ, ipK_smul_left κ, eq_zero_of_ipK_self κ⟩
  rw [ipK_self, Complex.ofReal_re]
  exact integral_nonneg fun k => by positivity

end GlobalTheory.CompanionTheory.ModelS.L2InnerProduct
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l2_inner_product_hermitian_form : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)] (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) [IsFiniteMeasure κ] [κ.IsOpenPosMeasure], (∀ x y : GlobalTheory.CompanionTheory.ModelS.SmF n, conj (GlobalTheory.CompanionTheory.ModelS.ipK κ y x) = GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ (∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, 0 ≤ (GlobalTheory.CompanionTheory.ModelS.ipK κ x x).re) ∧ (∀ x y z : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ (x + y) z = GlobalTheory.CompanionTheory.ModelS.ipK κ x z + GlobalTheory.CompanionTheory.ModelS.ipK κ y z) ∧ (∀ (c : ℂ) (x y : GlobalTheory.CompanionTheory.ModelS.SmF n), GlobalTheory.CompanionTheory.ModelS.ipK κ (c • x) y = conj c * GlobalTheory.CompanionTheory.ModelS.ipK κ x y) ∧ ∀ x : GlobalTheory.CompanionTheory.ModelS.SmF n, GlobalTheory.CompanionTheory.ModelS.ipK κ x x = 0 → ∀ k : Matrix.unitaryGroup (Fin n) ℂ, x.1 k.1 = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.L2InnerProduct.ipK_form
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem eq_smul_of_commute_of_ev : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  intro n V _ _ F1 F2 hfin z hz ev c hev hS x
  set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
  set y : V := z x - c • x with hy
  obtain ⟨S₁, hfd, hyS₁, hst⟩ := hfin y
  have hpres : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      exact hst a b
    | algebraMap r =>
      intro w hw
      simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
    | add S T _ _ hS' hT' =>
      intro w hw
      exact S₁.add_mem (hS' w hw) (hT' w hw)
    | mul S T _ _ hS' hT' =>
      intro w hw
      exact hS' _ (hT' w hw)
  have hcomm : ∀ T ∈ A, z * T = T * z := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl⟩ := hT
      have h1 := (hz a b).1
      have h2 := (hz a b).2
      show z * (F1 a b + F2 a b) = (F1 a b + F2 a b) * z
      rw [mul_add, add_mul, h1, h2]
    | algebraMap r => exact (Algebra.commutes r z).symm
    | add S T _ _ hS' hT' => rw [mul_add, add_mul, hS', hT']
    | mul S T _ _ hS' hT' => rw [← mul_assoc, hS', mul_assoc, hT', mul_assoc]
  let S : Submodule ℂ V := (Subalgebra.toSubmodule A).map (LinearMap.applyₗ y)
  have hmem : ∀ w, w ∈ S ↔ ∃ T ∈ A, T y = w := by
    intro w
    simp [S, Submodule.mem_map]
  have hle : S ≤ S₁ := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    exact hpres T hT y hyS₁
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
  have hSst : ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    refine (hmem _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
  have hSev : ∀ w ∈ S, ev w = 0 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hmem w).1 hw
    have hzT : T (z x) = z (T x) := (LinearMap.congr_fun (hcomm T hT) x).symm
    rw [hy, map_sub, map_smul, hzT, map_sub, map_smul, hev, smul_eq_mul, sub_self]
  have hyS : y ∈ S := (hmem y).2 ⟨1, A.one_mem, rfl⟩
  exact sub_eq_zero.1 (hS S hSfd hSst hSev y hyS)

end GlobalTheory.CompanionTheory.ModelS
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_acts_by_scalar_on_cyclic : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), (∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → ∀ (z : Module.End ℂ V), (∀ a b, z * F1 a b = F1 a b * z ∧ z * F2 a b = F2 a b * z) → ∀ (ev : V →ₗ[ℂ] ℂ) (c : ℂ), (∀ v, ev (z v) = c * ev v) → (∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) → ∀ w ∈ S, w = 0) → ∀ x : V, z x = c • x := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.eq_smul_of_commute_of_ev
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.EvGel

section Dual

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def dualFam (E : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ (Module.Dual ℂ V) :=
  fun a b => (E b a).dualMap

theorem dualFam_apply (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    dualFam E a b φ v = φ (E b a v) := rfl

theorem glRel_dualFam {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (dualFam E) := by
  intro a b c d
  refine LinearMap.ext fun φ => LinearMap.ext fun v => ?_
  have h2 := congrArg (fun T : Module.End ℂ V => φ (T v)) (hE d c b a)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, dualFam_apply]
  by_cases h1 : b = c <;> by_cases h3 : d = a
  · subst h1; subst h3; simpa [dualFam_apply] using h2
  · subst h1; simpa [dualFam_apply, h3, Ne.symm h3] using h2
  · subst h3; simpa [dualFam_apply, h1, Ne.symm h1] using h2
  · simpa [dualFam_apply, h1, h3, Ne.symm h1, Ne.symm h3] using h2

theorem pow_dualFam (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) (φ : Module.Dual ℂ V) (v : V) :
    ((Matrix.of (dualFam E) : Matrix (Fin n) (Fin n) (Module.End ℂ (Module.Dual ℂ V))) ^ m) a b φ v =
      φ (((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) b a v) := by
  induction m generalizing a b φ v with
  | zero =>
    by_cases h : a = b
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  | succ m ih =>
    rw [pow_succ', pow_succ, Matrix.mul_apply, Matrix.mul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
      LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Module.End.mul_apply, Matrix.of_apply, dualFam_apply, ih]

end Dual

theorem epow_eq_pow {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem ev_gelA : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
    (∀ a b, b < a → ∀ v, ev (E a b v) = 0) → (∀ a v, ev (E a a v) = x a * ev v) →
    ∀ (m : ℕ) (v : V), ev (gelA E m v) =
      GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v := by
  intro n V _ _ E hE ev x hlow hdiag m v
  have hHW : Formalism.REAL.IsHW (dualFam E) x ev :=
    ⟨fun a => LinearMap.ext fun w => by simp [dualFam_apply, hdiag],
      fun a b hab => LinearMap.ext fun w => by simpa [dualFam_apply] using hlow b a hab w⟩
  have h1 := GlobalTheory.PhiEigenfun.trace_pow_hw (dualFam E) x ev (glRel_dualFam hE) hHW m
  have h2 := congrArg (fun φ : Module.Dual ℂ V => φ v) h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, pow_dualFam, smul_eq_mul] at h2
  have hval : GlobalTheory.Dec.gelfVal (fun a : Fin n => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m =
      ∑ a, ∑ b, (Formalism.REAL.Amat (Formalism.REAL.lsh x) ^ m) a b := by
    have : (fun c : Fin n => x c + ((n : ℂ) - 1) / 2 - ((c : ℕ) : ℂ) + ((n : ℂ) - 1) / 2) = Formalism.REAL.lsh x := by
      funext c
      simp only [Formalism.REAL.lsh]
      ring
    rw [GlobalTheory.Dec.gelfVal, this]
  rw [hval, ← h2, gelA, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [epow_eq_pow]

end GlobalTheory.CompanionTheory.EvGel
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_invariant_eval_lowest : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ), (∀ a b, b < a → ∀ v, ev (E a b v) = 0) → (∀ a v, ev (E a a v) = x a * ev v) → ∀ (m : ℕ) (v : V), ev (gelA E m v) = GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v := by
  atlas_forward_decl GlobalTheory.CompanionTheory.EvGel.ev_gelA
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem epow_eq_pow_of {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (m : ℕ) (a b : Fin n) :
    epow E m a b = ((Matrix.of E : Matrix (Fin n) (Fin n) (Module.End ℂ V)) ^ m) a b := by
  induction m generalizing a b with
  | zero => simp [epow, Matrix.one_apply]
  | succ m ih => simp only [epow, pow_succ', Matrix.mul_apply, Matrix.of_apply, ih]

theorem gelA_central : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E →
    ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  intro n V _ _ E hE m a b
  rw [eq_comm, ← sub_eq_zero]
  simp only [gelA, epow_eq_pow_of]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [GlobalTheory.SmoothForms.comm_pow_of_apply E hE, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

end GlobalTheory.CompanionTheory.ModelS
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_invariant_commute_generator : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.gelA_central
end

section
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

theorem commute_epow_of_units {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V)
    (hT : ∀ a b, T * E a b = E a b * T) (m : ℕ) (a b : Fin n) :
    Commute T (epow E m a b) := by
  induction m generalizing a b with
  | zero =>
    simp only [epow]
    split_ifs
    · exact Commute.one_right T
    · exact Commute.zero_right T
  | succ m ih =>
    simp only [epow]
    exact Commute.sum_right _ _ _ fun c _ => Commute.mul_right (hT a c) (ih c b)

theorem gelA_commute_of_units : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
    (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  intro n V _ _ E T hT m
  have h : Commute T (gelA E m) :=
    Commute.sum_right _ _ _ fun a _ => commute_epow_of_units E T hT m a a
  exact h.eq.symm

end GlobalTheory.CompanionTheory.ModelS
end
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_invariant_commute_of_commute : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V), (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units
end

section
section
theorem GlobalTheory.CompanionTheory.ModelS.gelfVal_perm :
    ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ),
      GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k :=
  fun _ χ σ k => GlobalTheory.CompanionTheory.WaveMult.gelfVal_comp_perm χ σ k
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfand_value_perm_invariant : ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ), GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.gelfVal_perm
end

section
section
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.ReversedBlocks

variable {n : ℕ}

theorem lower_iff (P : Fin n → Prop) [DecidablePred P] (hP : ∀ a b, a ≤ b → P b → P a) (b : Fin n) :
    P b ↔ (b : ℕ) < (univ.filter P).card :=
  _root_.UpperTheory.Reformulated.B.Re1.lower_iff P hP b

def lowC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b < lev a).card

def topC (lev : Fin n → ℕ) (a : Fin n) : ℕ := (univ.filter fun b => lev b ≤ lev a).card

theorem lt_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b < lev a ↔ (b : ℕ) < lowC lev a :=
  lower_iff (fun b => lev b < lev a) (fun _ _ h hb => lt_of_le_of_lt (hm h) hb) b

theorem le_iff {lev : Fin n → ℕ} (hm : Monotone lev) (a b : Fin n) : lev b ≤ lev a ↔ (b : ℕ) < topC lev a :=
  lower_iff (fun b => lev b ≤ lev a) (fun _ _ h hb => le_trans (hm h) hb) b

theorem high_add_topC (lev : Fin n → ℕ) (a : Fin n) :
    (univ.filter fun b => lev a < lev b).card + topC lev a = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun b => lev a < lev b)
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  unfold topC
  exact h

def rv (lev : Fin n → ℕ) (a : Fin n) : ℕ := lowC lev a + (topC lev a - 1) - a

theorem rv_bounds {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) :
    lowC lev a ≤ a ∧ (a : ℕ) < topC lev a ∧ rv lev a + a + 1 = lowC lev a + topC lev a := by
  have h1 : ¬ (a : ℕ) < lowC lev a := fun h => lt_irrefl _ ((lt_iff hm a a).2 h)
  have h2 : (a : ℕ) < topC lev a := (le_iff hm a a).1 le_rfl
  unfold rv
  omega

theorem rv_lt {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rv lev a < n := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have := high_add_topC lev a
  omega

def rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : Fin n := ⟨rv lev a, rv_lt hm a⟩

theorem lev_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : lev (rf hm a) = lev a := by
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  apply le_antisymm
  · exact (le_iff hm a _).2 (by simp only [rf]; omega)
  · exact not_lt.1 fun h => by
      have := (lt_iff hm a _).1 h
      simp only [rf] at this
      omega

theorem rf_rf {lev : Fin n → ℕ} (hm : Monotone lev) (a : Fin n) : rf hm (rf hm a) = a := by
  have hl := lev_rf hm a
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  obtain ⟨k1, k2, k3⟩ := rv_bounds hm (rf hm a)
  have e1 : lowC lev (rf hm a) = lowC lev a := by simp only [lowC, hl]
  have e2 : topC lev (rf hm a) = topC lev a := by simp only [topC, hl]
  apply Fin.ext
  have e3 : ((rf hm a : Fin n) : ℕ) = rv lev a := rfl
  have e4 : ((rf hm (rf hm a) : Fin n) : ℕ) = rv lev (rf hm a) := rfl
  omega

theorem exists_perm_yZ : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
    ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
      (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  intro n lam lev h
  obtain ⟨hm, hc⟩ := h
  refine ⟨Function.Involutive.toPerm (rf hm) (rf_rf hm), fun a => ?_⟩
  have hv : (Function.Involutive.toPerm (rf hm) (rf_rf hm)) a = rf hm a := rfl
  rw [hv]
  have hl : lam (rf hm a) = lam a := hc _ _ (lev_rf hm a)
  obtain ⟨h1, h2, h3⟩ := rv_bounds hm a
  have h4 := high_add_topC lev a
  have c3 : ((rv lev a : ℕ) : ℂ) + ((a : ℕ) : ℂ) + 1 = (lowC lev a : ℂ) + (topC lev a : ℂ) := by exact_mod_cast h3
  have c4 : (((univ.filter fun b => lev a < lev b).card : ℕ) : ℂ) + (topC lev a : ℂ) = (n : ℂ) := by exact_mod_cast h4
  have e3 : (((rf hm a : Fin n) : ℕ) : ℂ) = (rv lev a : ℂ) := rfl
  have hlow : (((univ.filter fun b => lev b < lev a).card : ℕ) : ℂ) = (lowC lev a : ℂ) := rfl
  simp only [GlobalTheory.CompanionTheory.ModelS.yZ, GlobalTheory.CompanionTheory.ModelS.muZ, infOf, hl, e3]
  push_cast
  rw [hlow]
  linear_combination (-1 : ℂ) * c3 - c4

end GlobalTheory.CompanionTheory.ModelS.ReversedBlocks
end

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char : ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev → ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n, (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ) = infOf lam false (σ a) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ
end

section
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

theorem kF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {F1 F2 : Fin n → Fin n → Module.End ℂ V}
    (g1 : Formalism.REAL.GlRel F1) (g2 : Formalism.REAL.GlRel F2) (cm : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) :
    Formalism.REAL.GlRel (kF F1 F2) := by
  intro a b c d
  have e : kF F1 F2 a b * kF F1 F2 c d - kF F1 F2 c d * kF F1 F2 a b =
      (F1 a b * F1 c d - F1 c d * F1 a b) + (F2 a b * F2 c d - F2 c d * F2 a b) +
        (F1 a b * F2 c d - F2 c d * F1 a b) - (F1 c d * F2 a b - F2 a b * F1 c d) := by
    simp only [kF]
    noncomm_ring
  rw [e, g1 a b c d, g2 a b c d, cm a b c d, cm c d a b]
  simp only [kF, sub_self, add_zero, sub_zero]
  split_ifs <;> first | abel | (simp; done) | (simp; abel)

theorem barF_gl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {F2 : Fin n → Fin n → Module.End ℂ V}
    (g2 : Formalism.REAL.GlRel F2) : Formalism.REAL.GlRel (barF F2) := by
  intro a b c d
  have h := g2 b a d c
  simp only [barF, neg_mul_neg]
  rw [h]
  simp only [eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
  split_ifs <;> first | abel | (simp; done) | (simp; abel)

theorem muZ_cast (lam : Fin n → ℤ) (lev : Fin n → ℕ) (a : Fin n) : ((muZ lam lev a : ℤ) : ℝ) = muQ lam lev a := by
  simp only [muZ, muQ, rhoU]
  push_cast
  ring

theorem model_of_ops (lam : Fin n → ℤ) (lev : Fin n → ℕ) (hlev : IsLev lam lev)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V) (f : V)
    (ev : V →ₗ[ℂ] ℂ) (gl1 : Formalism.REAL.GlRel F1) (gl2 : Formalism.REAL.GlRel F2)
    (cm : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b)
    (unitK : ∀ a b (x y : V), ⟪kF F1 F2 a b x, y⟫_ℂ = ⟪x, kF F1 F2 b a y⟫_ℂ)
    (gen : ∀ x : V, ∃ T ∈ alg F1 F2, T f = x) (S₀ : Submodule ℂ V) (fd : FiniteDimensional ℂ S₀) (hf : f ∈ S₀)
    (st : ∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) (hw : f ∈ hwSp F1 F2 (muQ lam lev)) (hev : ev f ≠ 0)
    (e1l : ∀ a b v, lev b ≤ lev a → a ≠ b → ev (F1 a b v) = 0) (e1d : ∀ a v, ev (F1 a a v) = (lam a : ℂ) * ev v)
    (e2l : ∀ a b v, lev b ≤ lev a → a ≠ b → ev (barF F2 a b v) = 0)
    (e2d : ∀ a v, ev (barF F2 a a v) = (yZ lam lev a : ℂ) * ev v)
    (sep : ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → (∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S) → (∀ w ∈ S, ev w = 0) →
      ∀ w ∈ S, w = 0) : Nonempty (Model lam lev) := by
  have gK := kF_gl gl1 gl2 cm
  have gB := barF_gl gl2
  have lf := GlobalTheory.T.exists_k_finite_submodule_containing n V F1 F2 gl1 gl2 cm f gen S₀ fd hf st
  have hlow : ∀ a b : Fin n, b < a → lev b ≤ lev a ∧ a ≠ b := fun a b h => ⟨hlev.1 h.le, h.ne'⟩
  refine ⟨{ W := V, F1 := F1, F2 := F2, f := f, gl1 := gl1, gl2 := gl2, comm := cm, unitK := unitK, locFin := lf,
            hw := hw, ne := fun h => hev (by rw [h, map_zero]), ch1 := ?_, ch2 := ?_, cone := ?_ }⟩
  · intro m x
    refine GlobalTheory.T.center_acts_by_scalar_on_cyclic n V F1 F2 lf (gelA F1 m) (fun a b => ⟨GlobalTheory.T.gelfand_invariant_commute_generator n V F1 gl1 m a b, GlobalTheory.T.gelfand_invariant_commute_of_commute n V F1 (F2 a b)
      (fun c d => (cm c d a b).symm) m⟩) ev _ (fun v => ?_) sep x
    have h := GlobalTheory.T.gelfand_invariant_eval_lowest n V F1 gl1 ev (fun a => (lam a : ℂ)) (fun a b hba v => e1l a b v (hlow a b hba).1 (hlow a b hba).2)
      e1d m v
    rw [h]
    congr 2
    funext a
    simp [infOf]
  · intro m x
    refine GlobalTheory.T.center_acts_by_scalar_on_cyclic n V F1 F2 lf (gelA (barF F2) m) (fun a b => ⟨?_, ?_⟩) ev _ (fun v => ?_) sep x
    · refine GlobalTheory.T.gelfand_invariant_commute_of_commute n V (barF F2) (F1 a b) (fun c d => ?_) m
      simp only [barF, mul_neg, neg_mul, cm a b d c]
    · have h := GlobalTheory.T.gelfand_invariant_commute_generator n V (barF F2) gB m b a
      simp only [barF, mul_neg, neg_mul, neg_inj] at h
      simpa [barF] using h
    · have h := GlobalTheory.T.gelfand_invariant_eval_lowest n V (barF F2) gB ev (fun a => (yZ lam lev a : ℂ))
        (fun a b hba v => e2l a b v (hlow a b hba).1 (hlow a b hba).2) e2d m v
      rw [h]
      obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char n lam lev hlev
      have : (fun a : Fin n => (yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) =
          fun a => infOf lam false (σ a) := funext hσ
      rw [this, GlobalTheory.T.gelfand_value_perm_invariant n (infOf lam false) σ m]
  · intro ν x hx hx0
    set A := Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = kF F1 F2 a b} with hA
    refine GlobalTheory.T.highest_weight_mem_cone n V (kF F1 F2) gK lev hlev.1 ev (muQ lam lev) ν x hx (fun a b v hl hne => ?_) (fun a v => ?_) ?_
    · have h1 := e1l a b v hl.ge hne
      have h2 := e2l b a v hl.le hne.symm
      simp only [barF, LinearMap.neg_apply, map_neg, neg_eq_zero] at h2
      simp [kF, h1, h2]
    · have h1 := e1d a v
      have h2 := e2d a v
      simp only [barF, LinearMap.neg_apply, map_neg] at h2
      have hm : (muQ lam lev a : ℂ) = (lam a : ℂ) - (yZ lam lev a : ℂ) := by
        rw [← muZ_cast]
        simp [yZ]
      simp only [kF, LinearMap.add_apply, map_add, h1, hm]
      linear_combination -h2
    · by_contra hcon
      push_neg at hcon
      obtain ⟨S₁, fd₁, hx₁, st₁⟩ := lf x
      have hstab : ∀ T ∈ A, ∀ w ∈ S₁, T w ∈ S₁ := by
        intro T hT
        induction hT using Algebra.adjoin_induction with
        | mem T hT => obtain ⟨a, b, rfl⟩ := hT; exact st₁ a b
        | algebraMap r => intro w hw; simpa [Module.algebraMap_end_apply] using S₁.smul_mem r hw
        | add T T' _ _ h h' => intro w hw; exact S₁.add_mem (h w hw) (h' w hw)
        | mul T T' _ _ h h' => intro w hw; exact h _ (h' w hw)
      let S : Submodule ℂ V := A.toSubmodule.map (LinearMap.applyₗ x)
      have hS : ∀ w, w ∈ S ↔ ∃ T ∈ A, T x = w := by
        intro w
        simp [S, Submodule.mem_map]
      have hle : S ≤ S₁ := by
        intro w hw
        obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact hstab T hT x hx₁
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hle
      have h0 := sep S inferInstance (fun a b w hw => ?_) (fun w hw => ?_) x ((hS x).2 ⟨1, A.one_mem, rfl⟩)
      · exact hx0 h0
      · obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact (hS _).2 ⟨kF F1 F2 a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, rfl⟩) hT, rfl⟩
      · obtain ⟨T, hT, rfl⟩ := (hS w).1 hw
        exact hcon T hT

theorem res_gl {M : Type} [AddCommGroup M] [Module ℂ M] (V : Submodule ℂ M) (E : Fin n → Fin n → Module.End ℂ M)
    (hE : ∀ a b, ∀ v ∈ V, E a b v ∈ V) (h : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (fun a b => (E a b).restrict (hE a b)) := by
  intro a b c d
  ext v
  have := congrArg (fun F => F (v : M)) (h a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, LinearMap.restrict_apply]
  rw [this]
  split_ifs <;> simp

theorem first_raising_mem_equivariant (lev : Fin n → ℕ) (φ : Mat n → ℂ) (a b : Fin n) {h : SmF n} (hh : h ∈ Eqv lev φ) :
    e1 DR a b h ∈ Eqv lev φ := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)
    (Submodule.smul_mem _ _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)))

theorem first_lowering_mem_equivariant (lev : Fin n → ℕ) (φ : Mat n → ℂ) (a b : Fin n) {h : SmF n} (hh : h ∈ Eqv lev φ) :
    f1 DR a b h ∈ Eqv lev φ := by
  simp only [f1, LinearMap.smul_apply, LinearMap.add_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)
    (Submodule.smul_mem _ _ (GlobalTheory.T.right_derivative_preserves_equivariant n lev φ _ h hh)))

theorem evaluation_raising_lowering (lev : Fin n → ℕ) (f h : SmF n) (hf : f ∈ Eqv lev f.1) (h1 : f.1 1 = 1) (hh : h ∈ Eqv lev f.1)
    (a b : Fin n) (hab : lev b ≤ lev a) :
    (e1 DR a b h).1 1 = (e1 DR a b f).1 1 * h.1 1 ∧ (f1 DR a b h).1 1 = (f1 DR a b f).1 1 * h.1 1 := by
  have hX : ∀ c : ℂ, ∀ a' b', lev a' < lev b' → (Matrix.single a b c : Mat n) a' b' = 0 := by
    intro c a' b' hlt
    rw [Matrix.single_apply_of_ne]
    rintro ⟨rfl, rfl⟩
    exact absurd hlt (not_lt.2 hab)
  have d1 := GlobalTheory.T.right_derivative_lower_block_at_one n lev f h hf h1 hh _ (hX 1)
  have d2 := GlobalTheory.T.right_derivative_lower_block_at_one n lev f h hf h1 hh _ (hX Complex.I)
  constructor
  · simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
      Pi.sub_apply, d1, d2, smul_eq_mul]
    ring
  · simp only [f1, LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, Pi.smul_apply,
      Pi.add_apply, d1, d2, smul_eq_mul]
    ring

theorem modelEx_main : ModelEx := by
  intro n lam hlam lev hlev
  classical
  letI : MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _
  haveI : BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := GlobalTheory.T.exists_haar_unitary_group n
  have hmem := GlobalTheory.T.inducedFunction_smooth n lam hlam lev hlev
  let F : SmF n := ⟨fRaw lam lev, hmem⟩
  have hF : F.1 = fRaw lam lev := rfl
  have hFe : F ∈ Eqv lev F.1 := fun p hp g hg => GlobalTheory.T.inducedFunction_parabolic_equivariant n lam hlam lev hlev p hp g hg
  have hF1 : F.1 1 = 1 := GlobalTheory.T.inducedFunction_at_one n lam lev
  let A := Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}
  have hcyc : ∀ w, w ∈ cyc F ↔ ∃ T ∈ A, T F = w := by
    intro w
    simp [cyc, A, Submodule.mem_map]
  have hEq : ∀ T ∈ A, ∀ h ∈ Eqv lev F.1, T h ∈ Eqv lev F.1 := by
    intro T hT
    induction hT using Algebra.adjoin_induction with
    | mem T hT =>
      obtain ⟨a, b, rfl | rfl⟩ := hT
      · exact fun h hh => first_raising_mem_equivariant lev _ a b hh
      · intro h hh
        simp only [e2, LinearMap.neg_apply]
        exact Submodule.neg_mem _ (first_lowering_mem_equivariant lev _ b a hh)
    | algebraMap r => intro w hw; simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hw
    | add T T' _ _ h h' => intro w hw; exact Submodule.add_mem _ (h w hw) (h' w hw)
    | mul T T' _ _ h h' => intro w hw; exact h _ (h' w hw)
  have hWE : ∀ w ∈ cyc F, w ∈ Eqv lev F.1 := by
    intro w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact hEq T hT F hFe
  have st1 : ∀ a b, ∀ w ∈ cyc F, e1 DR a b w ∈ cyc F := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact (hcyc _).2 ⟨e1 DR a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩) hT, rfl⟩
  have st2 : ∀ a b, ∀ w ∈ cyc F, e2 DR a b w ∈ cyc F := by
    intro a b w hw
    obtain ⟨T, hT, rfl⟩ := (hcyc w).1 hw
    exact (hcyc _).2 ⟨e2 DR a b * T, A.mul_mem (Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩) hT, rfl⟩
  obtain ⟨hsym, hnn, hadd, hsm, hdef⟩ := GlobalTheory.T.l2_inner_product_hermitian_form n κ
  have hzero : ∀ w ∈ cyc F, (∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0) → w = 0 := by
    intro w hw hk
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · obtain ⟨p, hp, k, rfl⟩ := GlobalTheory.T.iwasawa_parabolic_unitary n lev hlev.1 g hg
      have := hWE w hw p hp k.1 (GlobalTheory.CompanionTheory.ModelS.unit_mem k)
      simp [this, hk k]
    · exact w.2.2 g hg
  let core : InnerProductSpace.Core ℂ (cyc F) :=
    { inner := fun x y => ipK κ x.1 y.1
      conj_inner_symm := fun x y => hsym x.1 y.1
      re_inner_nonneg := fun x => hnn x.1
      add_left := fun x y z => hadd x.1 y.1 z.1
      smul_left := fun x y c => hsm c x.1 y.1
      definite := fun x hx => Subtype.ext (hzero x.1 x.2 (hdef x.1 hx)) }
  letI : NormedAddCommGroup (cyc F) := @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ core
  letI : InnerProductSpace ℂ (cyc F) := InnerProductSpace.ofCore core.toCore
  obtain ⟨g1, g2, cm⟩ := GlobalTheory.CompanionTheory.GLK.Pair.gl_pair n (SmF n) DR (GlobalTheory.T.right_derivative_real_lie_hom n).1 (GlobalTheory.T.right_derivative_real_lie_hom n).2.1 (GlobalTheory.T.right_derivative_real_lie_hom n).2.2
  let F1 : Fin n → Fin n → Module.End ℂ (cyc F) := fun a b => (e1 DR a b).restrict (st1 a b)
  let F2 : Fin n → Fin n → Module.End ℂ (cyc F) := fun a b => (e2 DR a b).restrict (st2 a b)
  have hKc : ∀ a b (x : cyc F), ((kF F1 F2 a b x : cyc F) : SmF n) = Kf a b x.1 := fun _ _ _ => rfl
  let f : cyc F := ⟨F, (hcyc F).2 ⟨1, A.one_mem, rfl⟩⟩
  let ev : cyc F →ₗ[ℂ] ℂ := ev1.comp (cyc F).subtype
  obtain ⟨S₁, fd₁, hf₁, st₁⟩ := GlobalTheory.T.inducedFunction_k_finite n lam hlam lev hlev F hF
  obtain ⟨hh1, hh2⟩ := GlobalTheory.T.inducedFunction_k_highest_weight n lam hlam lev hlev F hF
  have hder := GlobalTheory.T.inducedFunction_derivative_at_one n lam hlam lev hlev F hF
  refine model_of_ops lam lev hlev F1 F2 f ev (res_gl _ _ st1 g1) (res_gl _ _ st2 g2) ?_ ?_ ?_
    (S₁.comap (cyc F).subtype) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b c d
    refine LinearMap.ext fun w => Subtype.ext ?_
    exact congrArg (fun T => T w.1) (cm a b c d)
  · intro a b x y
    exact GlobalTheory.T.k_action_skew_adjoint_l2 n κ (GlobalTheory.T.integral_right_derivative_eq_zero n κ) a b x.1 y.1
  · intro x
    have key : ∀ T ∈ A, ∃ T' ∈ alg F1 F2, ∀ w : cyc F, ((T' w : cyc F) : SmF n) = T w.1 := by
      intro T hT
      induction hT using Algebra.adjoin_induction with
      | mem T hT =>
        obtain ⟨a, b, rfl | rfl⟩ := hT
        · exact ⟨F1 a b, Algebra.subset_adjoin ⟨a, b, Or.inl rfl⟩, fun _ => rfl⟩
        · exact ⟨F2 a b, Algebra.subset_adjoin ⟨a, b, Or.inr rfl⟩, fun _ => rfl⟩
      | algebraMap r =>
        exact ⟨algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun w => by simp [Module.algebraMap_end_apply]⟩
      | add T T' _ _ h h' =>
        obtain ⟨P, hP, hP'⟩ := h
        obtain ⟨Q, hQ, hQ'⟩ := h'
        exact ⟨P + Q, Subalgebra.add_mem _ hP hQ, fun w => by simp [hP', hQ']⟩
      | mul T T' _ _ h h' =>
        obtain ⟨P, hP, hP'⟩ := h
        obtain ⟨Q, hQ, hQ'⟩ := h'
        exact ⟨P * Q, Subalgebra.mul_mem _ hP hQ, fun w => by simp [hP', hQ']⟩
    obtain ⟨T, hT, hTx⟩ := (hcyc x.1).1 x.2
    obtain ⟨T', hT', hc⟩ := key T hT
    exact ⟨T', hT', Subtype.ext (by rw [hc f]; exact hTx)⟩
  · let φ : ↥(S₁.comap (cyc F).subtype) →ₗ[ℂ] S₁ :=
      ((cyc F).subtype ∘ₗ (S₁.comap (cyc F).subtype).subtype).codRestrict S₁ (fun x => x.2)
    exact Module.Finite.of_injective φ (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : ↥S₁ => (t : SmF n)) h)))
  · exact hf₁
  · intro a b w hw
    exact st₁ a b w.1 hw
  · refine ⟨fun a => ?_, fun a b hab _ => ?_⟩
    · apply Subtype.ext
      rw [hKc]
      have := hh2 a
      rw [← muZ_cast]
      simpa [f] using this
    · apply Subtype.ext
      rw [hKc]
      exact hh1 a b hab
  · show F.1 1 ≠ 0
    rw [hF1]
    exact one_ne_zero
  · intro a b v hl hne
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a b hl).1
    have h0 := (hder a b hl).1
    show (e1 DR a b v.1).1 1 = 0
    rw [this, h0, if_neg hne, zero_mul]
  · intro a v
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a a le_rfl).1
    have h0 := (hder a a le_rfl).1
    show (e1 DR a a v.1).1 1 = _ * v.1.1 1
    rw [this, h0, if_pos rfl]
  · intro a b v hl hne
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a b hl).2
    have h0 := (hder a b hl).2
    show (-(e2 DR b a v.1)).1 1 = 0
    simp only [e2, neg_neg, LinearMap.neg_apply]
    rw [this, h0, if_neg hne, zero_mul]
  · intro a v
    have := (evaluation_raising_lowering lev F v.1 hFe hF1 (hWE _ v.2) a a le_rfl).2
    have h0 := (hder a a le_rfl).2
    show (-(e2 DR a a v.1)).1 1 = _ * v.1.1 1
    simp only [e2, neg_neg, LinearMap.neg_apply]
    rw [this, h0, if_pos rfl]
  · intro S fdS stS ev0 w hw
    haveI := fdS
    have hS := GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one n (S.map (cyc F).subtype) inferInstance (by
        intro a b u hu
        obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
        exact Submodule.mem_map.2 ⟨kF F1 F2 a b v, stS a b v hv, rfl⟩) (by
        intro u hu
        obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hu
        exact ev0 v hv) w.1 (Submodule.mem_map.2 ⟨w, hw, rfl⟩)
    exact Subtype.ext (hzero w.1 w.2 hS)

end GlobalTheory.CompanionTheory.ModelS
end
end

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_model_exists : PositivityTheory.RgBcC.RealD.ModelEx := by
  atlas_forward_decl GlobalTheory.CompanionTheory.ModelS.modelEx_main
end
