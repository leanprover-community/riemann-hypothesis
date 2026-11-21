import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNefHermitianTwistingSheaf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ManyIndependentProductsInFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairSectionMemBallExpOfProjArithVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorialMulRankLeDegreeOfIndepSmallSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxMonomialFamilyProdMemNormBallOfExponentLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarieStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleNefHermitianSmallSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermPairPowSectionMemAndNormPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffExistsSmallSectionDiffe

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} {f : J → X.functionField}

theorem regAt_nhds {x : X} {g : X.functionField} (h : RegAt x g) :
    ∃ U : X.Opens, x ∈ U ∧ ∀ y ∈ U, RegAt y g := by
  obtain ⟨U, hx, a, rfl⟩ := h.exists_fnOf
  exact ⟨U, hx, fun y hy => regAt_fnOf hy _ a⟩

theorem exists_min [Fintype J] [Nonempty J] (hf : Total f) (x : X) :
    ∃ j, ∀ l, RegAt x (f l / f j) := by
  have key : ∀ s : Finset J, s.Nonempty → ∃ j, ∀ l ∈ s, RegAt x (f l / f j) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨a, fun l hl => ?_⟩
      rw [Finset.mem_singleton.1 hl, div_self (hf.1 a)]
      exact (unitAt_one x).regAt
    | cons a s ha hs ih =>
      obtain ⟨j, hj⟩ := ih
      rcases hf.2 x a j with h | h
      ·
        refine ⟨j, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · exact h
        · exact hj l hl
      ·
        refine ⟨a, fun l hl => ?_⟩
        rcases Finset.mem_cons.1 hl with rfl | hl
        · rw [div_self (hf.1 l)]; exact (unitAt_one x).regAt
        · have e : f l / f a = f l / f j * (f j / f a) := by
            rw [div_mul_div_cancel₀ (hf.1 j)]
          rw [e]; exact (hj l hl).mul h
  obtain ⟨j, hj⟩ := key Finset.univ Finset.univ_nonempty
  exact ⟨j, fun l => hj l (Finset.mem_univ l)⟩

def inv (hf : Total f) (j : J) : X.functionFieldˣ := Units.mk0 (f j)⁻¹ (inv_ne_zero (hf.1 j))

theorem germOf_inv_eq (hf : Total f) {x : X} {j j' : J} (hj : ∀ l, RegAt x (f l / f j))
    (hj' : ∀ l, RegAt x (f l / f j')) : germOf x (inv hf j) = germOf x (inv hf j') := by
  rw [germOf_eq_iff]
  change UnitAt x ((f j')⁻¹ / (f j)⁻¹)
  rw [inv_div_inv]
  refine (unitAt_iff (div_ne_zero (hf.1 j) (hf.1 j'))).2 ⟨hj' j, ?_⟩
  rw [inv_div]
  exact hj j'

theorem isOpen_minSet [Finite J] (hf : Total f) (j : J) :
    IsOpen {y : X | ∀ l, RegAt y (f l / f j)} := by
  refine isOpen_iff_forall_mem_open.2 fun y hy => ?_
  choose V hV hV' using fun l => regAt_nhds (hy l)
  exact ⟨⋂ l, (V l : Set X), fun z hz l => hV' l z (Set.mem_iInter.1 hz l),
    isOpen_iInter_of_finite fun l => (V l).isOpen, Set.mem_iInter.2 hV⟩

variable [Fintype J] [Nonempty J]

def fsDiv (hf : Total f) : CartierDiv X :=
  show cartierGroup X from ⟨fun x => germOf x (inv hf (exists_min hf x).choose), fun x =>
    ⟨⟨_, isOpen_minSet hf (exists_min hf x).choose⟩, (exists_min hf x).choose_spec,
      inv hf (exists_min hf x).choose, fun y hy =>
        germOf_inv_eq hf (exists_min hf y).choose_spec hy⟩⟩

theorem isEqn_inv (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).IsEqn x (inv hf j) :=
  germOf_inv_eq hf (exists_min hf x).choose_spec hj

theorem mem_sections (hf : Total f) (l : J) : f l ∈ (fsDiv hf).sections :=
  CartierDiv.mem_sections.2 fun x =>
    ⟨_, isEqn_inv hf (exists_min hf x).choose_spec, by
      change RegAt x (f l * (f _)⁻¹)
      rw [← div_eq_mul_inv]
      exact (exists_min hf x).choose_spec l⟩

theorem generatesAt (hf : Total f) {x : X} {j : J} (hj : ∀ l, RegAt x (f l / f j)) :
    (fsDiv hf).GeneratesAt x (f j) :=
  ⟨_, isEqn_inv hf hj, by
    change UnitAt x (f j * (f j)⁻¹)
    rw [mul_inv_cancel₀ (hf.1 j)]
    exact unitAt_one x⟩

end GlobalTheory.HSNef.FSExist

namespace GlobalTheory.HSNef.FSExist

variable {X : Scheme.{0}} [IsIntegral X] {J : Type} [Fintype J] [Nonempty J] {f : J → X.functionField}
  [DecidableEq J]

def sec (hf : Total f) (l : J) : (toLB (fsDiv hf)).Sec :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose

theorem rat_sec (hf : Total f) (l : J) : (presents_toLB (fsDiv hf)).rat (sec hf l) = f l :=
  ((presents_toLB (fsDiv hf)).exists_rat_eq (mem_sections hf l)).choose_spec

theorem iSup_sec (hf : Total f) : ⨆ j, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (sec hf j) = ⊤ :=
  eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨(exists_min hf x).choose,
    ((presents_toLB (fsDiv hf)).generatesAt_rat_iff _).1 (by
      rw [rat_sec]; exact generatesAt hf (exists_min hf x).choose_spec)⟩

def expDiag (w : J → ℝ) : Matrix J J ℂ := Matrix.diagonal fun j => ((Real.exp (w j) : ℝ) : ℂ)

theorem det_expDiag (w : J → ℝ) : (expDiag w).det ≠ 0 := by
  classical
  rw [expDiag, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun j _ => Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'

theorem map_expDiag (w : J → ℝ) : (expDiag w).map (starRingEnd ℂ) = expDiag w := by
  ext i j
  by_cases h : i = j
  · subst h; rw [Matrix.map_apply, expDiag, Matrix.diagonal_apply_eq, Complex.conj_ofReal]
  · simp [expDiag, Matrix.diagonal_apply_ne _ h]

theorem sum_expDiag (w : J → ℝ) (v : J → ℂ) (a : J) :
    ∑ j, expDiag w j a * v j = ((Real.exp (w a) : ℝ) : ℂ) * v a := by
  classical
  rw [Finset.sum_eq_single a (fun j _ hj => by simp [expDiag, Matrix.diagonal_apply_ne _ hj])
    (fun h => (h (Finset.mem_univ a)).elim)]
  simp [expDiag]

end GlobalTheory.HSNef.FSExist

open GlobalTheory.HSNef.FSExist in

theorem GlobalTheory.HSNef.exists_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f →
      ∃ M : HermLB p, IsFS M f w := by
  intro k _ X _ p J _ _ f w hf
  classical
  let h := presents_toLB (fsDiv hf)
  refine ⟨HermLB.fs p (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (fun _ => expDiag w)
    (fun _ => det_expDiag w) (fun _ => ⟨1, one_mem _, by rw [mul_one, map_expDiag]⟩), ?_⟩
  refine ⟨fun i => i.1.2, h.isRatSec, fun x c hx => ⟨fun j => ?_, ?_⟩, fun σ y (c : (toLB (fsDiv hf)).ι) (hy : y ∈ ptsIn p σ ((toLB (fsDiv hf)).U c)) => ?_⟩
  · exact (c.2.2 x hx).regularAt_iff.1 (CartierDiv.mem_sections.1 (mem_sections hf j) x)
  · exact ⟨_, (c.2.2 x hx).generatesAt_iff.1 (generatesAt hf (exists_min hf x).choose_spec)⟩
  · refine (Weight.fsBasis_φ (p := p) (σ := σ) (isLB_toLB (fsDiv hf)) (sec hf) (iSup_sec hf) (expDiag w)
      (det_expDiag w) c y).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sum_expDiag]
    have e : f a * (c.1.2 : X.functionField) = fnOf _ c.2.1 ((sec hf a).f c) := by
      rw [← rat_sec hf a]; exact h.rat_mul (sec hf a) c c.2.1
    have e2 : ratVal (f a * (c.1.2 : X.functionField)) y =
        valR y.1 ((toLB (fsDiv hf)).U c) ((sec hf a).f c) := by
      rw [e]; exact ratVal_fnOf (U := (toLB (fsDiv hf)).U c) hy c.2.1 _
    rw [e2]
    rw [norm_mul, mul_pow, mul_comm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    norm_num
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f → ∃ M : HermLB p, IsFS M f w := by
  atlas_forward_decl GlobalTheory.HSNef.exists_isFS
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic
open ReciprocityTheory.L2DbarEstimates (V leviV)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem semiPos_of_isFS : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (D : ℕ) (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → M.SemiPos D := by
  intro k _ X _ p D M J _ f w hM σ i c y hy ξ
  classical
  obtain ⟨ρ, -, hreg, hφ⟩ := hM
  have hx : under y ∈ M.B.U i := mem_ptsIn.1 hy.2
  obtain ⟨hr, j0, hu⟩ := hreg (under y) i hx
  choose U hU a ha using fun j => (hr j).exists_fnOf
  let G (j : J) (v : V D) : ℂ := (Real.exp (w j) : ℂ) * ev p σ (U j) (a j) (c.e.symm v)
  let S : Set (CxPts p σ) := ptsIn p σ (M.B.U i) ∩ ⋂ j, ptsIn p σ (U j)
  have hSo : IsOpen S := (isOpen_ptsIn _).inter (isOpen_iInter_of_finite fun j => isOpen_ptsIn _)
  have hyS : y ∈ S := ⟨hy.2, Set.mem_iInter.2 fun j => mem_ptsIn.2 (hU j)⟩
  have hO := isOpen_over c.e hSo
  have hmO := mem_over c.e hy.1 hyS

  have hval (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ratVal (f j * (ρ i : X.functionField)) z = ev p σ (U j) (a j) z := by
    rw [← ha j]
    exact ratVal_fnOf (Set.mem_iInter.1 hz.2 j) _ _
  have hterm (z : CxPts p σ) (hz : z ∈ S) (j : J) :
      ‖ratVal (f j * (ρ i : X.functionField)) z‖ ^ 2 * Real.exp (2 * w j) =
        Complex.normSq ((Real.exp (w j) : ℂ) * ev p σ (U j) (a j) z) := by
    rw [hval z hz j, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq,
      ← Real.exp_add]
    ring_nf
  have hG (j : J) : ContDiffAt ℂ 2 (G j) (c.e y) := by
    have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (U j))
    have hm := mem_over c.e hy.1 (mem_ptsIn.2 (hU j))
    exact contDiffAt_const.mul ((((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
      (c.holo (U j) (a j))).contDiffAt (ho.mem_nhds hm)).of_le (by norm_cast)))
  let e := Fintype.equivFin J
  let u (b : Fin (Fintype.card J)) (v : V D) : ℝ := Complex.normSq (G (e.symm b) v)
  have hsum (v : V D) : ∑ b, u b v = ∑ j, Complex.normSq (G j v) :=
    Equiv.sum_comp e.symm fun j => Complex.normSq (G j v)
  have hev : (fun v => (((M.φ σ).φ i (c.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => ((Real.log (∑ b, u b v) : ℝ) : ℂ) := by
    filter_upwards [hO.mem_nhds hmO] with v hv
    rw [hφ σ _ i hv.2.1, hsum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => hterm _ hv.2 j
  have hpos : 0 < ∑ b, u b (c.e y) := by
    rw [hsum]
    simp only [G, c.e.left_inv hy.1]
    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨j0, Finset.mem_univ _, ?_⟩
    rw [← hterm y hyS j0]
    exact mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2) (Real.exp_pos _)
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr hev]
  exact ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
    (fun b => ReciprocityTheory.L2DbarEstimates.contDiffAt_normSq_comp (hG _))
    (fun b => ReciprocityTheory.L2DbarEstimates.logPshAt_normSq (hG _)) hpos ξ

end GlobalTheory.HSNef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiPos_of_isFubiniStudyOfRatFnFamily : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (D : ℕ) (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → M.SemiPos D := by
  atlas_forward_decl GlobalTheory.HSNef.semiPos_of_isFS
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenNef

theorem isNef_of_gen_small : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  intro _ k _ X _ p D hX M n s hsp hsm hs
  have hcov : ⨆ i, ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i) = ⊤ :=
    top_le_iff.1 fun x _ =>
      have ⟨i, hi⟩ := hs x
      Opens.mem_iSup.2 ⟨i, hi⟩
  exact GlobalTheory.VolBr.Model.isNef_of_small hX M hsp
    (GlobalTheory.TrueGeo.OfLattice.nefFib_of_isGenerated hX M (GlobalTheory.isGenerated_of_finite s hcov))
    fun x => have ⟨i, hi⟩ := hs x; ⟨s i, hsm i, hi⟩

end GlobalTheory.GenNef

end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNef_of_semiPos_generated_by_smallSections : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (n : ℕ) (s : Fin n → M.B.Sec), M.SemiPos D → (∀ i, s i ∈ M.smallSec) → (∀ x : X, ∃ i, x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s i)) → M.IsNef D := by
  atlas_forward_decl GlobalTheory.GenNef.isNef_of_gen_small
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FSNef

section Sec

variable {X : Scheme.{0}} [IsIntegral X]

open Classical in

def fnOnOpen (U : X.Opens) (g : X.functionField) (hg : ∀ x ∈ U, RegAt x g) : Γ(X, U) :=
  if h : genericPoint X ∈ U then (exists_fnOf_eq h hg).choose else 0

theorem fnOf_fnOnOpen {U : X.Opens} {g : X.functionField} (hg : ∀ x ∈ U, RegAt x g) (h : genericPoint X ∈ U) :
    fnOf U h (fnOnOpen U g hg) = g := by
  classical
  rw [fnOnOpen, dif_pos h]
  exact (exists_fnOf_eq h hg).choose_spec

def secOfRat (B : LB X) (ρ : B.ι → X.functionFieldˣ) (hρ : IsRatSec B ρ) (g : X.functionField)
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) : B.Sec where
  f c := fnOnOpen (B.U c) _ (hg c)
  compat i j := fn_ext fun h => by
    change fnOf _ h (resG X inf_le_left _) =
      fnOf _ h ((B.g i j : Γ(X, B.U i ⊓ B.U j)) * resG X inf_le_right _)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_fnOnOpen, fnOf_fnOnOpen, hρ i j h]
    ring

theorem fnOf_secOfRat {B : LB X} {ρ : B.ι → X.functionFieldˣ} (hρ : IsRatSec B ρ) {g : X.functionField}
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) (c : B.ι) (h : genericPoint X ∈ B.U c) :
    fnOf _ h ((secOfRat B ρ hρ g hg).f c) = g * ρ c :=
  fnOf_fnOnOpen (hg c) h

end Sec

theorem isNef_of_isFS : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → (∀ j, 0 ≤ w j) → M.IsNef D := by
  intro hA k _ X _ p D hX M J _ f w hFS hw
  have hsemi := GlobalTheory.T.semiPos_of_isFubiniStudyOfRatFnFamily k X p D M J f w hFS
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hFS
  let s : J → M.B.Sec := fun j => secOfRat M.B ρ hρ (f j) fun c x hx => (hreg x c hx).1 j
  have hs : ∀ j c (h : genericPoint X ∈ M.B.U c), fnOf _ h ((s j).f c) = f j * ρ c :=
    fun j c h => fnOf_secOfRat hρ _ c h
  let e := Fintype.equivFin J
  refine GlobalTheory.T.isNef_of_semiPos_generated_by_smallSections hA k X p D hX M (Fintype.card J) (fun i => s (e.symm i)) hsemi (fun i => ?_) (fun x => ?_)
  · intro σ y
    have hy : y ∈ ptsIn p σ (M.B.U (pick (M.φ σ).isLB y)) := mem_pick _ y
    have hg : genericPoint X ∈ M.B.U (pick (M.φ σ).isLB y) := gen_mem (mem_ptsIn.1 hy)
    have hval : ∀ l, secVal p σ (s l) (pick (M.φ σ).isLB y) y =
        ratVal (f l * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y := fun l => by
      rw [secVal_apply, ← ratVal_fnOf hy hg, hs]
    rw [Weight.nsq, hval, hφ σ y _ hy]
    obtain ⟨l, hl⟩ := (hreg _ _ (mem_ptsIn.1 hy)).2
    have hnn : ∀ m ∈ Finset.univ, 0 ≤ ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      fun m _ => by positivity
    have hpos : 0 < ∑ m, ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      lt_of_lt_of_le (mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl)) 2) (Real.exp_pos _))
        (Finset.single_le_sum hnn (Finset.mem_univ l))
    rw [Real.exp_neg, Real.exp_log hpos, ← div_eq_mul_inv, div_le_one hpos]
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ (e.symm i)))
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by linarith [hw (e.symm i)]))
  · obtain ⟨c, hc⟩ := exists_chart M.isLB x
    obtain ⟨j, hj⟩ := (hreg x c hc).2
    refine ⟨e j, ?_⟩
    rw [e.symm_apply_apply, mem_nonzeroLocus_iff _ c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs]
    exact hj

end GlobalTheory.HSNef.FSNef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → (∀ j, 0 ≤ w j) → M.IsNef D := by
  atlas_forward_decl GlobalTheory.HSNef.FSNef.isNef_of_isFS
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isFS_mem_pair : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  intro k _ X _ p M J _ f w h
  obtain ⟨ρ, hρ, hreg, -⟩ := h
  refine ⟨⟨M, M, ρ, ρ, hρ, hρ⟩, rfl, fun j x i c hi _ => ?_⟩
  have e : Pair.loc ⟨M, M, ρ, ρ, hρ, hρ⟩ 1 0 (f j) i c = f j * (ρ i : X.functionField) := by
    simp [Pair.loc]
  rw [e]
  exact (hreg x i hi).1 j

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ), IsFS M f w → ∃ P : Pair p, P.L = M ∧ ∀ j, f j ∈ P.H 1 0 := by
  atlas_forward_decl GlobalTheory.HSNef.isFS_mem_pair
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.RankNef

theorem rank_le_gdeg_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), P.L.IsNef D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hL J _ e x he hx hbox
  have hcz : CharZero X.functionField := by
    have := hX.charZero
    exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 this
  have htb : IsTranscendenceBasis ℤ x := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).2 x hx
  obtain ⟨A, hAamp, hAnef, s, hs, hs0⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hAr k X p D hX
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  let Q : Pair p := ⟨P.L, A, P.r, r', P.hr, hr'⟩
  have hQbox : ∀ c, boxFam e x c ∈ Q.H 1 0 := by
    intro c z i j hi _
    obtain ⟨j', hj'⟩ : ∃ j', z ∈ P.A.B.U j' := by
      have h1 : z ∈ (⨆ j, P.A.B.U j) := by rw [P.A.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 h1
    have h2 := hbox c z i j' hi hj'
    simpa [Pair.loc, Q] using h2
  have hbd : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ Q.Bl 1 0 (Real.exp u) :=
    fun c => GlobalTheory.T.pairSection_mem_ball_exp_of_projArithVariety k X p D hX Q 1 0 _ (hQbox c)
  choose u hu0 hu using hbd
  set t₀ : ℝ := ∑ c, u c with ht₀
  have ht₀0 : 0 ≤ t₀ := Finset.sum_nonneg fun c _ => hu0 c
  have hBl : ∀ c, boxFam e x c ∈ Q.Bl 1 0 (Real.exp t₀) := fun c =>
    ⟨(hu c).1, fun σ y => ((hu c).2 σ y).trans
      (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c)))⟩
  obtain ⟨ε, hεinj, hεrange, hεnu, -⟩ := RepDict.rep_dict k X p Q 0 1 Q.A (Pair.rep_base k X p Q).2.1
  have hsm : ∀ w ∈ A.smallSec, ε w ∈ Q.Bl 0 1 1 := by
    intro w hw
    refine ⟨?_, fun σ y => ?_⟩
    · rw [← SetLike.mem_coe, ← hεrange]; exact ⟨w, rfl⟩
    · have hnn : 0 ≤ Q.nu 0 1 σ y (ε w) := by
        unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      have h2 : Q.nu 0 1 σ y (ε w) ^ 2 ≤ 1 := by rw [hεnu]; exact hw σ y
      exact (pow_le_one_iff_of_nonneg hnn two_ne_zero).1 h2
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ Q.Bl 0 1 1, g ≠ 0 := by
    by_cases h : ε s = 0
    · refine ⟨ε 0, hsm 0 (HermLB.zero_mem_smallSec _), fun h0 => hs0 ?_⟩
      exact (hεinj (h0.trans h.symm)).symm
    · exact ⟨ε s, hsm s hs, h⟩
  have key : ∀ n : ℕ, 0 < n →
      (D.factorial : ℝ) * ((Fintype.card J * n ^ D : ℕ) : ℝ) ≤ gdeg ((P.L.pow n).tens A) D := by
    intro n hn
    have hrep : Q.Rep (n : ℤ) 1 ((Q.L.pow n).tens Q.A) := by
      have h1 := Pair.rep_pow k X p Q 1 0 Q.L n (Pair.rep_base k X p Q).1
      have h2 := Pair.rep_tens k X p Q _ _ 0 1 _ _ h1 (Pair.rep_base k X p Q).2.1
      simpa using h2
    have hamp : IsAmpleLB ((P.L.pow n).tens A).B :=
      GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample k X p D hX (P.L.pow n) A
        (nefFib_of_isNef (GlobalTheory.NefPow.isNef_pow hAr k X p D hX P.L n hL)) hAamp
    have hsp : ((P.L.pow n).tens A).SemiPos D := (hL.semiPos.pow n).tens hAnef.semiPos
    have hvec : ∀ m : ℕ, 0 < m → ∃ v : Fin ((Fintype.card J * n ^ D) * m ^ D) → X.functionField,
        LinearIndependent ℤ v ∧ ∀ i, v i ∈ Q.Bl (m * (n : ℤ)) (m * 1) (Real.exp ((t₀ * n) * m)) := by
      intro m hm
      obtain ⟨v0, hv0, hv0s⟩ := GlobalTheory.T.exists_linearIndependent_products_function_field X.functionField D x htb J e he (n * m) (Nat.mul_pos hn hm)
      have hcard : Fintype.card J * (n * m) ^ D = (Fintype.card J * n ^ D) * m ^ D := by rw [mul_pow]; ring
      have hgm : g ^ m ∈ Q.H ((m : ℤ) * 0) ((m : ℤ) * 1) :=
        (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).1
      have hgm0 : g ^ m ≠ 0 := pow_ne_zero _ hg0
      refine ⟨fun i => v0 (Fin.cast hcard.symm i) * g ^ m, ?_, fun i => ?_⟩
      · have hli := hv0.map' (LinearMap.mulRight ℤ (g ^ m))
          (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hgm0))
        exact hli.comp _ (Fin.cast_injective _)
      · obtain ⟨w, a, ha, hw⟩ := hv0s (Fin.cast hcard.symm i)
        have hprod := GlobalTheory.T.boxMonomialFamily_prod_mem_normBall_of_exponent_lt k X p Q D J e x 1 0 (Real.exp t₀) (Real.exp_pos _).le hBl (n * m) w a ha
        rw [← hw] at hprod
        obtain ⟨hmem, hnu⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q _ _ _ _ _ _ hprod.1 hgm
        have e1 : (((n * m : ℕ) : ℤ) * 1 + (m : ℤ) * 0) = (m : ℤ) * n := by push_cast; ring
        have e2 : (((n * m : ℕ) : ℤ) * 0 + (m : ℤ) * 1) = (m : ℤ) * 1 := by push_cast; ring
        rw [e1, e2] at hmem hnu
        refine ⟨hmem, fun σ y => ?_⟩
        rw [hnu, (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).2 σ y]
        have hA1 := hprod.2 σ y
        have hB1 : Q.nu 0 1 σ y g ^ m ≤ 1 := by
          have hnn : 0 ≤ Q.nu 0 1 σ y g := by
            unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
          exact pow_le_one₀ hnn (hg.2 σ y)
        have hnn' : 0 ≤ Q.nu ((n * m : ℕ) * 1) ((n * m : ℕ) * 0) σ y (v0 (Fin.cast hcard.symm i)) := by
          unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        have hexp : Real.exp t₀ ^ (n * m) = Real.exp ((t₀ * n) * m) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        calc _ ≤ Real.exp t₀ ^ (n * m) * 1 := mul_le_mul hA1 hB1 (pow_nonneg (by unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) _) (pow_nonneg (Real.exp_pos _).le _)
          _ = _ := by rw [mul_one, hexp]
    have := GlobalTheory.T.factorial_mul_rank_le_degree_of_indep_small_sections hAr hHS k X p D hX Q n 1 _ hrep hamp hsp (Fintype.card J * n ^ D) (t₀ * n) hvec
    exact this
  have hlim := GlobalTheory.T.tendsto_hermLineBundleGeometricDegree_pow_tens_div_pow hAr k X p D hX P.L A
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := by positivity
  rw [le_div_iff₀ hnD]
  have := key n hn
  push_cast at this
  nlinarith [this]

end GlobalTheory.HSNef.RankNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_geometricDegree_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), P.L.IsNef D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  atlas_forward_decl GlobalTheory.HSNef.RankNef.rank_le_gdeg_of_isNef
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fs_box_rank_le : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J]
    (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ),
    LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) →
    IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  intro hAr hHS k _ X _ p D hD M J _ e x w he hx hw hFS
  have hNef : M.IsNef D := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hAr k X p D hD M _ (boxFam e x) w hFS hw
  obtain ⟨P, hPL, hmem⟩ := GlobalTheory.T.isFubiniStudy_ratFns_mem_pairSections k X p M _ (boxFam e x) w hFS
  subst hPL
  exact GlobalTheory.T.rank_le_geometricDegree_of_isNef hAr hHS k X p D hD P hNef J e x he hx hmem

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_fubiniStudy_boxFamily : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) → IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  atlas_forward_decl GlobalTheory.HSNef.fs_box_rank_le
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_ne_zero {x : X} {h : X.functionField} (hh : UnitAt x h) : h ≠ 0 := by
  obtain ⟨b, hb, rfl⟩ := hh
  intro e
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (b * ↑hb.unit⁻¹) = 1 := by
    rw [IsUnit.mul_val_inv, map_one]
  rw [map_mul, e, zero_mul] at h1
  exact zero_ne_one h1

theorem regAt_div_unitAt {x : X} {g h : X.functionField} (hg : RegAt x g) (hh : UnitAt x h) :
    RegAt x (g / h) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb, hbh⟩ := hh
  refine ⟨a * ↑hb.unit⁻¹, ?_⟩
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField b *
      algebraMap (X.presheaf.stalk x) X.functionField ↑hb.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, ha, div_eq_mul_inv, ← hbh, eq_inv_of_mul_eq_one_right h1]

theorem le_shift_of_isFS_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ)
      (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' →
      (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  intro k _ X _ p M M' J J' _ _ f w w' ι Δ hι hM hM' hw
  rw [GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients]
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨ρ', hρ', hreg', hφ'⟩ := hM'
  simp only [Function.comp_apply] at hreg' hφ'

  have hq : ∀ (x : X) c d (j' : J'), UnitAt x (f (ι j') * (ρ' d : X.functionField)) →
      (ρ c : X.functionField) / (ρ' d : X.functionField) =
        f (ι j') * (ρ c : X.functionField) / (f (ι j') * (ρ' d : X.functionField)) := by
    intro x c d j' hu
    have hf : f (ι j') ≠ 0 := left_ne_zero_of_mul (unitAt_ne_zero hu)
    rw [mul_div_mul_left _ _ hf]
  have hτ : ∀ (x : X) c d, x ∈ M.B.U c → x ∈ M'.B.U d →
      RegAt x ((ρ c : X.functionField) / (ρ' d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨-, j', hj'⟩ := hreg' x d hd
    rw [hq x c d j' hj']
    exact regAt_div_unitAt ((hreg x c hc).1 (ι j')) hj'
  refine ⟨ρ, ρ', hρ, hρ', hτ, ?_⟩
  intro σ y c d hc hd
  have hc' := mem_ptsIn.1 hc
  have hd' := mem_ptsIn.1 hd
  set τ : X.functionField := (ρ c : X.functionField) / (ρ' d : X.functionField) with hτdef
  have hτr : RegAt (under y) τ := hτ _ c d hc' hd'

  have hval : ∀ j' : J', ratVal (f (ι j') * (ρ c : X.functionField)) y =
      ratVal τ y * ratVal (f (ι j') * (ρ' d : X.functionField)) y := by
    intro j'
    have e : f (ι j') * (ρ c : X.functionField) = τ * (f (ι j') * (ρ' d : X.functionField)) := by
      rw [hτdef]; field_simp
    rw [e, ratVal_mul hτr ((hreg' _ d hd').1 j')]
  set S : ℝ := ∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) with hS
  set S' : ℝ := ∑ j', ‖ratVal (f (ι j') * (ρ' d : X.functionField)) y‖ ^ 2 * Real.exp (2 * w' j') with hS'
  have e1 : (M.φ σ).φ c y = Real.log S := hφ σ y c hc
  have e2 : ((M'.shift (fun _ => Δ) fun _ => rfl).φ σ).φ d y = Real.log S' + 2 * Δ := by
    change (M'.φ σ).φ d y + 2 * Δ = _
    rw [hφ' σ y d hd]
  have hS'pos : 0 < S' := by
    obtain ⟨-, j₀, hj₀⟩ := hreg' _ d hd'
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ _, ?_⟩
    have : ratVal (f (ι j₀) * (ρ' d : X.functionField)) y ≠ 0 := ratVal_ne_zero hj₀
    have : 0 < ‖ratVal (f (ι j₀) * (ρ' d : X.functionField)) y‖ := norm_pos_iff.2 this
    positivity
  set t : ℝ := ‖ratVal τ y‖ with ht
  have hineq : t ^ 2 * Real.exp (2 * Δ) * S' ≤ S := by
    classical
    calc t ^ 2 * Real.exp (2 * Δ) * S'
        = ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * (w' j' + Δ)) := by
          rw [hS', Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [hval, norm_mul, ← ht, mul_add, Real.exp_add]; ring
      _ ≤ ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w (ι j')) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          gcongr
          exact hw j'
      _ = ∑ j ∈ Finset.univ.image ι, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) :=
          by rw [Finset.sum_image (fun a _ b _ h => hι h)]
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
  rw [e1, e2]
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact zero_le_one
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hineq
  have hE : Real.exp (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) ^ 2 = S' * Real.exp (2 * Δ) / S := by
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) = (Real.log S' + 2 * Δ) - Real.log S := by
      push_cast; ring
    rw [this, Real.exp_sub, Real.exp_add, Real.exp_log hS'pos, Real.exp_log hSpos]
  rw [← sq_le_one_iff₀ (by positivity), mul_pow, hE]
  rw [← mul_div_assoc, div_le_one hSpos]
  linarith [hineq]

end GlobalTheory.HSNef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ) (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' → (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  atlas_forward_decl GlobalTheory.HSNef.le_shift_of_isFS_sub
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

open MvPolynomial in

theorem mixed_diff_nonneg : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ), IsArFun ![A, B] D Φ → Le B A → ∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D → 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D) := by
  intro hC k _ X _ p D hX A B Φ hΦ hle x y hN
  classical
  haveI := hX.isLocallyNoetherian
  obtain ⟨s, hs, hs0⟩ := (GlobalTheory.T.hermLBLeBySmallSection_iff_exists_smallSection_difference k X p A B).1 hle
  have hg :=  (sec_ne_zero_iff s).1 hs0
  let L : Fin 2 → HermLB p := ![A, B]
  let F : Option (Fin 2) → HermLB p := fun o => o.elim (A.tens B.dual) L
  let E : Option (Fin 2) → Fin 2 → ℤ := fun o => o.elim ![1, -1] (fun i => Pi.single i 1)
  have hiso : ∀ j, (comb L (E j)).Isometric (F j) := by
    rintro (_ | i)
    · apply HermLB.icls_eq_iff.1
      simp [icls_comb, Fin.sum_univ_two, L, E, F, HermLB.icls_tens, HermLB.icls_dual, sub_eq_add_neg]
    · exact isometric_comb_single L i
  have hΦ' := ((hC.arIso k X p D hX).2 (Fin 2) L Φ hΦ).2.2 (Option (Fin 2)) F E hiso
  let n : Fin 2 → ℤ := ![(x : ℤ), (y : ℤ)]
  obtain ⟨h, hh⟩ := (hC.arExists k X p D hX).1 (comb L n)
  have hNiso : (comb L n).Isometric ((A.pow x).tens (B.pow y)) := by
    apply HermLB.icls_eq_iff.1
    simp [icls_comb, Fin.sum_univ_two, L, n, HermLB.icls_tens, HermLB.icls_pow]
  have hr := isRatSec_ratOfSec s hg
  obtain ⟨-, hmix⟩ := hC.arMix k X p D hX (Fin 2) (A.tens B.dual) L _ hΦ' n h hh (ratOfSec s hg) hr
  have hpoly : aeval (fun j => lin fun i => ((E j i : ℤ) : ℝ))
      (MvPolynomial.X none * rename some (lin fun i => ((n i : ℤ) : ℝ)) ^ D) =
      (MvPolynomial.X 0 - MvPolynomial.X 1) * (C (x : ℝ) * MvPolynomial.X 0 + C (y : ℝ) * MvPolynomial.X 1) ^ D := by
    simp [aeval_rename, lin, Fin.sum_univ_two, E, n, Function.comp_def, Pi.single_apply]
    left
    ring
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, hpoly] at hmix
  rw [hmix]
  have h1 : 0 ≤ ∑ᶠ z, (((A.tens B.dual).div hr).mult z : ℝ) * h z :=
    finsum_nonneg fun z => mul_nonneg (Int.cast_nonneg (mult_divOfSec_nonneg (hL := (A.tens B.dual).isLB) z))
      (hN.2 h (hNiso.isArithHeight hX hh) z)
  have h2 : ∀ σ, ((comb L n).φ σ).chernInt D (offSupp p σ ((A.tens B.dual).div hr))
      (logNorm ((A.tens B.dual).φ σ) (ratOfSec s hg)) ≤ 0 := by
    intro σ
    have hneg : ((comb L n).φ σ).chernPart D (-1) = 0 := by
      rw [hNiso.chernPart_eq]
      exact Weight.chernPart_neg_eq_zero (((A.pow x).tens (B.pow y)).cInf σ) (hN.1 σ)
    rw [Weight.chernInt, hneg, MeasureTheory.Measure.restrict_zero, MeasureTheory.integral_zero_measure, sub_zero]
    refine MeasureTheory.setIntegral_nonpos (isOpen_offSupp _).measurableSet fun z hz => ?_
    have hz' : z ∈ ptsIn p σ (Out.nonzeroLocus s) := by
      rw [← offSupp_divOfSec (hL := (A.tens B.dual).isLB)]
      exact hz
    rw [logNorm_ratOfSec _ hz']
    have h0 : 0 ≤ ((A.tens B.dual).φ σ).nsq (secVal p σ s) z := by
      unfold Weight.nsq
      positivity
    have := Real.log_nonpos h0 (hs σ z)
    linarith
  have h3 : (comb L n).archInt (A.tens B.dual) D hr ≤ 0 := by
    have := finsum_nonneg fun σ => neg_nonneg.2 (h2 σ)
    rw [finsum_neg_distrib] at this
    unfold HermLB.archInt
    linarith
  linarith

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedArithIntersection_nonneg_of_small_section_diff : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ), IsArFun ![A, B] D Φ → Le B A → ∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D → 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) * (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D) := by
  atlas_forward_decl GlobalTheory.HSNef.mixed_diff_nonneg
end

section
open Filter Topology

namespace GlobalTheory

open Polynomial in

theorem hasDerivAt_linearMap_eval_algebraMap {A : Type*} [CommRing A] [Algebra ℝ A]
    (Φ : A →ₗ[ℝ] ℝ) (R : Polynomial A) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => Φ (R.eval (algebraMap ℝ A t)))
      (Φ ((derivative R).eval (algebraMap ℝ A τ))) τ := by
  induction R using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, map_add, derivative_add]
    exact hp.add hq
  | monomial n a =>
    simp only [eval_monomial, derivative_monomial]
    have h1 : ∀ (m : ℕ) (t : ℝ), Φ (a * (algebraMap ℝ A t) ^ m) = t ^ m * Φ a := by
      intro m t
      rw [← map_pow, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]
    have h2 : Φ (a * (n : A) * (algebraMap ℝ A τ) ^ (n - 1)) = (n : ℝ) * τ ^ (n - 1) * Φ a := by
      have : a * (n : A) * (algebraMap ℝ A τ) ^ (n - 1) = n • (a * (algebraMap ℝ A τ) ^ (n - 1)) := by
        rw [nsmul_eq_mul]; ring
      rw [this, map_nsmul, h1, nsmul_eq_mul]; ring
    have h3 : (fun t : ℝ => Φ (a * (algebraMap ℝ A t) ^ n)) = fun t => t ^ n * Φ a := funext (h1 n)
    rw [h3, h2]
    exact (hasDerivAt_pow n τ).mul_const (Φ a)

theorem monotone_form_along_segment : ∀ (D : ℕ) (Φ : MvPolynomial (Fin 2) ℝ →ₗ[ℝ] ℝ),
    (∀ x y : ℕ, 0 ≤ Φ ((MvPolynomial.X 0 - MvPolynomial.X 1) *
      (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (y : ℝ) * MvPolynomial.X 1) ^ D)) →
    Φ (MvPolynomial.X 1 ^ (D + 1)) ≤ Φ (MvPolynomial.X 0 ^ (D + 1)) := by
  intro D Φ hyp
  have hΦC : ∀ (r : ℝ) (q : MvPolynomial (Fin 2) ℝ), Φ (MvPolynomial.C r * q) = r * Φ q := by
    intro r q; rw [MvPolynomial.C_mul', map_smul, smul_eq_mul]
  set a : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1 with ha
  set b : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0 - MvPolynomial.X 1 with hb
  set Q : Polynomial (MvPolynomial (Fin 2) ℝ) :=
    (Polynomial.C a + Polynomial.X * Polynomial.C b) ^ (D + 1) with hQ
  set R : Polynomial (MvPolynomial (Fin 2) ℝ) :=
    Polynomial.C b * (Polynomial.C a + Polynomial.X * Polynomial.C b) ^ D with hR
  set g : ℝ → ℝ := fun t => Φ (Q.eval (algebraMap ℝ _ t)) with hg
  set f : ℝ → ℝ := fun t => Φ (R.eval (algebraMap ℝ _ t)) with hf
  have hgd : ∀ τ, HasDerivAt g (((D : ℝ) + 1) * f τ) τ := by
    intro τ
    convert hasDerivAt_linearMap_eval_algebraMap Φ Q τ using 1
    simp [hf, hQ, hR, Polynomial.derivative_pow]
    have hc : ((D : MvPolynomial (Fin 2) ℝ) + 1) = MvPolynomial.C ((D : ℝ) + 1) := by simp
    rw [hc, mul_assoc, hΦC]
    congr 2
    ring
  have hfc : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro τ
    exact (hasDerivAt_linearMap_eval_algebraMap Φ R τ).continuousAt
  have hfrat : ∀ x n : ℕ, 0 < n → x ≤ n → 0 ≤ f ((x : ℝ) / n) := by
    intro x n hn hxn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have e : a + MvPolynomial.C ((x : ℝ) / n) * b = MvPolynomial.C (1 / (n : ℝ)) *
        (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (((n - x : ℕ)) : ℝ) * a) := by
      rw [Nat.cast_sub hxn]
      have h1 : MvPolynomial.C (1 / (n : ℝ)) * MvPolynomial.C (x : ℝ) =
          (MvPolynomial.C ((x : ℝ) / n) : MvPolynomial (Fin 2) ℝ) := by
        rw [← map_mul]; congr 1; ring
      have h2 : MvPolynomial.C (1 / (n : ℝ)) * MvPolynomial.C ((n : ℝ) - x) =
          (1 - MvPolynomial.C ((x : ℝ) / n) : MvPolynomial (Fin 2) ℝ) := by
        rw [← map_mul, ← map_one MvPolynomial.C, ← map_sub]; congr 1; field_simp
      rw [ha, hb]
      linear_combination (-(MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ)) * h1 - (MvPolynomial.X 1) * h2
    have hfx : f ((x : ℝ) / n) = (1 / (n : ℝ)) ^ D * Φ (b *
        (MvPolynomial.C (x : ℝ) * MvPolynomial.X 0 + MvPolynomial.C (((n - x : ℕ)) : ℝ) * a) ^ D) := by
      simp only [hf, hR, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, MvPolynomial.algebraMap_eq]
      rw [e, mul_pow, ← map_pow, mul_left_comm, hΦC]
    rw [hfx]
    exact mul_nonneg (pow_nonneg (by positivity) _) (hyp _ _)
  have hfpos : ∀ τ ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ f τ := by
    intro τ hτ
    by_contra hneg
    push_neg at hneg
    have hev : ∀ᶠ t in 𝓝 τ, f t < 0 := hfc.continuousAt.eventually (Iio_mem_nhds hneg)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (τ - ε) < τ from
      max_lt hτ.1 (by linarith))
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
    have hqε : τ - ε < q := lt_of_le_of_lt (le_max_right _ _) hq1
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    have hnum : 0 < q.num := Rat.num_pos.mpr hq0'
    have hx : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
      have := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    have hqdef : (q : ℝ) = (q.num.toNat : ℝ) / (q.den : ℝ) := by
      rw [hx]; exact_mod_cast (Rat.num_div_den q).symm
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hle : q.num.toNat ≤ q.den := by
      have h1 : (q : ℝ) < 1 := by linarith [hτ.2]
      rw [hqdef, div_lt_one hden] at h1
      exact_mod_cast h1.le
    have h0 := hfrat q.num.toNat q.den q.den_pos hle
    rw [← hqdef] at h0
    have hd : dist (q : ℝ) τ < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    linarith [hball hd]
  have hgdiff : ∀ τ, DifferentiableAt ℝ g τ := fun τ => (hgd τ).differentiableAt
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun τ _ => (hgdiff τ).continuousAt.continuousWithinAt
    · exact fun τ _ => (hgdiff τ).differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [(hgd τ).deriv]
      exact mul_nonneg (by positivity) (hfpos τ hτ)
  have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simpa [hg, hQ, ha, hb] using h01

end GlobalTheory
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem selfInter_mono : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), Le B A → (∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D) → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hC k _ Y _ p D hX A B α β hle hnef hα hβ
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p D hX).2 (Fin 2) ![A, B]).1
  have hpos := GlobalTheory.T.mixedArithIntersection_nonneg_of_small_section_diff hC k Y p D hX A B Φ hΦ hle
  have hmono := GlobalTheory.monotone_form_along_segment D Φ fun x y => hpos x y (hnef x y)
  have hd := ((hC.arIso k Y p D hX).2 (Fin 2) _ Φ hΦ).1
  have h0 : Φ (MvPolynomial.X 0 ^ (D + 1)) = α := HermLB.IsSelfInter.unique hX (hd 0) hα
  have h1 : Φ (MvPolynomial.X 1 ^ (D + 1)) = β := HermLB.IsSelfInter.unique hX (hd 1) hβ
  rw [← h0, ← h1]
  exact hmono

end GlobalTheory.HSNef
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfIntersection_mono_of_height_nef : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), Le B A → (∀ x y : ℕ, HtNef ((A.pow x).tens (B.pow y)) D) → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  atlas_forward_decl GlobalTheory.HSNef.selfInter_mono
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNefMono

theorem selfInter_mono_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), A.IsNef D → B.IsNef D → Le B A → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  intro hc hA hS k _ X _ p D hv A B α β hAn hBn hle hα hβ
  refine GlobalTheory.T.selfIntersection_mono_of_height_nef hc k X p D hv A B α β hle (fun x y => ?_) hα hβ
  exact GlobalTheory.T.arithKleiman_heightNef_of_isNef hc hA hS k X p D hv _
    (GlobalTheory.T.hermLineBundle_isNef_tens hc k X p D hv _ _ (GlobalTheory.NefPow.isNef_pow hc k X p D hv A x hAn)
      (GlobalTheory.NefPow.isNef_pow hc k X p D hv B y hBn))

end GlobalTheory.HSNefMono
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithSelfIntersection_mono_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (A B : HermLB p) (α β : ℝ), A.IsNef D → B.IsNef D → Le B A → A.IsSelfInter α → B.IsSelfInter β → β ≤ α := by
  atlas_forward_decl GlobalTheory.HSNefMono.selfInter_mono_of_isNef
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem Total.comp {X : Scheme.{0}} [IsIntegral X] {J J' : Type} {f : J → X.functionField} (h : Total f)
    (ι : J' → J) : Total (f ∘ ι) :=
  ⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩

theorem selfInter_nonneg_of_isFS (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) {k : Type} [CommRing k]
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {M : HermLB p} {J : Type} [Fintype J]
    {f : J → X.functionField} {w : J → ℝ} (hM : IsFS M f w) (hw : ∀ j, 0 ≤ w j) {μ : ℝ} (hμ : M.IsSelfInter μ) :
    0 ≤ μ := by
  have hnef := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M J f w hM hw
  have hht := (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX M hnef).2
  obtain ⟨h, hh, rfl⟩ := hμ
  exact hht h hh _

theorem levels_le_selfInter (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (x : Fin D → X.functionField) (Δ : ℝ)
    (hx : AlgebraicIndependent ℤ x) (hΔ : 0 < Δ) :
    ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ),
      LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) →
      M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ∑ j, (n j : ℝ) ≤ μ := by
  intro N
  induction N with
  | zero =>
    intro J _ e n M μ _ hn _ hM hμ
    have h0 : ∀ j, n j = 0 := fun j => Nat.le_zero.1 (hn j)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ
  | succ N ih =>
    intro J _ e n M μ he hn ht hM hμ
    classical
    have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
    by_cases hJ : ∀ j, n j = 0
    · simp only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      exact selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ
    push_neg at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    let J' := {j // 1 ≤ n j}
    let e' : J' → X.functionField := fun j => e j.1
    let n' : J' → ℕ := fun j => n j.1 - 1
    let ι : J' × Finset (Fin D) → J × Finset (Fin D) := fun c => (c.1.1, c.2)
    have hι : Function.Injective ι := by
      rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
      simp only [ι, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hbox : boxFam e' x = boxFam e x ∘ ι := rfl
    haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩
    have ht' : Total (boxFam e' x) := hbox ▸ ht.comp ι
    obtain ⟨M', hM'⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'
    obtain ⟨h', hh'⟩ := (hC.arExists k X p D hX).1 M'
    have hμ' : M'.IsSelfInter (h' (genericPoint X)) := ⟨h', hh', rfl⟩
    have he' : LinearIndependent ℤ e' := he.comp _ Subtype.val_injective
    have hn' : ∀ j, n' j ≤ N := fun j => by
      have := hn j.1
      simp only [n']
      omega
    have IH := ih J' e' n' M' _ he' hn' ht' hM' hμ'
    have hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ := fun c => by positivity
    have hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ := fun c => by
      have h1 := c.1.2
      simp only [n', ι]
      rw [Nat.cast_sub h1]
      push_cast
      linarith
    have hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M :=
      GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ)
        (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep
    have hnefM := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M _ _ _ hM hw0
    have hnefM' := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M' _ _ _ hM' hw0'
    have hnefS := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'
    have hsh := hC.arShift k X p D hX M' _ Δ hμ'
    have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh
    have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'
    have hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J' := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]
      have h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          have := j.2
          have : n j.1 = 0 := by omega
          simp [this]
      rw [h2, add_zero]
      have h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1 := fun j => by
        simp only [n']
        rw [Nat.cast_sub j.2]
        ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := by
      calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J' = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J') := by
            rw [hf]; ring
        _ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)
    rw [hsum, mul_add]
    linarith

theorem chain_moving_parts : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  intro hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ
  have key := levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ
  have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
  have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D := by
    calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J) := by
          rw [hf]; ring
      _ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)
  have hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, mul_add]
  linarith

end GlobalTheory.HSNef
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxFamily_movingParts_chain_bound : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  atlas_forward_decl GlobalTheory.HSNef.chain_moving_parts
end
