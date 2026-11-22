module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open MeasureTheory
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.ProjVar.Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ Δ' : Y.Dv} {g g' : Y.Fnˣ}
  {y : Y.pts σ} {f f' : Y.FnC σ}

instance nonempty_pts : Nonempty (Y.pts σ) := ⟨(exists_mem_ptsIn (U := ⊤) trivial).choose⟩

variable (σ) in
def eqnSet (Δ : Y.Dv) (g : Y.Fnˣ) : Set (Y.pts σ) := {y | Δ.IsEqn (base y) g}

theorem isOpen_eqnSet (Δ : Y.Dv) (g : Y.Fnˣ) : IsOpen (eqnSet σ Δ g) :=
  isOpen_iff_forall_mem_open.2 fun _ hy =>
    have ⟨U, hU, h⟩ := IsEqn.exists_nhds hy
    ⟨ptsIn Y.str σ U, fun _ hz => h _ (mem_ptsIn_iff.1 hz), isOpen_ptsIn U, mem_ptsIn_iff.2 hU⟩

def eqn (Δ : Y.Dv) (y : Y.pts σ) : Y.Fnˣ := (Δ.exists_isEqn (base y)).choose

theorem mem_eqnSet (Δ : Y.Dv) (y : Y.pts σ) : y ∈ eqnSet σ Δ (eqn Δ y) :=
  (Δ.exists_isEqn (base y)).choose_spec

def tv (g g' : Y.Fnˣ) (y : Y.pts σ) : ℂ := val y (Y.cx σ (g' / g))

theorem tv_ne_zero (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') : tv g g' y ≠ 0 :=
  val_cx_ne_zero_iff.2 ((IsEqn.iff_unitAt h).1 h')

theorem tv_mul_mul {g₁ g₁' : Y.Fnˣ} (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') :
    tv (g * g₁) (g' * g₁') y = tv g g' y * tv g₁ g₁' y := by
  rw [tv, Units.val_mul, Units.val_mul, mul_div_mul_comm, map_mul, val_unit_mul (tv_ne_zero h h')]
  rfl

theorem tv_mul {g'' : Y.Fnˣ} (h : y ∈ eqnSet σ Δ g) (h' : y ∈ eqnSet σ Δ g') :
    tv g g' y * tv g' g'' y = tv g g'' y := by
  rw [← tv_mul_mul h h', tv, tv, Units.val_mul, Units.val_mul, mul_comm (g : Y.Fn),
    mul_div_mul_left _ _ g'.ne_zero]

theorem holoOn_tv (Δ : Y.Dv) (g g' : Y.Fnˣ) :
    (Y.an σ).HoloOn (eqnSet σ Δ g ∩ eqnSet σ Δ g') (tv g g') :=
  (holoOn_val _).mono fun _ hz => regC_of_val_ne_zero (tv_ne_zero hz.1 hz.2)

variable (Y σ) in
structure Met (Δ : Y.Dv) where

  h : Y.Fnˣ → Y.pts σ → ℝ

  nonneg : ∀ g y, 0 ≤ h g y

  trans : ∀ g g' y, y ∈ eqnSet σ Δ g → y ∈ eqnSet σ Δ g' → h g y = ‖tv g g' y‖ ^ 2 * h g' y

namespace Met

variable (m : Met Y σ Δ) (m' : Met Y σ Δ')

def wt (g : Y.Fnˣ) (y : Y.pts σ) : ℝ := -Real.log (m.h g y)

def posSet : Set (Y.pts σ) := {y | 0 < m.h (eqn Δ y) y}

variable {m} in
theorem mem_posSet_iff (hg : y ∈ eqnSet σ Δ g) : y ∈ m.posSet ↔ 0 < m.h g y := by
  have := tv_ne_zero (mem_eqnSet Δ y) hg
  rw [posSet, mem_setOf_eq, m.trans _ g y (mem_eqnSet Δ y) hg, mul_pos_iff_of_pos_left (by positivity)]

variable {m} in
theorem wt_trans (hy : y ∈ m.posSet) (hg : y ∈ eqnSet σ Δ g) (hg' : y ∈ eqnSet σ Δ g') :
    m.wt g' y = m.wt g y + Real.log (‖tv g g' y‖ ^ 2) := by
  have := tv_ne_zero hg hg'
  rw [wt, wt, m.trans g g' y hg hg',
    Real.log_mul (by positivity) ((mem_posSet_iff hg').1 hy).ne']
  ring

section Cover

variable {ι : Type} (S : ι → Set (Y.pts σ)) (e : ι → Y.Fnˣ) (sub : ∀ i, S i ⊆ eqnSet σ Δ (e i))
  (cover : ∀ y, ∃ i, y ∈ S i) (w : ι → Y.pts σ → ℝ) (hw : ∀ i y, 0 ≤ w i y)
  (compat : ∀ i j y, y ∈ S i → y ∈ S j → w i y = ‖tv (e i) (e j) y‖ ^ 2 * w j y)

def ofCover : Met Y σ Δ where
  h g y := ‖tv g (e (cover y).choose) y‖ ^ 2 * w (cover y).choose y
  nonneg _ _ := mul_nonneg (sq_nonneg _) (hw _ _)
  trans g g' y hg hg' := by rw [← mul_assoc, ← mul_pow, ← norm_mul, tv_mul hg hg']

include sub compat in
theorem ofCover_h {i : ι} (hi : y ∈ S i) : (ofCover (Δ := Δ) S e cover w hw).h (e i) y = w i y :=
  (compat i _ y hi (cover y).choose_spec).symm

end Cover

variable {m} in
def SmoothOn (m : Met Y σ Δ) (S : Set (Y.pts σ)) : Prop :=
  S ⊆ m.posSet ∧ ∀ g, (Y.an σ).SmoothOn (S ∩ eqnSet σ Δ g) (m.wt g)

variable {m} in
theorem smoothOn_of_cover {S : Set (Y.pts σ)} (hS : IsOpen S) (h0 : S ⊆ m.posSet) {ι : Type}
    {T : ι → Set (Y.pts σ)} (hT : ∀ i, IsOpen (T i)) (hc : ∀ y, ∃ i, y ∈ T i) {e : ι → Y.Fnˣ}
    (sub : ∀ i, T i ⊆ eqnSet σ Δ (e i)) (h : ∀ i, (Y.an σ).SmoothOn (S ∩ T i) (m.wt (e i))) :
    m.SmoothOn S := ⟨h0, fun g => AnRead.smoothOn_of_cover hT (fun y _ => hc y) fun i =>
  AnRead.SmoothOn.congr (f := fun y => m.wt (e i) y + Real.log (‖tv (e i) g y‖ ^ 2))
    (fun c => ((h i).mono (fun _ (hz : _ ∈ (S ∩ eqnSet σ Δ g) ∩ T i) => ⟨hz.1.1, hz.2⟩) c).add
      (((holoOn_tv Δ (e i) g).mono fun _ (hz : _ ∈ (S ∩ eqnSet σ Δ g) ∩ T i) => ⟨sub i hz.2, hz.1.2⟩).smoothOn_log
        ((hS.inter (isOpen_eqnSet Δ g)).inter (hT i))
        (fun _ hz => tv_ne_zero (sub i hz.2) hz.1.2) c))
    fun _ hz => wt_trans (h0 hz.1.1) (sub i hz.2) hz.1.2⟩

end Met

open Met

section OfWeight

variable {L : LB Y.X} {r : L.ι → Y.Fnˣ}

theorem tv_eq_gv (hp : Presents Δ L r) {i j : L.ι} (hi : y ∈ ptsIn Y.str σ (L.U i))
    (hj : y ∈ ptsIn Y.str σ (L.U j)) : tv (r j) (r i) y = gv Y.str σ L i j y := by
  have h : base y ∈ L.U i ⊓ L.U j := ⟨mem_ptsIn_iff.1 hi, mem_ptsIn_iff.1 hj⟩
  rw [tv, hp.isRatSec i j (gen_mem h), mul_div_cancel_right₀ _ (r j).ne_zero, val_cx_fnOf h]
  rfl

theorem ptsIn_subset_eqnSet (hp : Presents Δ L r) (i : L.ι) :
    ptsIn Y.str σ (L.U i) ⊆ eqnSet σ Δ (r i) := fun _ h => hp.isEqn i _ (mem_ptsIn_iff.1 h)

variable (Y σ Δ L r) in
def ofWeight (_ : Presents Δ L r) (φ : Weight Y.str σ L) : Met Y σ Δ :=
  ofCover (fun i => ptsIn Y.str σ (L.U i)) r (fun y => ⟨_, mem_pick φ.isLB y⟩)
    (fun i y => Real.exp (-φ.φ i y)) fun _ _ => (Real.exp_pos _).le

theorem ofWeight_h (hp : Presents Δ L r) (φ : Weight Y.str σ L) {i : L.ι}
    (hi : y ∈ ptsIn Y.str σ (L.U i)) :
    (ofWeight Y σ Δ L r hp φ).h (r i) y = Real.exp (-φ.φ i y) :=
  ofCover_h _ _ (ptsIn_subset_eqnSet hp) _ _ _ (fun i j y hi hj => by
    have := normSq_mul_exp (gv_ne_zero hj hi) 1 (φ.φ i y)
    rw [φ.trans j i y hj hi, sub_add_cancel, mul_one, norm_one, one_pow, one_mul] at this
    rw [tv_eq_gv hp hj hi, φ.trans j i y hj hi, this]) hi

def Met.toWeight (m : Met Y σ Δ) (hm : m.posSet = univ) (hp : Presents Δ L r) :
    Weight Y.str σ L where
  isLB := hp.isLB
  φ i := m.wt (r i)
  trans i j y hi hj := by
    rw [wt_trans (hm ▸ mem_univ y) (ptsIn_subset_eqnSet hp j hj) (ptsIn_subset_eqnSet hp i hi),
      tv_eq_gv hp hi hj, add_sub_cancel_right]

end OfWeight

variable {m : Met Y σ Δ} {m' : Met Y σ Δ'}

variable (Y σ Δ) in
def mSmooth (m : Met Y σ Δ) : Prop := m.SmoothOn univ

theorem mSmooth.posSet_eq (h : mSmooth Y σ Δ m) : m.posSet = univ := univ_subset_iff.1 h.1

theorem mSmooth_ofWeight_iff {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hp : Presents Δ L r)
    (φ : Weight Y.str σ L) : mSmooth Y σ Δ (ofWeight Y σ Δ L r hp φ) ↔ φ.IsSmooth (Y.an σ) := by
  have e (i) (y) (hi : y ∈ ptsIn Y.str σ (L.U i)) : (ofWeight Y σ Δ L r hp φ).wt (r i) y = φ.φ i y := by
    rw [wt, ofWeight_h hp φ hi, Real.log_exp, neg_neg]
  refine ⟨fun h i => ((h.2 (r i)).mono fun y hy => ⟨trivial, ptsIn_subset_eqnSet hp i hy⟩).congr
    fun y hy => (e i y hy).symm, fun h => smoothOn_of_cover isOpen_univ (fun y _ => ?_)
      (fun i => isOpen_ptsIn (L.U i)) (fun y => ⟨_, mem_pick φ.isLB y⟩) (ptsIn_subset_eqnSet hp)
      fun i => ((h i).mono inter_subset_right).congr fun y hy => e i y hy.2⟩
  have hi := mem_pick φ.isLB y
  rw [mem_posSet_iff (ptsIn_subset_eqnSet hp _ hi), ofWeight_h hp φ hi]
  exact Real.exp_pos _

theorem mSmooth.isSmooth_toWeight (h : mSmooth Y σ Δ m) {L : LB Y.X} {r : L.ι → Y.Fnˣ}
    (hp : Presents Δ L r) : (m.toWeight h.posSet_eq hp).IsSmooth (Y.an σ) := fun i =>
  (h.2 (r i)).mono fun _ hy => ⟨trivial, ptsIn_subset_eqnSet hp i hy⟩

variable {s : Fin Y.dim → Y.FnC σ} {c c' : AlgChart Y.str σ Y.dim}

end GlobalTheory.ProjVar.Var

namespace GlobalTheory.ProjVar

open Var

variable (F : Type) [Field F] (σ : F →+* ℂ) (n : ℕ)

end GlobalTheory.ProjVar
