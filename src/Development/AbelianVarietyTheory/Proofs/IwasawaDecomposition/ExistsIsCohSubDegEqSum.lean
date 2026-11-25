module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB
open GlobalTheory.LB (resG_resG resG_self homOfLinear toMod fun_ext_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)

namespace GlobalTheory.TriangularFrames

variable {C : Scheme.{0}} {F : C.Modules} {J : Type} {T : J → C.Opens} {κ : J → Type}
  [∀ j, Fintype (κ j)] {v : ∀ j, κ j → Γ(F, T j)} {α : Type}

variable (v) in
abbrev spn (e : ∀ j, α ↪ κ j) (S : Finset α) (j : J) {V : C.Opens} (h : V ≤ T j) :
    Submodule Γ(C, V) Γ(F, V) :=
  Submodule.span Γ(C, V) ((fun a => resM F h (v j (e j a))) '' (S : Set α))

theorem mem_spn_iff (hv : ∀ j, IsFrame (v j)) {e : ∀ j, α ↪ κ j} {S : Finset α} {j : J}
    {V : C.Opens} (h : V ≤ T j) {x : Γ(F, V)} :
    x ∈ spn v e S j h ↔ ∀ b, (∀ a ∈ S, e j a ≠ b) → ((hv j).basis h).repr x b = 0 := by
  have hB : (fun a => resM F h (v j (e j a))) '' (S : Set α) =
      ((hv j).basis h) '' ((e j) '' (S : Set α)) := by
    rw [Set.image_image]
    simp only [IsFrame.basis_apply]
  rw [spn, hB, Module.Basis.mem_span_image]
  constructor
  · intro hs b hb
    by_contra hne
    obtain ⟨a, ha, rfl⟩ := hs (Finsupp.mem_support_iff.2 hne)
    exact hb a ha rfl
  · intro H b hb
    by_contra hn
    exact (Finsupp.mem_support_iff.1 hb) (H b fun a ha hab => hn ⟨a, ha, hab⟩)

def sub (hv : ∀ j, IsFrame (v j)) (e : ∀ j, α ↪ κ j) (S : Finset α) : Sub F where
  sec V :=
    { carrier := {x | ∀ j (W : C.Opens) (h₁ : W ≤ V) (h₂ : W ≤ T j), resM F h₁ x ∈ spn v e S j h₂}
      add_mem' := fun hs ht j W h₁ h₂ => by
        rw [map_add (f := resM F h₁)]
        exact add_mem (hs j W h₁ h₂) (ht j W h₁ h₂)
      zero_mem' := fun j W h₁ h₂ => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun a s hs j W h₁ h₂ => by
        rw [resM_smul]; exact Submodule.smul_mem _ _ (hs j W h₁ h₂) }
  res_mem h s hs j W h₁ h₂ := by rw [resM_resM]; exact hs j W _ h₂
  mem_of_local {V s} H j W h₁ h₂ := by
    refine (mem_spn_iff hv h₂).2 fun b hb => ?_
    choose U hU hx hs using fun x : W => H x (h₁ x.2)
    refine fun_ext_of_cover (fun x => W ⊓ U x) (fun _ => inf_le_left)
      (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx', hx _⟩) fun x => ?_
    have := (mem_spn_iff hv _).1 (hs x j (W ⊓ U x) inf_le_right (inf_le_left.trans h₂)) b hb
    rw [resM_resM] at this
    rw [map_zero, ← IsFrame.repr_resM, resM_resM, this]

variable [Fintype α] {rk : α → ℕ} {e : ∀ j, α ↪ κ j}

variable (v rk e) in
def IsTriangular (g : α → ∀ j j', Γ(C, T j ⊓ T j')) : Prop :=
  ∀ j j' a, ∃ cf : α → Γ(C, T j ⊓ T j'), cf a = g a j j' ∧ (∀ b, b ≠ a → rk a ≤ rk b → cf b = 0) ∧
    resM F inf_le_right (v j' (e j' a)) = ∑ b, cf b • resM F inf_le_left (v j (e j b))

variable {g : α → ∀ j j', Γ(C, T j ⊓ T j')}

def refine (M : LB C) (idx : J → M.ι) (hle : ∀ j, T j ≤ M.U (idx j)) : LB C where
  ι := J
  U := T
  g j j' := res (inf_le_inf (hle j) (hle j')) (M.g (idx j) (idx j'))

theorem isLB_refine (hT : ⨆ j, T j = ⊤) {M : LB C} (hM : M.IsLB) (idx : J → M.ι)
    (hle : ∀ j, T j ≤ M.U (idx j)) : (refine M idx hle).IsLB := {
  cover := hT
  g_self j := by
    have hg : ((refine M idx hle).g j j).val =
        resG C (inf_le_inf (hle j) (hle j)) (M.g (idx j) (idx j)).val :=
      GlobalTheory.LB.val_res _ _
    have h0 := hM.g_self (idx j)
    rw [Units.ext_iff, GlobalTheory.LB.val_res, Units.val_one] at h0
    apply Units.ext
    rw [GlobalTheory.LB.val_res, hg]
    have h1 := congrArg (resG C (hle j)) h0
    rw [resG_resG, map_one] at h1
    exact (resG_resG _ _ _).trans h1
  cocycle i j k := by
    have hg : ∀ i j : J, ((refine M idx hle).g i j).val =
        resG C (inf_le_inf (hle i) (hle j)) (M.g (idx i) (idx j)).val :=
      fun i j => GlobalTheory.LB.val_res _ _
    have h0 := hM.cocycle (idx i) (idx j) (idx k)
    rw [Units.ext_iff, Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res] at h0
    apply Units.ext
    rw [Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, hg i j, hg j k, hg i k]
    have h1 := congrArg (resG C (inf_le_inf (inf_le_inf (hle i) (hle j)) (hle k))) h0
    rw [map_mul, resG_resG, resG_resG, resG_resG] at h1
    exact (congrArg₂ (· * ·) (resG_resG _ _ _) (resG_resG _ _ _)).trans
      (h1.trans (resG_resG _ _ _).symm) }

private theorem res_transition_mul_comm_square {M : LB C} (hM : M.IsLB) (i i' k k' : M.ι) {W : C.Opens}
    (h₁ : W ≤ M.U i) (h₂ : W ≤ M.U i') (h₃ : W ≤ M.U k) (h₄ : W ≤ M.U k') :
    resG C (le_inf h₁ h₃) (M.g i k).val * resG C (le_inf h₃ h₄) (M.g k k').val =
      resG C (le_inf h₁ h₂) (M.g i i').val * resG C (le_inf h₂ h₄) (M.g i' k').val := by
  have c1 := hM.cocycle i k k'
  have c2 := hM.cocycle i i' k'
  rw [Units.ext_iff, Units.val_mul, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, GlobalTheory.LB.val_res] at c1 c2
  have d1 := congrArg (resG C (le_inf (le_inf h₁ h₃) h₄)) c1
  have d2 := congrArg (resG C (le_inf (le_inf h₁ h₂) h₄)) c2
  rw [map_mul, resG_resG, resG_resG, resG_resG] at d1 d2
  exact d1.trans d2.symm

theorem lbIso_refine {M : LB C} (hM : M.IsLB) (idx : J → M.ι)
    (hle : ∀ j, T j ≤ M.U (idx j)) : LBIso (refine M idx hle) M := by
  have grp : ∀ {R : Type} [CommRing R] (X A B Y : Rˣ), X * B = A * Y → X = A * B⁻¹ * Y := by
    intro R _ X A B Y h
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq, h]
  have hv2 : ∀ {U V W : C.Opens} (h : V ≤ U) (h' : W ≤ V) (u : Γ(C, U)ˣ),
      ((res h' (res h u) : Γ(C, W)ˣ) : Γ(C, W)) = resG C (h'.trans h) (u : Γ(C, U)) := by
    intro U V W h h' u
    rw [GlobalTheory.LB.val_res, GlobalTheory.LB.val_res, resG_resG]
  refine ⟨⟨fun p => res (show M.U p.1 ⊓ T p.2 ≤ M.U p.1 ⊓ M.U (idx p.2) from
    inf_le_inf le_rfl (hle p.2)) (M.g p.1 (idx p.2))⟩, ?_⟩
  rintro ⟨i, j⟩ ⟨i', j'⟩
  apply grp
  apply Units.ext
  have key := res_transition_mul_comm_square hM i i' (idx j) (idx j') (W := (M.U i ⊓ T j) ⊓ (M.U i' ⊓ T j'))
    (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    ((inf_le_left.trans inf_le_right).trans (hle j)) ((inf_le_right.trans inf_le_right).trans (hle j'))
  exact ((Units.val_mul _ _).trans ((congrArg₂ (· * ·) (hv2 _ _ _) (hv2 _ _ _)).trans
    (key.trans (congrArg₂ (· * ·) (GlobalTheory.LB.val_res _ _).symm (hv2 _ _ _).symm)))).trans
    (Units.val_mul _ _).symm

end GlobalTheory.TriangularFrames
