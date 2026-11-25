module

public import GroundTheory.AutomorphicForms.TensorProductTheorem.Operators
public import GroundTheory.AutomorphicForms.TensorProductTheorem.MatrixCoeff
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set

variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]

section Window

variable (ρ : Representation ℂ M V)

structure IsWinProj (e : End ℂ V) : Prop where
  idem : ∀ v, e (e v) = e v
  mem : ∀ Y : Subrepresentation ρ, ∀ y ∈ Y.toSubmodule, e y ∈ Y.toSubmodule

variable {ρ} {e : End ℂ V}

theorem IsWinProj.apply_of_mem (he : IsWinProj ρ e) {v : V} (hv : v ∈ LinearMap.range e) :
    e v = v := by
  obtain ⟨w, rfl⟩ := hv
  exact he.idem w


variable (ρ e) in
def winOp (m : M) : End ℂ (LinearMap.range e) :=
  LinearMap.codRestrict (LinearMap.range e) (e ∘ₗ ρ m ∘ₗ (LinearMap.range e).subtype)
    fun _ => ⟨_, rfl⟩


variable (ρ e) in
def winOps : Set (End ℂ (LinearMap.range e)) := range (winOp ρ e)

theorem isSimpleUnder_winOps [ρ.IsIrreducible] (he : IsWinProj ρ e)
    (hne : LinearMap.range e ≠ ⊥) : IsSimpleUnder (winOps ρ e) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hx0' : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  rw [eq_top_iff]
  intro y _
  have hle : Submodule.span ℂ (range fun m => ρ m (x : V)) ≤
      (p.map (LinearMap.range e).subtype).comap e := by
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact ⟨winOp ρ e m x, hp _ ⟨m, rfl⟩ x hx, rfl⟩
  have := hle (mem_span_orbit (ρ := ρ) hx0' (y : V))
  obtain ⟨z, hz, hzy⟩ := this
  have : z = y := Subtype.ext (hzy.trans (he.apply_of_mem y.2))
  rwa [← this]

theorem exists_eq_smul_of_commute [ρ.IsIrreducible] (he : IsWinProj ρ e)
    (hne : LinearMap.range e ≠ ⊥) [FiniteDimensional ℂ (LinearMap.range e)] {T : End ℂ V}
    (hTρ : ∀ m, T * ρ m = ρ m * T) (hTe : T * e = e * T) : ∃ c : ℂ, T = c • 1 := by
  have : Nontrivial (LinearMap.range e) := Submodule.nontrivial_iff_ne_bot.2 hne
  let T' : End ℂ (LinearMap.range e) := LinearMap.codRestrict _ (T ∘ₗ (LinearMap.range e).subtype)
    fun x => by
      obtain ⟨w, hw⟩ := x.2
      refine ⟨T w, ?_⟩
      rw [← Module.End.mul_apply, ← hTe, Module.End.mul_apply, hw]
      rfl
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T'
  obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩

  let Y : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (T - c • 1)
      apply_mem_toSubmodule := fun m v hv => by
        rw [LinearMap.mem_ker] at hv ⊢
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, ← Module.End.mul_apply,
          hTρ, Module.End.mul_apply, ← map_smul, ← map_sub]
        rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv
        rw [hv, map_zero] }
  have hxY : (x : V) ∈ Y.toSubmodule := by
    have := hx.apply_eq_smul
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_eq_zero]
    exact congrArg Subtype.val this
  rcases IsSimpleOrder.eq_bot_or_eq_top Y with h | h
  · exfalso
    rw [h] at hxY
    exact hx.2 (Subtype.ext hxY)
  · ext v
    have : v ∈ Y.toSubmodule := by rw [h]; trivial
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
    exact this

end Window

section Quotient

variable (ρ : Representation ℂ M V)

def mGenSubrep (N : Submodule ℂ V) : Subrepresentation ρ where
  toSubmodule := ⨆ g : M, N.map (ρ g)
  apply_mem_toSubmodule g x hx := by
    have : (⨆ h : M, N.map (ρ h)) ≤ (⨆ h : M, N.map (ρ h)).comap (ρ g) := by
      refine iSup_le fun h => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact Submodule.mem_iSup_of_mem (g * h) ⟨n, hn, rfl⟩
    exact this hx

theorem le_mGenSubrep (N : Submodule ℂ V) : N ≤ (mGenSubrep ρ N).toSubmodule := fun n hn =>
  Submodule.mem_iSup_of_mem 1 ⟨n, hn, by simp⟩

theorem mGenSubrep_le {N : Submodule ℂ V} {X : Subrepresentation ρ} (h : N ≤ X.toSubmodule) :
    (mGenSubrep ρ N).toSubmodule ≤ X.toSubmodule :=
  iSup_le fun g => by
    rintro _ ⟨n, hn, rfl⟩
    exact X.apply_mem_toSubmodule g (h hn)

variable (e : End ℂ V) (N : Submodule ℂ V)

def mGenKernel : Submodule ℂ (mGenSubrep ρ N).toSubmodule where
  carrier := {u | ∀ g, e (ρ g u) = 0}
  add_mem' {a b} ha hb g := by
    simp only [Submodule.coe_add, map_add (f := _), ha g, hb g, add_zero]
  zero_mem' g := by simp
  smul_mem' c a ha g := by
    simp only [Submodule.coe_smul, map_smul, ha g, smul_zero]

theorem mGenKernel_le_comap (g : M) :
    mGenKernel ρ e N ≤ (mGenKernel ρ e N).comap ((mGenSubrep ρ N).toRepresentation g) := by
  intro u hu h
  show e (ρ h (ρ g u)) = 0
  rw [show ρ h (ρ g u) = ρ (h * g) u by rw [map_mul]; rfl]
  exact hu (h * g)

def mGenQuotRep : Representation ℂ M ((mGenSubrep ρ N).toSubmodule ⧸ mGenKernel ρ e N) :=
  (mGenSubrep ρ N).toRepresentation.quotient _ (mGenKernel_le_comap ρ e N)

def mGenQuotMk : N →ₗ[ℂ] (mGenSubrep ρ N).toSubmodule ⧸ mGenKernel ρ e N :=
  (mGenKernel ρ e N).mkQ ∘ₗ Submodule.inclusion (le_mGenSubrep ρ N)

theorem mGenQuotRep_mk (g : M) (u : (mGenSubrep ρ N).toSubmodule) :
    mGenQuotRep ρ e N g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((mGenSubrep ρ N).toRepresentation g u) :=
  rfl

variable {ρ e N}

theorem mGenQuotMk_injective (he : IsWinProj ρ e) (hNe : N ≤ LinearMap.range e) :
    Function.Injective (mGenQuotMk ρ e N) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro n hn
  rw [LinearMap.mem_ker, mGenQuotMk, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hn
  have := hn 1
  rw [map_one, Module.End.one_apply] at this
  simp only [Submodule.coe_inclusion] at this
  rw [Submodule.mem_bot]
  exact Subtype.ext ((he.apply_of_mem (hNe n.2)).symm.trans this)

theorem isIrreducible_mGenQuotRep (he : IsWinProj ρ e) (hNe : N ≤ LinearMap.range e)
    (hNst : ∀ g, ∀ n ∈ N, e (ρ g n) ∈ N) (hN0 : N ≠ ⊥)
    (hNmin : ∀ N₁ : Submodule ℂ V, N₁ ≤ N → N₁ ≠ ⊥ → (∀ g, ∀ n ∈ N₁, e (ρ g n) ∈ N₁) → N₁ = N) :
    (mGenQuotRep ρ e N).IsIrreducible := by
  set U := mGenSubrep ρ N
  set U₀ := mGenKernel ρ e N
  set π := mGenQuotRep ρ e N
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hmk0 : mGenQuotMk ρ e N ⟨n, hn⟩ ≠ 0 := by
    intro h
    have := mGenQuotMk_injective he hNe (a₁ := ⟨n, hn⟩) (a₂ := 0) (by rw [h, map_zero])
    exact hn0 (congrArg Subtype.val this)
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h0
    have : mGenQuotMk ρ e N ⟨n, hn⟩ ∈ (⊤ : Subrepresentation π).toSubmodule := Submodule.mem_top
    rw [← h0] at this
    exact hmk0 this

  have hUN : ∀ u ∈ U.toSubmodule, e u ∈ N := by
    intro u hu
    have : U.toSubmodule ≤ N.comap e := by
      refine iSup_le fun g => ?_
      rintro _ ⟨m, hm, rfl⟩
      exact hNst g m hm
    exact this hu
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }
  let Y : Subrepresentation ρ :=
    { toSubmodule := (X.toSubmodule.comap U₀.mkQ).map U.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨u, hu, rfl⟩
        refine ⟨U.toRepresentation g u, ?_, rfl⟩
        have hu' : U₀.mkQ u ∈ X.toSubmodule := hu
        have := X.apply_mem_toSubmodule g hu'
        exact this }
  have hYU : ∀ {x : V}, x ∈ Y.toSubmodule → x ∈ U.toSubmodule := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2
  have hst : ∀ g, ∀ m ∈ Y.toSubmodule ⊓ N, e (ρ g m) ∈ Y.toSubmodule ⊓ N := by
    rintro g m ⟨hmY, hmN⟩
    exact ⟨he.mem Y _ (Y.apply_mem_toSubmodule g hmY), hNst g m hmN⟩
  by_cases hYN : Y.toSubmodule ⊓ N = ⊥
  · left
    ext q
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show Submodule.Quotient.mk u = (0 : U.toSubmodule ⧸ U₀)
      rw [Submodule.Quotient.mk_eq_zero]
      intro g
      have hY : (U.toRepresentation g u : V) ∈ Y.toSubmodule :=
        ⟨U.toRepresentation g u, X.apply_mem_toSubmodule g hq, rfl⟩
      have h1 := he.mem Y _ hY
      have h2 : e (ρ g u) ∈ N := hUN _ (hYU hY)
      have h3 : e (ρ g u) ∈ Y.toSubmodule ⊓ N := ⟨h1, h2⟩
      rw [hYN, Submodule.mem_bot] at h3
      exact h3
    · have : q = 0 := hq
      rw [this]
      exact X.toSubmodule.zero_mem
  · right
    have heq := hNmin _ inf_le_right hYN hst
    have hNY : N ≤ Y.toSubmodule := heq ▸ inf_le_left
    have hUY := mGenSubrep_le ρ hNY
    ext q
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u', hu', hu'u⟩ := hUY u.2
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'


variable (ρ e N) in
def mGenQuotForm (l : Dual ℂ V) :
    Dual ℂ ((mGenSubrep ρ N).toSubmodule ⧸ mGenKernel ρ e N) :=
  (mGenKernel ρ e N).liftQ (l ∘ₗ e ∘ₗ (mGenSubrep ρ N).toSubmodule.subtype) fun u hu => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
    have := hu 1
    rw [map_one, Module.End.one_apply] at this
    simp only [Submodule.subtype_apply, this, map_zero]

theorem mGenQuotForm_apply (l : Dual ℂ V) (g : M) (n : N) :
    mGenQuotForm ρ e N l (mGenQuotRep ρ e N g (mGenQuotMk ρ e N n)) = l (e (ρ g n)) :=
  rfl

end Quotient

end RestrictedTensor

end GroundTheory.Automorphic
