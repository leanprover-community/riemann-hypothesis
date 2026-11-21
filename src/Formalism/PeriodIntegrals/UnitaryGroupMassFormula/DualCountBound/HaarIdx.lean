import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGDict

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

def PowQ : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F], IsNonarchimedeanLocalField F →
    ∀ (N : Type) [AddCommGroup N] [Module 𝒪[F] N], Finite N → ∃ i : ℕ, Nat.card N = qF F ^ i

def FinBB (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          Finite (BB H t)

def BoundBB (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          Finite (BB H t) → (be H t : ℝ) ≤ P.Hp

end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Mod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def toO (M : Model F E) : 𝒪[F] →+* M.L.O where
  toFun x := ⟨algebraMap F E (x : F), (M.L.O_def _).2 (isIntegral_algebraMap (x := x))⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[simp] lemma toO_coe (M : Model F E) (x : 𝒪[F]) : ((toO M x : M.L.O) : E) = algebraMap F E (x : F) := rfl

variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

def bbMod (t : Term V M r) : Module 𝒪[F] (BB H t) := Module.compHom _ (toO M)

def iSub (t : Term V M r) : @Submodule 𝒪[F] (BB H t) _ _ (bbMod H t) :=
  letI := bbMod H t
  { carrier := Iset H t
    zero_mem' := ⟨0, 0, 0, 0, by simp, Submodule.zero_mem _, Submodule.zero_mem _, Submodule.zero_mem _,
      by simpa using t.abelian₂.zero_mem, by simpa using t.abelian₂.zero_mem, by simp⟩
    add_mem' := by
      rintro _ _ ⟨y₁, w₁, l₁, l₁', rfl, hw₁, hl₁, hl₁', h₁, h₁', e₁⟩ ⟨y₂, w₂, l₂, l₂', rfl, hw₂, hl₂, hl₂', h₂, h₂', e₂⟩
      refine ⟨y₁ + y₂, w₁ + w₂, l₁ + l₂, l₁' + l₂', by simp, Submodule.add_mem _ hw₁ hw₂,
        Submodule.add_mem _ hl₁ hl₂, Submodule.add_mem _ hl₁' hl₂', ?_, ?_, ?_⟩
      · have := t.abelian₂.add_mem h₁ h₂
        convert this using 1; abel
      · have := t.abelian₂.add_mem h₁' h₂'
        convert this using 1; abel
      · simp only [Submodule.coe_add, smul_add, e₁, e₂]; abel
    smul_mem' := by
      rintro a _ ⟨y, w, l, l', rfl, hw, hl, hl', h, h', e⟩
      refine ⟨toO M a • y, algebraMap F E (a : F) • w, algebraMap F E (a : F) • l,
        algebraMap F E (a : F) • l', rfl, Submodule.smul_mem _ _ hw, Submodule.smul_mem _ _ hl,
        Submodule.smul_mem _ _ hl', ?_, ?_, ?_⟩
      · have := t.abelian₂.smul_mem (toO M a) h
        rw [Submonoid.smul_def, toO_coe, smul_add] at this
        exact this
      · have := t.abelian₂.smul_mem (toO M a) h'
        rw [Submonoid.smul_def, toO_coe, smul_add] at this
        exact this
      · rw [Submodule.coe_smul, Submonoid.smul_def, toO_coe, smul_comm, e, smul_sub] }

end Mod

end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict

section Q

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

abbrev satQ (Λ : Submodule M.L.O V) {ι : Type} (v : ι → V) : Submodule M.L.O V :=
  Λ ⊓ (Submodule.span E (Set.range v)).restrictScalars M.L.O

abbrev QQ (Λ : Submodule M.L.O V) {ι : Type} (v : ι → V) : Type :=
  ↥(satQ Λ v) ⧸ (Submodule.span M.L.O (Set.range v)).comap (satQ Λ v).subtype

abbrev CokQ {ι : Type} [Fintype ι] (G : Matrix ι ι M.L.O) : Type :=
  (ι → M.L.O) ⧸ LinearMap.range G.mulVecLin

end Q

def FamLam (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          ∀ j, H.MMfam t j ∈ t.abelian₂

def FamIndep (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          LinearIndependent E (H.MMfam t)

def LamInt (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O

def GramEq (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          (H.gram (H.MMfam t)).det = (H.gram P.MMgen).det

def MinorInt (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P → ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
          ∀ l, P.Dm l ∈ M.L.O

def DualCount : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (ι : Type) [Fintype ι] [DecidableEq ι]
      (v : ι → V) (Λ : Submodule M.L.O V), LinearIndependent E v → (∀ j, v j ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) → IsUnit (H.gram v).det →
      ∀ G : Matrix ι ι M.L.O, (∀ a b, (G a b : E) = H.gram v a b) → Finite (CokQ G) →
        Finite (QQ Λ v) ∧ Nat.card (QQ Λ v) ^ 2 ≤ Nat.card (CokQ G)

def MatIdx : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι M.L.O) (δ : 𝒪[F]), δ ≠ 0 →
      ((G.det : M.L.O) : E) = algebraMap F E (δ : F) →
      Finite (CokQ G) ∧ Nat.card (CokQ G) ≤ Nat.card (M.L.O ⧸ Ideal.span {toO M δ})

def HaarIdx : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ δ : 𝒪[F], δ ≠ 0 → M.modK (algebraMap F E (δ : F)) * (Nat.card (M.L.O ⧸ Ideal.span {toO M δ}) : ℝ) ≤ 1

def ModLe : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ x ∈ M.R, M.modK x ≤ 1

def ModZero : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    M.modK 0 = 0

def InR : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ y : 𝒪[F], algebraMap F E (y : F) ∈ M.R

def FixO : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ x ∈ M.L.O, M.L.cj x = x → ∃ y : 𝒪[F], algebraMap F E (y : F) = x

end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict



end PI.NGStepBBW
end
end

section
noncomputable section

open ValuativeRel Topology

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc


end PI.NGStepBBW
end
end

section
noncomputable section

open scoped Classical
open ValuativeRel MeasureTheory

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.L2.SG.NGDict


section Split

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem R_eq_O_of_none {M : Model F E} (h : M.split = none) : M.R = M.L.O := by
  unfold Model.R
  rw [h]






end Split

def LocOOpen : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), IsOpen (L.O : Set E)




end PI.NGStepBBW
end
end
