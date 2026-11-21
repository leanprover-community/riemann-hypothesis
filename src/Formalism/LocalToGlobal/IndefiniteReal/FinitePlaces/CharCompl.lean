import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix Topology
open scoped TensorProduct ComplexConjugate Pointwise

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (S T : HSp D)

abbrev QO : Type := MO S T ⧸ ratL T S

def chiO (ψ : AddChar (AF D.host.F) ℂ) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) : ℂ :=
  ψ (symplO S T z (ratW T S a))

theorem periodic_of {f : MO S T → ℂ} (hf : ∀ a z, f (ratW T S a + z) = f z) :
    ∀ g ∈ ratL T S, ∀ z, f (g + z) = f z := by
  intro g hg z
  obtain ⟨a, rfl⟩ := (mem_ratL_iff S T g).1 hg
  exact hf a z

theorem chiO_periodic (hψ : IsStdChar D ψ (-1)) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : MO S T) :
    chiO S T ψ a (ratW T S b + z) = chiO S T ψ a z := by
  unfold chiO
  rw [symplO_add_left, AddChar.map_add_eq_mul, psi_rat hψ, one_mul]

def liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) : QO S T → ℂ :=
  Quotient.lift f (by
    intro x y hxy
    have h : -x + y ∈ ratL T S := QuotientAddGroup.leftRel_apply.1 hxy
    have := periodic_of S T hf (-x + y) h x
    rw [show -x + y + x = y by abel] at this
    exact this.symm)

theorem cont_liftQ (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) :
    Continuous (liftQ S T f hf) :=
  hc.quotient_lift _

def liftC (f : MO S T → ℂ) (hf : ∀ a z, f (ratW T S a + z) = f z) (hc : Continuous f) : C(QO S T, ℂ) :=
  ⟨liftQ S T f hf, cont_liftQ S T f hf hc⟩


def chiC (hψ : IsStdChar D ψ (-1)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : C(QO S T, ℂ) :=
  liftC S T (chiO S T ψ a) (fun b z => chiO_periodic S T hψ a b z)
    ((psi_cont hψ).comp (cont_symplO_left S T _))

theorem chiC_apply (hψ : IsStdChar D ψ (-1)) (a) (z : MO S T) :
    chiC S T hψ a (z : QO S T) = ψ (symplO S T z (ratW T S a)) := rfl

theorem chiC_mul (hψ : IsStdChar D ψ (-1)) (a b : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    chiC S T hψ a * chiC S T hψ b = chiC S T hψ (a + b) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.mul_apply, chiC_apply, ratW_add, symplO_add_right, AddChar.map_add_eq_mul]

theorem chiC_zero (hψ : IsStdChar D ψ (-1)) : chiC S T hψ 0 = 1 := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.one_apply, chiC_apply, ratW_zero, symplO_zero_right, AddChar.map_zero_eq_one]

theorem chiC_star (hψ : IsStdChar D ψ (-1)) (a : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    star (chiC S T hψ a) = chiC S T hψ (-a) := by
  ext q
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [ContinuousMap.star_apply, chiC_apply, chiC_apply, ratW_neg, symplO_neg_right]
  exact psi_conj hψ _

def Achar (hψ : IsStdChar D ψ (-1)) : StarSubalgebra ℂ C(QO S T, ℂ) where
  carrier := Submodule.span ℂ (Set.range (chiC S T hψ))
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  mul_mem' := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem x hx =>
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [chiC_mul]
        exact Submodule.subset_span ⟨a + b, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  one_mem' := by
    rw [← chiC_zero S T hψ]; exact Submodule.subset_span ⟨0, rfl⟩
  algebraMap_mem' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← chiC_zero S T hψ]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [chiC_star]; exact Submodule.subset_span ⟨-a, rfl⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [star_add]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h






end Formalism.IndefR.Fin

end
