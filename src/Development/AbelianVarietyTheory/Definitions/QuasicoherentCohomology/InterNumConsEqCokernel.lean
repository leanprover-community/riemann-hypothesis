import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.InterModel

variable {X Z : Scheme.{0}} {k : Type} [Field k] [Algebra k Γ(X, ⊤)]

def cut (F : X.Modules) {M : LB X} (hM : M.IsLB) (σ : LB.Sec M) : twistZ F M (-1) ⟶ F :=
  Twist.mulSecOfEq F (Twist.zofSec σ) (neg_add_cancel 1) ≫ (Twist.twistZZeroIso F hM).inv



variable (k) {ι : Type} [Fintype ι]


theorem radical_ker (f : Z ⟶ X) [QuasiCompact f] [IsReduced Z] : f.ker.radical = f.ker := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  refine Ideal.IsRadical.radical fun a ⟨n, hn⟩ => ?_
  rw [RingHom.mem_ker] at hn ⊢
  rw [map_pow] at hn
  exact IsNilpotent.eq_zero ⟨n, hn⟩

theorem interNumRed_eq_interNumOn (f : Z ⟶ X) [IsClosedImmersion f] [IsReduced Z]
    (C : Closeds X) (h : Set.range f = C) (L : ι → LB X) :
    interNumRed k C L = interNumOn k f L := by
  rw [interNumOn_eq_interNumSub, interNumRed_def, ← radical_ker f,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 2
  ext1
  rw [Scheme.Hom.support_ker, h, C.isClosed.closure_eq]

theorem isZero_of_isEmpty [IsEmpty X] (F : X.Modules) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  have : U = ⊥ := Subsingleton.elim _ _
  subst this
  have : Subsingleton Γ(X, ⊥) := inferInstance
  have := Module.subsingleton Γ(X, ⊥) Γ(F, ⊥)
  exact Subsingleton.elim _ _





end GlobalTheory.InterModel
