module

public import Formalism.LocalToGlobal.ProjectiveLattices.GenSectB

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

theorem psi_kt (x : Fin m → Ω) (j₀ : Fin m) (q : KT K D m) :
    psi x j₀ (ktToΩ K Ω D m q) = aeval (gs x j₀) q := by
  show aeval (gs x j₀) (MvPolynomial.map (algebraMap K Ω) q) = aeval (gs x j₀) q
  rw [MvPolynomial.aeval_map_algebraMap]

theorem algKTR_apply (q : KT K D m) :
    algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
      algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := by
  exact IsLocalization.map_eq _ _

def Phi (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    RS K Ω D m →+* FractionRing (CT Ω D j₀) :=
  IsLocalization.lift (M := KTS K Ω D m)
    (g := (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp (psi x j₀).toRingHom) (by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, rfl⟩ := hs
      refine isUnit_iff_ne_zero.mpr ?_
      show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ (ktToΩ K Ω D m q)) ≠ 0
      rw [psi_kt]
      exact fun h => hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm)))

theorem Phi_algebraMap (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0)
    (a : ΩT Ω D m) :
    Phi x j₀ hinj (algebraMap (ΩT Ω D m) (RS K Ω D m) a) =
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) :=
  IsLocalization.lift_eq _ _

theorem Phi_mk'_spec (x : Fin m → Ω) (j₀ : Fin m)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) (a : ΩT Ω D m) (y : KTS K Ω D m)
    (v : FractionRing (CT Ω D j₀)) :
    Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) a y) = v ↔
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) =
        algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) * v :=
  IsLocalization.lift_mk'_spec _ _ _ _

end Formalism.L2.Pj.GenSect
