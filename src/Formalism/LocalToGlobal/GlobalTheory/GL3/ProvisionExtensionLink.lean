import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.FrobeniusOrbits Classical

def LinkStdOK : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.StdOK

def LinkVecB : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → NonzeroThetaVectorFamily D (tor0 D cc δ) (B.eNat χ)

def LinkThB : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ →
      ThetaNormIndependent D (tor0 D cc δ) (B.eNat χ) ∧ th22U D (tor0 D cc δ) (B.eNat χ)

def LinkNormB : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → ∀ N N' L L', admitted D N N' L L' →
      normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (B.eNat χ N N' L L')
        = normSq D (tor0 D cc δ) (La D (tor0 D cc δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N')) (B.thZero N N')

def LinkExistsBase : Prop :=
  ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∃ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

theorem standard_basis_ok_link : LinkStdOK := fun _ _ hcc _ hδ B => SO.stdOK B hcc hδ

theorem vector_bound_link : LinkVecB :=
  fun D cc hcc δ hδ B => vector_link_holds D cc hcc δ hδ B (SO.stdOK B hcc hδ)




def LinkPeriodPair : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → ∀ δ : ℂ, δ ≠ 0 →
    ∃ L : PeriodPair, L.lattice.toAddSubgroup = lamOf D cc δ

def BasePointExists : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 →
    ∃ t : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t

def IsoExists (D : D7) : Prop :=
  ∃ (γ₀ : IsoK D) (gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
    ∀ x : Fin 4 → D.host.E, gC (fun w => embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)

def IsoPExists (D : D7) : Prop :=
  ∀ p : ℕ, p.Prime → SplitK D p → ∃ γ : IsoK D, γ.AtP p

def LinkBase : Prop :=
  ∀ D : D7, IsoExists D → IsoPExists D → BaseExists D





theorem ext_exists {K E : Type} [Field K] [Field E] [Algebra K E] {I : Type} [Fintype I] [DecidableEq I]
    (g : (Fin 4 → E) ≃ₗ[K] (I → K)) (φ : K →+* ℂ) (em : (Fin 4 → E) →+ (I → ℂ))
    (hem : ∀ (k : K) (y : Fin 4 → E), em (k • y) = φ k • em y)
    (hspan : Submodule.span ℂ (Set.range em) = ⊤) :
    ∃ G : (I → ℂ) ≃ₗ[ℂ] (I → ℂ), ∀ x, G (em x) = fun w => φ (g x w) := by
  have repr : ∀ x, x = ∑ v, (g x v) • g.symm (Pi.single v 1) := by
    intro x
    apply g.injective
    rw [map_sum]
    simp_rw [map_smul, LinearEquiv.apply_symm_apply]
    funext w
    simp [Finset.sum_apply, Pi.single_apply]
  let hC : (I → ℂ) →ₗ[ℂ] (I → ℂ) :=
    { toFun := fun c => ∑ v, c v • em (g.symm (Pi.single v 1))
      map_add' := by intro a b; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.smul_sum, mul_smul] }
  have key : ∀ x, hC (fun w => φ (g x w)) = em x := by
    intro x
    conv_rhs => rw [repr x]
    rw [map_sum]
    simp_rw [hem]
    rfl
  have hsurj : Function.Surjective hC := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, key x⟩
  have hinj : Function.Injective hC := LinearMap.injective_iff_surjective.2 hsurj
  refine ⟨(LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩).symm, fun x => ?_⟩
  rw [← key x]
  exact LinearEquiv.symm_apply_apply (LinearEquiv.ofBijective hC ⟨hinj, hsurj⟩) _

def LinkIsoExt : Prop := ∀ D : D7, Nonempty (IsoK D) → IsoExists D


def DiscrNe (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → discr (lamOf D cc 1) ≠ 0

def IsometryExtensionLink : Prop :=
  ∀ (D : D7) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D → Nonempty (IsoK D) → IsoPExists D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C


end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
