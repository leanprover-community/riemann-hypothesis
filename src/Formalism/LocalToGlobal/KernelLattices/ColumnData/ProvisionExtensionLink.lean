import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP

noncomputable section

namespace Formalism.L2.Ker.Cd.IntegralLatticeDensity

open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity hiding CMConjEmb CMTransitive DedekindFactor LinkChi LinkPer LinkThIndep LinkThU LinkThUFam ThetaNormIndependent theta_norm_independent_of_bounds th22U theta_norm_unitary_invariant_of_bounds

open NumberField Formalism.BasicNotions Formalism.L2.Ker Formalism.FrobeniusOrbits Classical
open Formalism.L2.Ker.Cd.TaylorLogMetric
open Formalism.MainNotions.TaylorLogMetric hiding admitted AdmittedStatements AllSplit CoefIn DataIn DualB EqAt EqAway FamE Hf IdE InProd Iop IsChi IsComb IsCurveIdeal IsDiscriminantTwelfthRootOfIdealLattice IsFrobC IsIdem JetsInt La LocBasis LocBasisW Mono N1 NNBasis OrthoBasisW Orthonormal Pos Qd QdB Stmt TVar TVarB Th ThSp Tor TorsPrime U VC Wop XiF YYl adm1 al atLog chK chg chgB coordV der detId logDerivativeAtOne ellT embT embV eq22 fF fnConj hYY hh homL int22 jet kap lamOf letterOf liftY logOmVal meanLogNormSq meanLogOm mmM mom22 LargerSupportMomentCondition mono normSq pSer pairN per22 posEmb posG aux₃ pull qH sE sgm str22 tauEmb tauSg taylor th22 tor0 torConj vec22 vecN wPh zB

def LinkStdOK : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, B.StdOK

def LinkVecB : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → NonzeroThetaVectorFamily D (tor0 D cc δ) (B.eNat χ)

def LinkThB : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ →
      ThetaNormIndependent D (tor0 D cc δ) (B.eNat χ) ∧ th22U D (tor0 D cc δ) (B.eNat χ)

def LinkNormB : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ B : Base D cc δ, ∀ χ, IsChi D χ → ∀ N N' L L', admitted D N N' L L' →
      normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (B.eNat χ N N' L L')
        = normSq D (tor0 D cc δ) (La D (tor0 D cc δ) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N) (Formalism.L2.Ker.Cd.StandardLatticesGL3.stdL D N')) (B.thZero N N')

def LinkExistsBase : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∃ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C

theorem standard_basis_ok_link : LinkStdOK := fun _ _ hcc _ hδ B => SO.stdOK B hcc hδ

theorem vector_bound_link : LinkVecB :=
  fun D cc hcc δ hδ B => vector_link_holds D cc hcc δ hδ B (SO.stdOK B hcc hδ)



def LinkPeriodPair : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → ∀ δ : ℂ, δ ≠ 0 →
    ∃ L : PeriodPair, L.lattice.toAddSubgroup = lamOf D cc δ

def BasePointExists : Prop :=
  ∀ D : Car, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 →
    ∃ t : ℂ, Formalism.L2.Ker.Cd.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t

def IsoExists (D : Car) : Prop :=
  ∃ (γ₀ : IsoK D) (gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
    ∀ x : Fin 4 → D.host.E, gC (fun w => embT D w.2 (x w.1)) = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E)

def IsoPExists (D : Car) : Prop :=
  ∀ p : ℕ, p.Prime → SplitK D p → ∃ γ : IsoK D, γ.AtP p

def LinkBase : Prop :=
  ∀ D : Car, IsoExists D → IsoPExists D → BaseExists D





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

def LinkIsoExt : Prop := ∀ D : Car, Nonempty (IsoK D) → IsoExists D


def DiscrNe (D : Car) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ → discr (lamOf D cc 1) ≠ 0

def IsometryExtensionLink : Prop :=
  ∀ (D : Car) (C : ℝ), AdmittedStatements D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ → per22 D (tor0 D cc δ)) →
    DiscrNe D → Nonempty (IsoK D) → IsoPExists D →
    (∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∀ B : Base D cc δ, ∀ χ, IsChi D χ → EigenvectorPacketProperties B C χ) →
    aux₃ D C


end Formalism.L2.Ker.Cd.IntegralLatticeDensity

end
