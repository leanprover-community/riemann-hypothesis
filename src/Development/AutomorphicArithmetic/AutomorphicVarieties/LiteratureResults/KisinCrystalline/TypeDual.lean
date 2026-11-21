import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KisinCrystalline.TypeSt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeDeformPer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AutomorphicArithmetic.AutomorphicVarieties.KisinPhiModules.TypeDualTwistIff

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module UpperTheory.V.Loc UpperTheory.V.Lit GlobalTheory.Pst GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

noncomputable section

namespace UpperTheory.V.Lit.TypeDual

section Alg



variable {Q A V F P J ι : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V]
  [IsScalarTower Q A V] [Field F] [Algebra Q F] [CommRing P] [Algebra Q P] [Algebra F P] [IsScalarTower Q F P]
  [Fintype J] [Fintype ι] (α : Basis J Q A)



end Alg

section Dual

variable {l : ℕ} [Fact l.Prime]





end Dual

section Cov

variable {l : ℕ} [Fact l.Prime] {A V : Type} [CommRing A] [Algebra ℚ_[l] A]
  [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

local notation "ci" => crisIncl (PP l) ℚ_[l] V
local notation "cm" => TensorProduct.comm ℚ_[l] (Bst (PP l)) V



private theorem ci_sm (L : FinExt l) (c : A ⊗[ℚ_[l]] ↥(K0 L)) (y : V ⊗[ℚ_[l]] Bcr l) :
    ci (smulC V L c y) = Thick.sm V (Bst (PP l)) c (ci y) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a k =>
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul v b =>
    refine (congrArg _ (Thick.sm_tmul a k v b)).trans ?_
    rw [crisIncl_tmul, crisIncl_tmul, Thick.sm_tmul, Polynomial.smul_C]


private def jU (A : Type) [CommRing A] [Algebra ℚ_[l] A] (L : FinExt l) :
    A ⊗[ℚ_[l]] ↥(K0 L) →ₐ[ℚ_[l]] A ⊗[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (IntermediateField.inclusion (inf_le_right : K0 L ≤ MaximalUnramifiedExtension l))



variable [FiniteDimensional ℚ_[l] V]



variable [Module.Finite ℚ_[l] A]


omit [Module.Finite ℚ_[l] A] [FiniteDimensional ℚ_[l] V] in
private theorem exists_gal (K K' : FinExt l) :
    ∃ L : FinExt l, K.1 ≤ L.1 ∧ K'.1 ≤ L.1 ∧ ((GK L).subgroupOf (GK K)).Normal := by
  haveI := (supExt K K').2
  let L : FinExt l := ⟨IntermediateField.normalClosure ℚ_[l] ↥(supExt K K').1 (Om l), inferInstance⟩
  have h : (supExt K K').1 ≤ L.1 := IntermediateField.le_normalClosure _
  haveI : (GK L).Normal := by
    haveI : IsGalois ℚ_[l] (Om l) := {}
    haveI : IsGalois ℚ_[l] ↥L.1 := { to_normal := normalClosure.normal _ _ _ }
    exact (InfiniteGalois.normal_iff_isGalois L.1).2 inferInstance
  exact ⟨L, le_sup_left.trans h, le_sup_right.trans h, inferInstance⟩


end Cov

end UpperTheory.V.Lit.TypeDual

end

open UpperTheory.V.Lit UpperTheory.V.Published

