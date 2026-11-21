import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumTwoOfHodgeTate
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open Module TensorProduct GlobalTheory.Pst.DpstMap

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Split

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}


variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]


end Split

section Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a b : ℕ}



end Sum
