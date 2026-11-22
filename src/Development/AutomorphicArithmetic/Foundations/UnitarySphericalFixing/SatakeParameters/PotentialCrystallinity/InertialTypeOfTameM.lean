module

public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralAndGoodOfIsSpherical
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterMonodromyZeroOfUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocDZOfSplitReg

@[expose] public section

noncomputable section

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SplitRead GlobalTheory.CuspRep in
theorem UpperTheory.One.M.goodI_of_sph {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (π : Irr k n) (h : IsSpherical π.π) : UpperTheory.One.M.GoodI π :=
  (GlobalTheory.SphSupport.toral_and_good_of_isSpherical UpperTheory.Zero.LLC.Pr.bz k (cls (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k)))
    (fixed_ne_bot_of_equiv (IrrRep.nonempty_equiv_rep (⟨π.V, π.π, π.smooth, π.irr⟩ : IrrRep (GL (Fin n) k))).some.symm h)).2

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.TameType

end GlobalTheory.TameType
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

namespace GlobalTheory.DepthZeroAssembly
open GlobalTheory.WeilDeligne (WD)
open GlobalTheory.SplitRead.BlockParam (twistIrr)

end GlobalTheory.DepthZeroAssembly
end
