module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FnCycMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.GalOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalQuot

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped nonZeroDivisors

namespace UpperTheory.V.Tower

section Norm

variable (K : Type) {K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

end Norm

section Lim

variable (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

variable (k : Type) [Field k] [NumberField k] [Algebra k Ω] [IsAlgClosure k Ω]

end Lim

section Desc

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

variable (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra L Ω] [IsScalarTower k L Ω] [IsAlgClosure L Ω]

def IsDesc {l : ℕ} [Fact l.Prime] (D : LData L Ω l) (e : ℤ) (U : Subgroup (G k Ω)) [U.Normal]
    (Φ : Sha D e →ₗ[ℤ_[l]] ShaD l l U (galOf k L Ω) e) : Prop :=
  ∀ (x : Sha D e) (u : Uinf L Ω l) (u' : cycU l U), u'.1 = galEmb k L Ω u.1 → (Φ x).1.1 u' = resInf D e x.1 u

variable [Normal k L]

variable (k Ω) (l : ℕ) [Fact l.Prime] (N : ℕ)

end Desc

end UpperTheory.V.Tower

end
