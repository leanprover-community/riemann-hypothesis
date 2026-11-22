module

public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace Formalism.IndefR.NX.BC

section Gen

variable (Ks L0 L : Type) [Field L0] [Field Ks] [Field L] [Algebra Ks L0] [Algebra L0 L] [Algebra Ks L]
  [IsScalarTower Ks L0 L]
variable (WL : Type) [AddCommGroup WL] [Module L0 WL] [Module Ks WL] [IsScalarTower Ks L0 WL]

instance acgBCW : AddCommGroup (BCW Ks L0 L WL) := inferInstanceAs (AddCommGroup (L ⊗[L0] WL))

instance modL : Module L (BCW Ks L0 L WL) := inferInstanceAs (Module L (L ⊗[L0] WL))

instance modKs : Module Ks (BCW Ks L0 L WL) := Module.compHom _ (algebraMap Ks L)

instance towKsL : IsScalarTower Ks L (BCW Ks L0 L WL) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

variable {W : (L0 →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]

instance nWbc (σ : L →+* ℂ) : NormedAddCommGroup (Wbc L0 L W σ) :=
  inferInstanceAs (NormedAddCommGroup (W (σ.comp (algebraMap L0 L))))

instance ipWbc (σ : L →+* ℂ) : InnerProductSpace ℂ (Wbc L0 L W σ) :=
  inferInstanceAs (InnerProductSpace ℂ (W (σ.comp (algebraMap L0 L))))

variable {Ks L0 L WL}

end Gen

section Forms

variable {Ks L0 : Type} [Field L0] [NumberField L0] [Field Ks] [NumberField Ks] [Algebra Ks L0]
variable (L : Type) [Field L] [NumberField L] [Algebra L0 L] [Algebra Ks L] [IsScalarTower Ks L0 L]
variable {WL : Type} [AddCommGroup WL] [Module L0 WL] [Module Ks WL] [IsScalarTower Ks L0 WL]
variable {W : (L0 →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0]

instance modOKs : Module (𝓞 Ks) (BCW Ks L0 L WL) :=
  Module.compHom _ ((algebraMap Ks L).comp (algebraMap (𝓞 Ks) Ks))

instance towOKs : IsScalarTower (𝓞 Ks) Ks (BCW Ks L0 L WL) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

variable (A : Arith.FormsL L0 Ks WL W G0)

variable [Module (𝓞 L0) WL] [IsScalarTower (𝓞 L0) L0 WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [Fintype G0]

end Forms

section Rec

open Formalism.BasicNotions

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

def rdTw (tw : NTw R H what₂ LL0 N) (i : tw.Tw) (b : Bool) : ↥LL0 →+* FractionRing (tw.O i) :=
  (IsFractionRing.map (A := tw.O0 i) (B := tw.O i) (K := FractionRing (tw.O0 i)) (L := FractionRing (tw.O i))
    (tw.O_inj i)).comp (if b then tw.emb0 i else tw.emb0b i)

end Rec

section Test

end Test

section BsupMap

open Formalism.BasicNotions

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

end BsupMap

end Formalism.IndefR.NX.BC
