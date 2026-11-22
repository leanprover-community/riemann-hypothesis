module

public import Formalism.WachLatticeTwists.Statement
public import Formalism.CharacterColumnKernels.Statement
public import Formalism.CharacterColumnKernels.StatementRho

@[expose] public section

universe u

open Formalism.NG (KO annih)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LOC

def eO (O : Type u) [CommRing O] (ℓ : ℕ) : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})

def toKO (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    FractionRing O →ₗ[O] KO O := Submodule.mkQ _

def mulSub {O : Type u} [CommRing O] (a : O) (M : Type u) [AddCommGroup M] [Module O M] :
    Submodule O M := LinearMap.range (LinearMap.lsmul O M a)

attribute [instance] DirectPush.gY DirectPush.mY DirectPush.gVY DirectPush.mVY DirectPush.gL
  DirectPush.mL DirectPush.gVL DirectPush.mVL

namespace DirectPush

variable {O A HV : Type u} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup HV]
    [Module O HV] {q : HV →ₗ[O] A} (P : DirectPush O A HV q)

end DirectPush

attribute [instance] DualPush.gY DualPush.mY DualPush.gVY DualPush.mVY DualPush.gVY' DualPush.mVY'
  DualPush.gLb DualPush.mLb DualPush.gVLb DualPush.mVLb

namespace DualPush

variable {O A HT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup HT'] [Module O HT']
    {pr : A →ₗ[O] HT' →ₗ[O] KO O} (Q : DualPush O A HT' pr)

end DualPush

def StatLocTorsDual : Prop :=
  ∀ (O A H : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup H] [Module O H]
    (pr : A →ₗ[O] H →ₗ[O] KO O) (M : Submodule O H) (S : Submodule O A) (a : O),
    (∀ s ∈ S, a • s ∈ annih pr M) →
    Module.length O (S ⧸ (annih pr M).comap S.subtype) ≤
      Module.length O (M ⧸ mulSub a M)

def StatLocQuotLen : Prop :=
  ∀ (O M : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (d : ℕ)
    (N : Submodule O (Fin d → KO O)) (δ : N →ₗ[O] M), Submodule.torsion O M ≤ LinearMap.range δ →
    ∀ ℓ e : ℕ, Module.length O (M ⧸ mulSub ((ℓ : O) ^ e) M) ≤
      ((Module.finrank O M + d : ℕ) : ℕ∞) * ((e : ℕ∞) * eO O ℓ)

end Formalism.RepresentationBoundsCohomology.LOC
