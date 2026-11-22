module

public import Formalism.LocalToGlobal.HermitianColumns.StarConj
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.HermitianForms.DefsChi

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

def reGL {a b : ℕ} (h : a = b) (R : Type) [CommRing R] : GL (Fin a) R ≃* GL (Fin b) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finCongr h)).toMulEquiv

def reV {a b : ℕ} (h : a = b) (E : Type) [Field E] : (Fin a → E) ≃ₗ[E] (Fin b → E) :=
  LinearEquiv.funCongrLeft E E (finCongr h).symm

def reL {a b : ℕ} (h : a = b) {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin a → E)) :
    Submodule (𝓞 E) (Fin b → E) :=
  L.map ((reV h E : (Fin a → E) →ₗ[E] (Fin b → E)).restrictScalars (𝓞 E))

structure SameCar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {a b : ℕ} (h : a = b)
    {cls : Type} {stab : cls → Type}
    (Lb : Submodule (𝓞 E) (Fin a → E)) (Lb' : Submodule (𝓞 E) (Fin b → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin a) (E ⊗[F] v.adicCompletion F)))
    (Uloc' : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin b) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (U' : Subgroup (GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (y : cls → GL (Fin a) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (y' : cls → GL (Fin b) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (st : ∀ c, stab c → GL (Fin a) E) (st' : ∀ c, stab c → GL (Fin b) E) : Prop where
  Lb_eq : Lb' = reL h Lb
  Uloc_eq : ∀ v, Uloc' v = (Uloc v).map (reGL h _).toMonoidHom
  U_eq : U' = U.map (reGL h _).toMonoidHom
  y_eq : ∀ c, y' c = reGL h _ (y c)
  st_eq : ∀ c s, st' c s = reGL h _ (st c s)

end Re

theorem rank_eq_first_level (R : Ranks) : R.k = R.N 0 := by
  simp [Ranks.N]

def crdN (D : D7) (i : ℕ) (hi : i ≤ D.R.m) : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E) :=
  (D.sp.X i).frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)

def crdP (D : D7) : D.sp.X'.V ≃ₗ[D.host.E] (Fin (D.R.N D.R.m - 1) → D.host.E) :=
  D.sp.X'.frame.equivFun.trans (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankP D)).symm)

end Formalism.L2.Forms

end
