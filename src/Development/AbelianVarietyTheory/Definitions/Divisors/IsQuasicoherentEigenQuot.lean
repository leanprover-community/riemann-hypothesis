module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self val_res homOfLinear homOfLinear_app isoOfLinear toMod fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover germ_resM)
open GlobalTheory.QCoh (IsFiniteQC appLinear appLinear_apply stalkLinear freeModule)

namespace GlobalTheory.VB

open scoped TensorProduct

variable {X Y : Scheme.{0}} {F G H : X.Modules} {U V W : X.Opens}

section Eigen

variable {O : Type} [CommRing O] (ρ : O →+* End F) (ρ' : O →+* End G) (ρ'' : O →+* End H)
  (σ : O →+* Γ(X, ⊤))

@[reassoc (attr := simp)] theorem eigenLift_ι (φ : G ⟶ F) (h : ∀ a, φ ≫ act ρ a = σ a • φ) :
    eigenLift φ h ≫ eigenι ρ σ = φ := rfl

instance epi_eigenπ : Epi (eigenπ ρ σ) := inferInstanceAs (Epi (cokernel.π _))

@[reassoc (attr := simp)] theorem eigenπ_desc (φ : F ⟶ G) (h : ∀ a, act ρ a ≫ φ = σ a • φ) :
    eigenπ ρ σ ≫ eigenDesc φ h = φ := cokernel.π_desc _ _ _

@[simp] theorem act_dualAct (a : O) : act (dualAct ρ) a = dualMap (act ρ a) := rfl

@[simp] theorem act_pullAct (f : Y ⟶ X) (a : O) :
    act (pullAct ρ f) a = (Scheme.Modules.pullback f).map (act ρ a) := rfl

end Eigen

section Split

variable {O : Type} [CommRing O] {k : Type} [Field k] {ι : Type}

variable {σ : ι → (O →+* k)}

variable [Algebra k Γ(X, ⊤)] (ρ : O →+* End F)

namespace IsSplitBy

variable [DecidableEq ι] (h : IsSplitBy σ)

variable [Fintype ι]

end IsSplitBy

end Split

section Frobenius

variable (p : ℕ) [Fact p.Prime]

variable (X) in
def frob (h : (p : Γ(X, ⊤)) = 0) : X ⟶ X := SS.FrobField.absFrob X p 1 Fact.out h

variable (h : (p : Γ(X, ⊤)) = 0)

theorem frob_app (U : X.Opens) (a : Γ(X, U)) : (frob X p h).app U a = (a ^ p : Γ(X, U)) :=
  congrArg (a ^ ·) (pow_one p)

@[reassoc] theorem frob_naturality (f : Y ⟶ X) (hY : (p : Γ(Y, ⊤)) = 0) :
    frob Y p hY ≫ f = f ≫ frob X p h := SS.FrobField.absFrob_nat f p 1 Fact.out hY h

variable {O : Type} [CommRing O] {k : Type} [Field k] [CharP k p] [Algebra k Γ(X, ⊤)]

end Frobenius

end GlobalTheory.VB
