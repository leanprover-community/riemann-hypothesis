module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds

section Operators

variable {B : Scheme.{0}} (P : Out.PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A)))

def IsMulPull (k : ℕ) (a : ℤ) {T : Over B} (θ : LB.Sec (Out.LPow P.A P.L 1 T)) (s : LB.Sec (Out.LPow P.A P.L a T)) : Prop :=
  ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ k).left] ![a, -1]),
    α.IsGen ∧
    LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (Out.ptSecT P.A 1).left)
      (LB.mulGen P.L _ _ _ _ (Out.rigT P.A P.L rig T a) (LB.invGen P.L _ _ (Out.rigT P.A P.L rig T 1))) ∧
    Out.IsTwistPull P.A P.L (Out.mulT P.A T k) (snd T P.A ^ k) (lift_snd _ _) a 1 α θ s

def IsValueZero (a : ℤ) {T : Over B} (s : LB.Sec (Out.LPow P.A P.L a T)) (v : Γ(T.left, ⊤)) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)),
    τ.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ τ (Out.rigT P.A P.L rig T a) ∧ Out.IsValueAt P.A P.L a s 1 τ v

end Operators

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

section Tests

variable {p : ℕ} [Fact p.Prime]

abbrev intRing (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : ValuationSubring K :=
  (OO p).comap (algebraMap K (PadicAlgCl p))

theorem intRing_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Function.Injective ((algebraMap K (PadicAlgCl p)).comp (intRing K).subtype) :=
  (algebraMap K (PadicAlgCl p)).injective.comp Subtype.val_injective

instance fracAlgebra (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Algebra (FractionRing (intRing K)) (PadicAlgCl p) :=
  (IsFractionRing.lift (A := intRing K) (K := FractionRing (intRing K)) (intRing_injective K)).toAlgebra

attribute [instance] UnifTest.grp UnifTest.comm

end Tests

end GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds
end
