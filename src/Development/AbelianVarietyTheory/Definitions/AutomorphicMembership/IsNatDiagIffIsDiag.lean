module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmHostRootComplexEqPmSqrt
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

abbrev Vecs (Dw : Datum H) {X : Scheme.{0}} (t : SAB H X) (R : Type) [CommRing R] : Type :=
  ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ t.G.left)

def IsFrame {l : Level H} {c : Coeff l} {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (f : c.F →+* R)
    (x : Sp R ⟶ X) (u : Vecs Dw t R) : Prop :=
  (∀ τ i, IsTanAtG t x (u τ i) ∧
    ∀ a : 𝓞 E, u τ i ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ u τ i) ∧
  ∀ τ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ w) →
    ∃! a : Fin (Dw.mult τ) → R, IsCombAtG t x (u τ) a w

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}

variable {Y : LocalSystem Xo p W} {i₀ : Idx H p}

namespace Pre

variable (Z : Pre Y i₀)

end Pre

namespace Mdl

variable (Z : Mdl Y i₀)

end Mdl

end GlobalTheory.LocM
