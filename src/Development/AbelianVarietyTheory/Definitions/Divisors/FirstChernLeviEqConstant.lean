module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs

@[expose] public section

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4O

section One

variable {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Z : Set X) (r : X → ℝ) (Om : LocPot X)

end One

attribute [instance] Man.top Man.cpt Man.t2 Man.ne

namespace Man

variable {e : ℕ} (M : Man e)

end Man

attribute [instance] Calc.grp Calc.mod

namespace An

variable {e : ℕ} {M : Man e} {ι : Type} [Fintype ι] {N : ℕ} (F : An M ι N) (j : ℕ)

end An

variable {D : D7} (Y : ShimX D.what₂.Tau)

variable {Y} (T : Real0 Y) (A : SlopeTestRemainingChoices Y)

variable (H : Ht Y)

end GlobalTheory.Mean4O
