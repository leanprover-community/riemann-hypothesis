module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineMultihomogClassify
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)

section Objects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

namespace Res

variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)

end Res

def IsProjVarQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P0 ∧ ringKrullDim (MRing ι ℚ ⧸ P0) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

section Ring

variable {K : Type} {ι : K → Type}

end Ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
