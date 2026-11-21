import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeInertUnramified

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

section Objects

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def SphericalAtInert (B : NBC A) (j : ℕ) (π : B.AU j) : Prop :=
  ∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w

structure IsDiscreteSelfDualSum (A : NAut N) (P : List (Part A.CG)) : Prop where

  discrete : ∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d

  selfDual : ∀ p ∈ P, A.csd p.π

  distinct : P.Nodup

structure IsBaseChange (B : NBC A) (j : ℕ) (π : B.AU j) (P : List (Part A.CG)) : Prop where

  parts : IsDiscreteSelfDualSum A P

  rank : rankIso N A P = R.nV

  split : ∀ w : PlE H, IsSplitPl H w → isoLoc N A P w = B.locAU j π w

  inertUnr : ∀ w : PlE H, ¬ IsSplitPl H w → A.unr (isoLoc N A P w)

  inertSat : ∀ w : PlE H, ¬ IsSplitPl H w →
    A.frobEig (isoLoc N A P w) = ubc R.nV (B.satAU j π w)

  infChar : ∀ τ : H.E →+* ℂ, isoInf N A P τ = B.infW j (B.wtAU j π) τ

def BaseChangeExists (B : NBC A) (j : ℕ) : Prop :=
  ∀ π : B.AU j, SphericalAtInert B j π → ∃ P : List (Part A.CG), IsBaseChange B j π P

end Objects

structure Standing (D : D7) (j : ℕ) : Prop where
  cm : @CMData D.host.F D.host.E _ _ _ _ D.host.cmStar _
  unram : ∀ w : PlE D.host, Algebra.IsUnramifiedAt (𝓞 D.host.F) w.asIdeal
  degree : 2 ≤ Module.finrank ℚ D.host.F
  inertOdd : ∀ w : PlE D.host, ¬ IsSplitPl D.host w → (2 : 𝓞 D.host.E) ∉ w.asIdeal
  rank : letI := D.host.cmStar; (D.sp.V j).rank = D.R.nV
  definite : letI := D.host.cmStar; (D.sp.V j).IsDefinite

def AtRecordGuarded (D : D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → Standing D j → BaseChangeExists D.nbc j

def AtRecord (D : D7) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → BaseChangeExists D.nbc j

def ForFamily {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ x : ℝ, Fm.x1 < x → ∀ i : Fm.Ix x, AtRecord (Fm.D x i)

def BaseChangeClosed (𝒞 : FamClass) : Prop :=
  Closed 𝒞 (fun Fm _ => ForFamily Fm)





end GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeInertUnramified

end
