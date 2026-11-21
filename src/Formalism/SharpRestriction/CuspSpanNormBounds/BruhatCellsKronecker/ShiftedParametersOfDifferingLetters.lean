import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NcardPrimesOverOfSplitsCompl
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.PrimeIdealNormRpowSumLe

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryVolumeMass NumberField IsDedekindDomain
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section HS

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]





end HS

section Sums

variable {T V : Type*} [NormedAddCommGroup V] [CompleteSpace V]



end Sums

section Parts

variable (D : D7) (u u' : D.what₂.Word)


def genericLoopPairs : Set (D.s.Pair u u') := {p | p ∈ pairsIn D.s (famG D.s) ∧ loopP D.s p}






end Parts

section Record

open scoped nonZeroDivisors

variable (D : D7) (large₂ : SizeData₂ D)







def s76x (u u' : D.what₂.Word) (l : ℕ) : D.what₂.Tau → LocalDataRealPlace D := fun τ =>
  { lam := lamSH D.R (D.hc τ), u := uS D u τ, u' := uS D u' τ,
    l := ⟨0, by have := D.R.m_add_three_le_k; omega⟩,
    a := 5 / 2 - vOne D τ l, b := (D.s.Del : ℝ) / 2 - vOne D τ l,
    a1 := 5 / 2 - vOne D τ l, b1 := NA D ^ 3 - vOne D τ l }

def s76L : LatticeDataWithDual D :=
  { La := fun _ _ => ⊥, La' := fun _ _ => ⊥,
    aaV := fun i s => ddE D ^ (-((2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1)) + 1)) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹,
    aaP := fun i s => ddE D ^ (-(2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1))) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹,
    κ := 0, ρ := rhoReal D }



def nongenericFactor (c C : ℝ) : ℝ :=
  Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ))) +
    (2 : ℝ) ^ (-((D.R.k : ℝ) - 2 * (D.R.rS : ℝ) - 5)) * Real.exp (C * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)

def loopFactor (c : ℝ) : ℝ := Real.exp (-(c * (D.R.k : ℝ) * (D.R.f : ℝ) * Real.log (D.R.k : ℝ)))

structure AdmissibleConstantInequalities (ca : AdmissibleBoundsFromSource.AdmC) : Prop where
  cut : ca.CA * ((D.R.k : ℝ) * NA D * ((D.R.rS : ℝ) + 1) ^ 2 + NA D ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + NA D ^ 3) ≤
    (D.s.Del : ℝ) / 2 - 5 / 2
  cut2 : NA D ^ 3 ≤ (D.s.Del : ℝ) / 2
  th : ca.CA' ≤ (D.R.k : ℝ) ^ ca.c5
  off : ∃ t : ℝ, 0 < t ∧
    (1 + t) * (f3 D * loopFactor D ca.cL + (1 + ca.CA * large₂.sc.b ^ (-7 : ℝ)) * (1 + eSum D ca.Ce) * f3 D) +
      (1 + 1 / t) * nongenericFactor D large₂ ca.cN ca.CN ≤ 1 + AdmissibleBoundsFromSource.eta0 D large₂
  diag : ∃ t : ℝ, 0 < t ∧
    (1 + t) * (f3 D * loopFactor D ca.cL + f3 D * Real.exp (ca.CE * (D.R.m : ℝ) ^ 5 * (D.R.f : ℝ) * large₂.sc.L)) +
      (1 + 1 / t) * nongenericFactor D large₂ ca.cN ca.CN ≤ AdmissibleBoundsFromSource.Gam D





end Record

section Numbers










variable (D : D7) (large₂ : SizeData₂ D)



end Numbers

section Family

variable {eps : ℝ} (Fm : FamP eps)


end Family

section Forms



end Forms

end Formalism.MainNotions.BridgeLemma

end
