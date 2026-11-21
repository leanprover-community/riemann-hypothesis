import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.SimilitudeFactorFormGroupBoundedOfTestSupport
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Formalism.DegreeFormula.PointDegree.FlagDeg

section
noncomputable section

open Classical

namespace GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst

open GlobalTheory.CompanionTheory.Ar.Cmp

def relab (N j : ℕ) (a : Fin N) : ℕ := if (a : ℕ) < N - j then j + a else a - (N - j)

def Sep {Ψ : Type} (N j : ℕ) (x : Ψ × Fin N) (c : LowEnt Ψ N) : Prop :=
  c.1 = x.1 ∧ min (relab N j c.2.1.1) (relab N j c.2.1.2) ≤ (x.2 : ℕ) ∧
    (x.2 : ℕ) < max (relab N j c.2.1.1) (relab N j c.2.1.2)

def sepCount {Ψ : Type} [Fintype Ψ] {e : ℕ} (N j : ℕ) (w : Fin e → Ψ × Fin N) : ℝ :=
  ∑ f : LowEnt Ψ N ≃ Fin e, ∏ c : LowEnt Ψ N, if Sep N j (w (f c)) c then (1 : ℝ) else 0



end GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst
end
end

section
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst
open Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst.Polar

open MvPolynomial

def lamS {Ψ : Type} {N e : ℕ} (w : Fin e → Ψ × Fin N) (S : Finset (Fin e)) : Ψ → Fin N → ℝ :=
  fun τ k => ∑ r ∈ S, if (w r).1 = τ ∧ k ≤ (w r).2 then (1 : ℝ) else 0

end GlobalTheory.CompanionTheory.Ar.Cmp.FlagCst.Polar
end
end
