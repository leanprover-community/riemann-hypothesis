import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def DensGood : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      RowsOf u F0 what₂ →
      ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
        ∀ Z : MatZ D, TotPos (GZ (Tn u) (Tn u') Z) →
          ∃ C : ℝ, ∀ᶠ p in Filter.cofinite,
            |densP L δ ϖ (Tn u) (Tn u') Z p - 1| ≤ C * (1 / ((p.asIdeal.absNorm : ℝ) ^ 2))

def PrimeZeta2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    Summable (fun p : HeightOneSpectrum (𝓞 K) => 1 / ((p.asIdeal.absNorm : ℝ) ^ 2))


end PI.UnitaryGroupMassFormula.CntFormula
