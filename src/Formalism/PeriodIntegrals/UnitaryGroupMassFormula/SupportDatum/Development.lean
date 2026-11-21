import Mathlib
import Formalism.PeriodIntegrals.SupportParts
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocProdFormula

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocStep : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (p : PlF D), Agree δ M p →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)), kind w = kind w' →
  ∀ c : Option ((M p).Cls D.R.rS), BBtop M δ T T' p w c ≠ 0 → BBtop M δ T T' p w' c ≠ 0 →
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) =
        (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
      (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS))

def TopNe : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (w : Point D.host.E (D.R.rS + 1)), Dmin w (D.R.rS + 1) ≠ 0


theorem norm_conjF (D : Formalism.BasicNotions.D7) (x : D.host.E) :
    Algebra.norm ℚ (D.conjF x) = Algebra.norm ℚ x := by
  let σ : D.host.E →ₐ[ℚ] D.host.E := D.conjF.restrictScalars ℚ
  have hb : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  exact Algebra.norm_eq_of_algEquiv (AlgEquiv.ofBijective σ hb) x




end PI.SupportDatumW
