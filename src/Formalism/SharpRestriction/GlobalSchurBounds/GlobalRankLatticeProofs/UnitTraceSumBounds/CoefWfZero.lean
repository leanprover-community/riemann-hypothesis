import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ExpIntW
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
import Formalism.SharpRestriction.GlobalSchurBounds.StatementTranslationInvariantSeventh

section
open Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

def PtW {p : ℕ} [Fact p.Prime] {σ : Type} (a : MvPowerSeries σ ℂ_[p]) : Prop :=
  IntegralW a ∧ MvPowerSeries.constantCoeff a = 0

def AddPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]), PtW a → PtW b → PtW (g.add a b)

def MulPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → ∀ c : ℂ_[p], IntegralW (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) →
    ∀ (σ : Type) (a : MvPowerSeries σ ℂ_[p]), PtW a → PtW (g.mulBy c a)

def LinPtW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∀ (ι : Type) [Fintype ι] (c : ι → ℂ_[p]), (∀ j, IntegralW (g.mulBy (c j) (Xv ()) : MvPowerSeries Unit ℂ_[p])) →
    ∀ (σ : Type) (a : ι → MvPowerSeries σ ℂ_[p]), (∀ j, PtW (a j)) → PtW (g.lin c a)

end Formalism.MainNotions.Ext
end

section
namespace Formalism.MainNotions.GL3Theta

theorem readW_holds : readW := expIntegralWitt

end Formalism.MainNotions.GL3Theta
end

section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

section

variable {p : ℕ} [Fact p.Prime]

theorem ptW_X {σ : Type} (i : σ) : PtW (Xv i : MvPowerSeries σ ℂ_[p]) := by
  classical
  unfold PtW
  constructor
  · intro n
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp

theorem coefWf_add {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f + g) := (coefWfRing_holds p σ f g hf hg).1

theorem coefWf_sub {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) : CoefWf (f - g) := (coefWfRing_holds p σ f g hf hg).2.1

theorem coefWf_phAt (g : G1 p) (hph : CoefWf g.ph) {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : PtW a) : CoefWf (g.phAt a) := by
  obtain ⟨ha1, ha2⟩ := ha
  exact substWf_holds p σ g.ph a hph ha1 ha2

theorem coefWf_be (HA : AddPtW) (g : G1 p) (hOk : g.Ok) (hF : IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hph : CoefWf g.ph) {σ : Type} {a b : MvPowerSeries σ ℂ_[p]} (ha : PtW a) (hb : PtW b) : CoefWf (g.be a b) := by
  have hab : PtW (g.add a b) := HA p g hOk hF σ a b ha hb
  show CoefWf (g.phAt (g.add a b) - g.phAt a - g.phAt b)
  exact coefWf_sub (coefWf_sub (coefWf_phAt g hph hab) (coefWf_phAt g hph ha)) (coefWf_phAt g hph hb)

theorem simeqW_of {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : CoefWf f) (hg : CoefWf g) (h : Simeq f g) : SimeqW f g := by

  obtain ⟨h0, hI⟩ := h
  have hr : SimeqW (f - g) 0 :=
    readW_holds p σ (f - g) (coefWf_sub hf hg) (And.intro (by simpa using h0) (by simpa using hI))
  obtain ⟨r0, rI⟩ := hr
  exact And.intro (by simpa using r0) (by simpa using rI)

end


end Formalism.MainNotions.Ext
end

section
namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3r7

section

variable {p : ℕ} [Fact p.Prime]



end



end Formalism.MainNotions.Ext
end
