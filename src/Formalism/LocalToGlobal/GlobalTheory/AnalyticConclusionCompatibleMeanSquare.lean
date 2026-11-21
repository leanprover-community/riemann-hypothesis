import Formalism.LocalToGlobal.GlobalTheory.AnalyticConclusionOfProp25
import Formalism.GL3MeanSquares.HookFormulaTorsion.BoxCountAllStatement
import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.MeanSquareWeakOfPrimeNumberTheorem

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.MergeGL2b

open Formalism.LFunctionChainParameters Formalism.HermitianLattices Formalism.L2.GlobalTheoryTheory.MergeGL2

def AnalyticEndFinal : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x)

def AnalyticConclusionCompatible : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ ∀ ε A C₄ x₄ : ℝ, 0 < ε → ε ≤ 1 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d

def Chain6AtFinal : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ eD eL A K cHH eK eW KW ε C₄ x₄ : ℝ, 0 < ε → ε < 1 / 4 → 0 < A → 0 < C₄ →
    WeakMeanSquareEstimates.MeanSquareHypW ε C₄ x₄ →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε))

def AnalyticEndPNT : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → FiltrationCocycleLiftCriterion.QDExists ε CVal0 x ∧
      ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime), EndFor c' ε A CVal0 x (q1At ε x) (dAt ε x))

def AnalyticPrimeNumberTheoremCompatible : Prop :=
  ∃ c' : ℝ, 0 < c' ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ ε A : ℝ, 0 < ε → ε ≤ 1 → 0 < A →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ D : Formalism.BasicNotions.D7, FiltrationCocycleLiftCriterion.QDTied D x ε CVal0 →
      ∃ (_ : Fact D.host.q.Prime) (_ : Fact D.host.d.Prime), EndFor c' ε A CVal0 x D.host.q D.host.d)

def Chain6AtPNT : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ (PrimeNumberTheoremConsequences.PNTAPRelW → ∀ eD eL A K cHH eK eW KW ε : ℝ, 0 < ε → ε < 1 / 4 → 0 < A →
    ∃ x₁ : ℝ, ∀ x : ℝ, x₁ ≤ x → ∃ (_ : Fact (q1At ε x).Prime) (_ : Fact (dAt ε x).Prime),
      (CoreAt (q1At ε x) (dAt ε x) A Cord eD eL K cHH eK eW KW ε x →
        Formalism.Gz x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 6) * ε)))



theorem zeroDensityBox : ZeroDensityInBoxes.ZeroDensityBox := Ext.PrimitiveCharacterCasts.ZD.zero_density_box







theorem final_iff_closed : AnalyticEndFinal ↔ AnalyticEndClosed :=
  ⟨fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ _ hM => h ε A C₄ x₄ hε hε1 hA hC₄ hM⟩,
   fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => h ε A C₄ x₄ hε hε1 hA hC₄ zeroDensityBox hM⟩⟩

theorem finalTied_iff_closedTied : AnalyticConclusionCompatible ↔ AnalyticEndClosedTied :=
  ⟨fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ _ hM => h ε A C₄ x₄ hε hε1 hA hC₄ hM⟩,
   fun ⟨c', hc', h⟩ => ⟨c', hc', fun ε A C₄ x₄ hε hε1 hA hC₄ hM => h ε A C₄ x₄ hε hε1 hA hC₄ zeroDensityBox hM⟩⟩

theorem chain6AtFinal_iff_closed : Chain6AtFinal ↔ Chain6AtClosed :=
  ⟨fun ⟨Cord, hC, h⟩ => ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ _ hM =>
      h eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM⟩,
   fun ⟨Cord, hC, h⟩ => ⟨Cord, hC, fun eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ hM =>
      h eD eL A K cHH eK eW KW ε C₄ x₄ hε hε4 hA hC₄ zeroDensityBox hM⟩⟩

example : AnalyticEndFinal := final_iff_closed.2 analyticEndClosed
example : AnalyticConclusionCompatible := finalTied_iff_closedTied.2 analyticEndClosedTied
example : Chain6AtFinal := chain6AtFinal_iff_closed.2 chain6AtClosed




end Formalism.L2.GlobalTheoryTheory.MergeGL2b
