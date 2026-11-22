module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Classical

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set ℂ) = ⊤

def Uniformization : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 →
    (∃ Λ : AddSubgroup ℂ, IsLat Λ ∧ g2 Λ = a ∧ g3 Λ = b) ∧
    ∀ Λ Λ' : AddSubgroup ℂ, IsLat Λ → IsLat Λ' → g2 Λ = a → g3 Λ = b → g2 Λ' = a → g3 Λ' = b →
      Λ = Λ'

def ThetaNormIndependent (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L₁ L₁' L₂ L₂', admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
    normSq D T (La D T L₁ L₁') (e N N' L₁ L₁') = normSq D T (La D T L₂ L₂') (e N N' L₂ L₂')

def th22U (D : D7) (T : Tor D) (e : FamE D) : Prop :=
  ∀ N N' L L', admitted D N N' L L' → ∀ x : VC D N N',
    normSq D T (La D T L L') (U D T x (e N N' L L')) = normSq D T (La D T L L') (e N N' L L')

def LinkThU : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ N N' L L', admitted D N N' L L' → ∀ G ∈ Th D (tor0 D cc δ) L L', ∀ x : VC D N N',
      normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (U D (tor0 D cc δ) x G) =
        normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') G

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
