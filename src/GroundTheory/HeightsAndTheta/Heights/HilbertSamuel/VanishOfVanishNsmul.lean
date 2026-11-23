module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsLast
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTail
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsRest
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem vanish_of_vanish_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (N : K → ℤ) {q : ℕ}
    (hq : 1 ≤ q)
    (h : ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + (c * q) • N) 1))
    (e : K → ℤ) : ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) := by
  choose c₀ hc₀ using fun r : ℕ => h (e + r • N)
  refine ⟨((Finset.range q).sup c₀ + 1) * q, fun c hc => ?_⟩
  have hr : c % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  have h1 : c₀ (c % q) ≤ (Finset.range q).sup c₀ := Finset.le_sup (f := c₀) hr
  have h2 : (Finset.range q).sup c₀ + 1 ≤ c / q := (Nat.le_div_iff_mul_le (by omega)).mpr hc
  have h3 := hc₀ (c % q) (c / q) (by omega)
  have e' : e + (c % q) • N + (c / q * q) • N = e + c • N := by
    rw [add_assoc, ← add_smul, Nat.mod_add_div' c q]
  rwa [e'] at h3

theorem KleimanVarietyH1Generation.proof (hK : KH.KAmpStatement) (hDev : H1VanishingDevissage.Statement)
    (hGen : GenerationOfH1Vanishing.Statement) : KleimanVarietyH1Generation.Statement := by
  intro F _ K _ _ ι _ _ I Q α b a hI hQ hN hb ha
  refine hGen F K ι Q _ inferInstance (hDev F K ι Q _ inferInstance fun P hP hQP e => ?_)

  obtain ⟨D, hKD, hD⟩ := Targets.ContractMixedField.exists_dim hP
  have hPd : IsProjVarF P (D - Fintype.card K) := ⟨hP, by rw [hD, Nat.sub_add_cancel hKD]⟩
  have hNP : KH.NefOnF I P α := fun W hW hPW => hN W hW (hQP.trans hPW)

  obtain ⟨q, hq, -, hvan⟩ := hK F K ι I P _ α b a hI hPd hNP hb ha
  exact vanish_of_vanish_nsmul _ _ hq hvan e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
