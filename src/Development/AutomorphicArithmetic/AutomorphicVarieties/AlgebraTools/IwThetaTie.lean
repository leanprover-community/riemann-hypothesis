module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.evaluation_unit_factor {A H E : Type} [CommRing A] [Semiring H] [Algebra A H] [Semiring E] [Algebra A E]
    (ev : H →ₐ[A] E) (a y z : H) (c : A) (u v w : Eˣ) (h : a * y = c • z) (hy : ev y = v) (hz : ev z = w)
    (hw : w = u * v) : ev a = c • (u : E) := by
  have h' := congrArg ev h
  rw [map_mul, map_smul, hy, hz, hw, Units.val_mul, ← smul_mul_assoc] at h'
  exact (Units.mul_left_inj _).1 h'

theorem UpperTheory.V.AlgebraTools.thetaTie :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∀ (b : UpperTheory.V.AlgebraTools.Hk.Bern n (resCard k : A) (HkAlg A (iwC k n ⊤))) (ev : HkAlg A (iwC k n ⊤) →ₐ[A] Module.End A (fixd ρ (iwC k n ⊤))) (θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n ⊤)))ˣ), (∀ g, ev (hT A (iwC k n ⊤) g) = hk ρ (iwC k n ⊤) g) → (∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n ⊤))) = hk ρ (iwC k n ⊤) (diagT k (Fin n) t)) → (∀ i : Fin n, b.th (MvPolynomial.X i) * hT A (iwC k n ⊤) (pw x (fund n i)) = ((resCard k : A) ^ (i : ℕ)) • hT A (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1)))) → ∀ i : Fin n, ev (b.th (MvPolynomial.X i)) = ((resCard k : A) ^ (i : ℕ)) • (θ (Pi.mulSingle i x) : Module.End A (fixd ρ (iwC k n ⊤))) := by
  intro k _ _ _ _ n A M _ _ _ ρ x hx _ b ev θ hev hθ hb i
  have hx1 : valuation k (x : k) ≤ 1 := by
    obtain ⟨p, -, hp⟩ := hx
    rw [← hp]
    exact p.2
  have hdom : ∀ m : ℕ, Dom (fun j : Fin n => x ^ fund n m j) := by
    intro m j l hjl
    have hjl' : (j : ℕ) ≤ (l : ℕ) := hjl
    simp only [fund]
    by_cases h1 : (l : ℕ) < m
    · have h2 : (j : ℕ) < m := lt_of_le_of_lt hjl' h1
      simp [h1, h2]
    · by_cases h2 : (j : ℕ) < m
      · simpa [h1, h2] using hx1
      · simp [h1, h2]
  have hsplit : (fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j)
      = Pi.mulSingle i x * (fun j : Fin n => x ^ fund n (i : ℕ) j) := by
    funext j
    simp only [fund, Pi.mul_apply]
    by_cases hj : j = i
    · subst hj
      simp
    · have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hj (Fin.ext h)
      rw [Pi.mulSingle_eq_of_ne hj, one_mul]
      by_cases h : (j : ℕ) < (i : ℕ)
      · have h' : (j : ℕ) < (i : ℕ) + 1 := by omega
        simp [h, h']
      · have h' : ¬ (j : ℕ) < (i : ℕ) + 1 := by omega
        simp [h, h']
  refine UpperTheory.V.AlgebraTools.evaluation_unit_factor ev _ _ _ _ _ (θ fun j : Fin n => x ^ fund n (i : ℕ) j)
    (θ fun j : Fin n => x ^ fund n ((i : ℕ) + 1) j) (hb i) ?_ ?_ ?_
  · exact (hev _).trans (hθ _ (hdom _)).symm
  · exact (hev _).trans (hθ _ (hdom _)).symm
  · rw [hsplit]
    exact map_mul θ _ _
