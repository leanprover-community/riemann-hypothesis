module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped nonZeroDivisors Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace UpperTheory.Gal.TP.Skew

private lemma mem_one_iff {E : Type} [Field E] [NumberField E] (y : E) :
    y ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ y := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.2
  · intro h
    exact ⟨⟨y, h⟩, rfl⟩

private lemma form_one {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (y x : Fin n → E) : form σ (1 : Matrix (Fin n) (Fin n) E) y x = ∑ i, y i * σ (x i) := by
  simp [form, dotProduct]

theorem stdHerm : StdHerm := by
  intro F E _ _ _ _ _ σ hc B hP n
  have hint : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (σ x) := fun x h =>
    h.map (σ.toRingHom.toIntAlgHom)
  have hL : ∀ y : Fin n → E, y ∈ (stdSpc F E n).L ↔ ∀ i, IsIntegral ℤ (y i) := by
    intro y
    have : (stdSpc F E n).L = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := rfl
    rw [this, Submodule.mem_pi]
    exact forall_congr' fun i => by simp only [Set.mem_univ, true_imp_iff, mem_one_iff]
  have hs : ∀ i, (Pi.single i (1 : E) : Fin n → E) ∈ (stdSpc F E n).L := fun i =>
    (hL _).2 fun j => by
      by_cases e : j = i
      · subst e
        simpa using isIntegral_one
      · simpa [Pi.single_eq_of_ne e] using isIntegral_zero
  have hJ : ∀ w, (stdSpc F E n).J.map (B.emb w).1 = 1 := by
    intro w
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [stdSpc, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · have h' : ¬ j = i := fun e => h e.symm
      simp [h, h']
  · intro w
    rw [hJ]
    refine ⟨rfl, Matrix.fromCols 1 0, ?_⟩
    ext (i | i) (j | j)
    · simp only [Matrix.mul_one]
      simp [Matrix.mul_apply, Matrix.one_apply]
      by_cases e : i = j
      · simp [e]
      · have e' : ¬ j = i := fun h => e h.symm
        simp [e, e']
    all_goals first | exact i.elim0 | exact j.elim0
  · haveI : (stdSpc F E n).L.IsLattice E := by
      refine ⟨Submodule.fg_pi fun _ => ?_, ?_⟩
      · rw [Submodule.one_eq_span]
        exact Submodule.fg_span_singleton 1
      · intro s _ h
        exact (LinearIndependent.iff_fractionRing (𝓞 E) E).mp h
    refine ⟨?_⟩
    apply top_unique
    rw [← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact Submodule.subset_span (hs i)
  · intro y
    rw [hL]
    constructor
    · intro hy x hx
      rw [hL] at hx
      simp only [stdSpc, form_one]
      exact IsIntegral.sum _ fun i _ => (hy i).mul (hint _ (hx i))
    · intro h i
      have := h _ (hs i)
      simpa [stdSpc, form_one, Pi.single_apply] using this
  · intro w
    rw [hJ]
    refine ⟨by simp [stdSpc], by simp [stdSpc], fun x hx => ?_⟩
    simp only [stdSpc, Matrix.one_mulVec]
    exact (Complex.pos_iff.1 (Matrix.dotProduct_self_star_pos_iff.2 hx)).1
  · intro v
    exact absurd v.2 (by simp [hP])

end UpperTheory.Gal.TP.Skew

end
