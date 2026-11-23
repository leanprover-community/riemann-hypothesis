module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Formalism.PadicSubsetSums.StableGradedCounts.DegreeOneSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.DzCong.CongruenceClosure

theorem isSplitAt_of_deg_one {E : Type} [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 E))
    (hf : v.asIdeal.inertiaDeg ℤ = 1) (he : v.asIdeal.ramificationIdx ℤ = 1) : IsSplitAt v := by
  classical
  have := v.isPrime
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have he' : v.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := by
    have := Ideal.ramificationIdx_tower (R := ℤ) (v.asIdeal.under (𝓞 (maximalRealSubfield E))) v.asIdeal
    rw [he] at this
    exact Nat.eq_one_of_mul_eq_one_left this.symm
  have hc := Formalism.IrreducibleCountingLemmas.Z.degree_one_split (maximalRealSubfield E) E h2 v.asIdeal v.ne_bot hf he'
  obtain ⟨P, Q, hne, hs⟩ := Set.ncard_eq_two.mp hc
  have hX : ∃ X ∈ (v.asIdeal.under (𝓞 (maximalRealSubfield E))).primesOver (𝓞 E), X ≠ v.asIdeal := by
    by_cases h : P = v.asIdeal
    · exact ⟨Q, hs ▸ Set.mem_insert_of_mem _ rfl, fun hQ => hne (h.trans hQ.symm)⟩
    · exact ⟨P, hs ▸ Set.mem_insert _ _, h⟩
  obtain ⟨X, hX, hXv⟩ := hX
  have hXb : X ≠ ⊥ := by
    rintro rfl
    have h0 : v.asIdeal.under (𝓞 (maximalRealSubfield E)) = ⊥ := hX.2.over.trans
      (Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ (𝓞 E)))
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot h0)
  have := hX.1
  refine ⟨⟨X, hX.1, hXb⟩, fun h => hXv (congrArg HeightOneSpectrum.asIdeal h), ?_⟩
  ext1
  exact hX.2.over.symm

theorem continuous_coeff_charpoly {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (n i : ℕ) :
    Continuous fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i := by
  have h : (fun M : Matrix (Fin n) (Fin n) K => M.charpoly.coeff i) =
      fun M => MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
        ((Matrix.charpoly.univ K (Fin n)).coeff i) := by
    funext M
    exact (Matrix.charpoly.univ_coeff_eval₂Hom (Fin n) (RingHom.id K) (fun ij : Fin n × Fin n => M ij.1 ij.2) i).symm
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp
    (continuous_pi fun ij => (continuous_apply ij.2).comp (continuous_apply ij.1))

end PositivityTheory.Rg.DzCong.CongruenceClosure

namespace PositivityTheory.Rg.DzCong

end PositivityTheory.Rg.DzCong

end
