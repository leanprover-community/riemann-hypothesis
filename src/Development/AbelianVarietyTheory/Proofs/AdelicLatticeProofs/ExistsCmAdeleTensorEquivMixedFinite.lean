module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpaceStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.AdeleCM

theorem exists_adele_tensor_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E); ∃ Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (1 ⊗ₜ[F] x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) (AlgHom.id F E) y ∈ AddSubgroup.closure {y : FiniteAdeleRing (𝓞 F) F ⊗[F] E | ∃ a ∈ {a : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F}, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ (v : HeightOneSpectrum (𝓞 F)) (ε : AdeleRing (𝓞 F) F), ε.1 = 0 → ε.2 v = 1 → (∀ v', v' ≠ v → ε.2 v' = 0) → (Φ (ε ⊗ₜ[F] 1)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (ε ⊗ₜ[F] 1)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AdeleRing (𝓞 F) F)ˣ, Φ ((a : AdeleRing (𝓞 F) F) ⊗ₜ[F] 1) = x := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI t1 : TopologicalSpace (AdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F ⊗[F] E)
  letI t2 : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  letI t3 : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  obtain ⟨e, he, -, hec⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  obtain ⟨ι, hι1, hι2, hι3⟩ := GlobalTheory.AdeleBaseChange.exists_tensor_finiteAdele_equiv F E
  have hιc := GlobalTheory.AdeleBaseChange.continuous_symm_finite F E ι hι2
  obtain ⟨θ, hθ1, hθc, hθ3⟩ := GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace F E σ hF hE h2 hσ
  have he1 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).1 = a.1 ⊗ₜ[F] x :=
    fun a x => (he _).1.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  have he2 : ∀ (a : AdeleRing (𝓞 F) F) (x : E), (e (a ⊗ₜ[F] x)).2 = a.2 ⊗ₜ[F] x :=
    fun a x => (he _).2.trans (Algebra.TensorProduct.map_tmul _ _ _ _)
  let Φ : AdeleRing (𝓞 F) F ⊗[F] E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E) :=
    e.trans (RingEquiv.prodCongr θ ι)
  have hΦ : ∀ z, Φ z = (θ (e z).1, ι (e z).2) := fun z => rfl
  refine ⟨Φ, fun x => ?_, fun y => ?_, fun v ε h0 h1 hv => ⟨?_, fun P => ?_⟩, ?_, fun x hx2 hx1 => ?_⟩
  · rw [hΦ, he1, he2]
    exact Prod.ext (hθ1 x) (hι1 x)
  · rw [← (he y).2]
    exact hι2 (e y).2
  · rw [hΦ, he1, h0]
    simp
  · rw [hΦ, he2]
    exact hι3 v ε.2 h1 hv P
  · have : (Φ.symm : _ → _) = fun w => e.symm (θ.symm w.1, ι.symm w.2) := rfl
    rw [this]
    exact hec.comp ((hθc.comp continuous_fst).prodMk (hιc.comp continuous_snd))
  · obtain ⟨a, ha⟩ := hθ3 (Units.map (RingHom.fst (mixedSpace E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x) hx1
    refine ⟨⟨((a : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)),
      ((a⁻¹ : (InfiniteAdeleRing F)ˣ), (1 : FiniteAdeleRing (𝓞 F) F)), ?_, ?_⟩, ?_⟩
    · exact Prod.ext a.mul_inv (mul_one _)
    · exact Prod.ext a.inv_mul (mul_one _)
    · rw [hΦ, he1, he2]
      refine Prod.ext ha ?_
      rw [hx2]
      exact map_one ι

end GlobalTheory.AdeleCM
