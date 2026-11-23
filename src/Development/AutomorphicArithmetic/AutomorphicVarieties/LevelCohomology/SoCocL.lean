module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.CobDown
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoCobPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLocTors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.soCocL : ∀ CK : ℝ, LemmaK CK → GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (c : HV.Coef l) (ψ : G k Ω →* c.Oˣ), IsOpen (ψ.ker : Set (G k Ω)) → ∀ e : ℕ, 1 ≤ e → ∀ z : G k Ω → c.O, Coc (Chr.Psi l e ψ)⁻¹ z → Alg.AdicCont (maximalIdeal c.O) z → (∀ v : HeightOneSpectrum (𝓞 k), ((l : ℕ) : 𝓞 k) ∈ v.asIdeal → ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A)) → CobOn (Chr.Psi l e ψ)⁻¹ z ⊤ := by
  intro CK hK pt fK tK lf lt le k Ω _ _ _ _ _ l hl c ψ ho e he z hz hc hl
  have key : ∀ (v : HeightOneSpectrum (𝓞 k)) (A : ValuationSubring Ω), IsPlaceOver A v →
      CobOn (Chr.Psi l e ψ)⁻¹ z (Dec (F := k) A) := fun v A hA => by
    by_cases hv : ((l : ℕ) : 𝓞 k) ∈ v.asIdeal
    · obtain ⟨A', hA', h⟩ := hl v hv
      exact So.cobPlace k Ω c.O _ z hz v A' A hA' hA h
    · rw [Chr.Psi_inv] at hz ⊢
      have ho' : IsOpen ((ψ⁻¹).ker : Set (G k Ω)) := by
        have : (ψ⁻¹).ker = ψ.ker := by
          ext g
          simp [MonoidHom.mem_ker]
        rwa [this]
      exact So.locTors lf lt le k Ω l c.O ψ⁻¹ ho' _ (by omega) (by omega) v A hA hv z hz hc
  refine So.soCoc CK hK pt fK tK k Ω l c ψ ho e he z hz hc (fun A => ?_) fun A hA => ?_
  · by_cases h : A = ⊤
    · rw [((places k Ω l A).2.1 h).1]
      refine cobOn_of_eq_zero _ fun g hg => ?_
      rw [Subgroup.mem_bot.1 hg]
      simpa using hz 1 1
    · obtain ⟨v, hv⟩ := (places k Ω l A).1 h
      exact (key v A hv).mono (Ine_le_Dec A)
  · obtain ⟨v, hv⟩ := (places k Ω l A).1 fun h => ((places k Ω l A).2.1 h).2 hA
    exact key v A hv
