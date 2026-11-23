module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModOfInjectiveIntertwining
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionMemAdjoinCapOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_inter {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (T : Module.End ℂ M) (T' : Module.End ℂ N) (h : ∀ x, f (T x) = T' (f x))
    (p : Polynomial ℂ) (x : M) : f (Polynomial.aeval T p x) = Polynomial.aeval T' p (f x) :=
  _root_.UpperTheory.Reformulated.B.Qe22.aeval_inter f T T' h p x

theorem UpperTheory.siegelLevi_block_aeval_stable :
    ∀ (K : Type) [Field K] [NumberField K] (a n : ℕ) (e : Fin a ↪ Fin n) (Γ : Set (AdelicGLn.AdelicGL K n)) (S Z : Submodule ℂ (archSmooth K n)) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι), (∀ ψ ∈ Z, ∀ g ∈ Γ, ∀ m, ψ.1 (g * emb e m) = 0) → (∀ τ u, AlgMod S Z (archCapBlock D e τ u)) → Centre (slSp e Γ S) := by
  intro K _ _ a n e Γ S Z ι _ D hZ hS z hz
  refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ {x | ∃ τ u, x = capOp D a τ u} ?_ ?_ _ (UpperTheory.centerU_action_mem_adjoin_capOp K a ι D z hz)
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨σ, v, rfl⟩
    exact Zc_comm (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D τ u) (UpperTheory.qdet_generates_universalEnveloping_centre K a ι D σ v)
  · rintro _ ⟨τ, u, rfl⟩
    obtain ⟨p, hp, hpS⟩ := hS τ u
    refine ⟨p, hp, fun x hx => ?_⟩
    have hle : slSp e Γ S ≤ LinearMap.ker (Polynomial.aeval (capOp D a τ u) p) := by
      refine Submodule.span_le.2 ?_
      rintro φ ⟨ψ, hψ, g, hg, hφ⟩
      obtain ⟨f, hf, hl⟩ := UpperTheory.exists_restriction_blockEmbedding_intertwines_lie K a n e g
      have hfφ : φ = f ψ := Subtype.ext (funext fun m => (hφ m).trans (hf ψ m).symm)
      have hgen : ∀ i j y, f (gen D (lam K n) τ (e i) (e j) y) = gen D (lam K a) τ i j (f y) := fun i j y =>
        gen_inter D (lam K n) (lam K a) τ (e i) (e j) i j (f ∘ₗ LinearMap.applyₗ y) (LinearMap.applyₗ (f y))
          fun t => by
            change f (lam K n (Matrix.single (e i) (e j) t) y) = lam K a (Matrix.single i j t) (f y)
            rw [← matrixExtendByZero_single, hl]
      have hq : ∀ y, f (archCapBlock D e τ u y) = capOp D a τ u (f y) :=
        UpperTheory.algMod_of_injective_intertwining _ _ a f _ _ hgen u
      change Polynomial.aeval (capOp D a τ u) p φ = 0
      rw [hfφ, ← aeval_inter f _ _ hq]
      exact Subtype.ext (funext fun m => (hf _ m).trans (hZ _ (hpS ψ hψ) g hg m))
    exact hle hx
