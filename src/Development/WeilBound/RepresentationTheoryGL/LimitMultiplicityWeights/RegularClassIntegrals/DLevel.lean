module

public import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DLevel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem level_of_mem {f : GAd σ J → ℂ} (hf : f ∈ CcAd σ J) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, b, hb, rfl⟩ := hx
    obtain ⟨V, hV, hVb⟩ := GlobalTheory.Orb.exists_biinvariant hb
    refine ⟨V.comap (projFin σ J), hV.preimage (continuous_projFin σ J), fun k hk hkf g => ?_⟩
    show a (projInf σ J (g * k)) * b (projFin σ J (g * k)) = a (projInf σ J g) * b (projFin σ J g)
    rw [map_mul, map_mul, mem_finPts.1 hkf, mul_one, (hVb _ hk _).2]
  | zero => exact ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h⟩ := hx
    obtain ⟨V, hV, h'⟩ := hy
    exact ⟨U ⊓ V, hU.inter hV, fun k hk hkf g => by
      simp only [Pi.add_apply, h k hk.1 hkf g, h' k hk.2 hkf g]⟩
  | smul c x _ hx =>
    obtain ⟨U, hU, h⟩ := hx
    exact ⟨U, hU, fun k hk hkf g => by simp only [Pi.smul_apply, h k hk hkf g]⟩

end MainStatements.WeightKernel.Dec.DLevel

theorem MainStatements.WeightKernel.Dec.level : MainStatements.WeightKernel.Dec.Level := by
  intro F E _ _ _ _ _ σ _ n J _ f hf
  exact MainStatements.WeightKernel.Dec.DLevel.level_of_mem hf

end
