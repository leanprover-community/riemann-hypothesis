module

public import Mathlib.RingTheory.Localization.FractionRing
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Formalism.ConjugateSelfDual.Statement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.IntRestBall

open GlobalTheory.TwAll

theorem span_inf_of_span_top {O V : Type} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V] (B : Submodule O V)
    (hB : Submodule.span (FractionRing O) (B : Set V) = ⊤) (W : Submodule (FractionRing O) V)
    (M : Submodule O V) (hM : ∀ f, f ∈ M ↔ f ∈ B ∧ f ∈ W) :
    Submodule.span (FractionRing O) (M : Set V) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    exact fun f hf => ((hM f).1 hf).2
  · intro f hf
    have h1 : f ∈ Submodule.span (FractionRing O) (B : Set V) := hB ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors O) (FractionRing O) (B : Set V) f h1
    rw [Submodule.span_eq] at ht
    have e : t • f = (algebraMap O (FractionRing O) t) • f := by
      rw [algebraMap_smul]; rfl
    have hne : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors t.2
    have h2 : t • f ∈ M := (hM _).2 ⟨ht, e ▸ W.smul_mem _ hf⟩
    have h3 := (Submodule.span (FractionRing O) (M : Set V)).smul_mem
      (algebraMap O (FractionRing O) t)⁻¹ (Submodule.subset_span h2)
    rwa [e, smul_smul, inv_mul_cancel₀ hne, one_smul] at h3

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  {Y : NExp D.R D.host D.what₂ D.LL0 N X} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

end GlobalTheory.IntRestBall
