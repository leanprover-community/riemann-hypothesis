module

public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingEquivariantGoodEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingEquivariantNotGoodEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionPreservesIntegralCuspFormsStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem GlobalTheory.geoAct_of_eqAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), IsInfFam R.θ → R.models_HW → TieIn T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → (∀ i σ, GoodEmb T.Q.c σ → ∀ hV, EqAt T R κ (O i) σ hV (T.cE ((i : ℕ) + 1) σ)) → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hθ hm ht hp he i
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  have hlift : ∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k := fun g =>
    ((hp i).2.lift.lev g).imp fun _ h => h.1
  have hs : GoodEmb T.Q.c (O i).s0 := by
    have e : (O i).s0 = T.toCore.σ₀ := sOv_eq T.toCore (O i).c' (O i).hle
    rw [e]
    exact T.toCore.good_σ₀
  obtain ⟨ρC, hρ⟩ := GlobalTheory.T.exists_level_action_cusp_form_representation T κ i (O i).lev2 ht.laws hact
    (fun g f hf => (hlift g).elim fun k hk =>
      (he i (O i).s0 hs (O i).hV g k hk f hf).1)
  refine ⟨ρC, fun σ g f => ?_, fun g f hf => ?_⟩
  · by_cases hσ : GoodEmb T.Q.c (res T σ)
    · exact GlobalTheory.T.cuspFormReading_equivariant_good_embedding T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
    · exact GlobalTheory.T.cuspFormReading_equivariant_not_good_embedding T R κ v₀ O hθ hm ht i hlift (he i) ρC hρ σ hσ g f
  · exact GlobalTheory.T.level_action_preserves_integral_cusp_forms T κ i (O i).lev2 ht.laws hact g f (ρC g f) (hρ g f) hf
