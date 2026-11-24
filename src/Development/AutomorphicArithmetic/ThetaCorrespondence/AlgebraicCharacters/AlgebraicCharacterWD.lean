module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaHecke
public import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ChIndep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.ContinuousRankOneRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Lit.CharWD GlobalTheory.Published
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands UpperTheory.V.W

theorem UpperTheory.Lit.CharWD.algebraicCharacterWD :
    GlobalArtinReciprocity → HeckeLAdicCharacterDeRham → DeRhamPotSemistable → AlgebraicCharacterWD := by
  intro hG hD hP E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ _ hμ hL w A h O _ _ _ Bw hj ξ hξ a ha
  have hc : Continuous (μ.comp (Dec (F := E) A).subtype) := hμ.comp continuous_subtype_val
  obtain ⟨η, hη, eη⟩ := locWD hG hD hP ι h Bw hj a ha _ hc _ (UpperTheory.V.Loc.laHecke h art hart ι χ n μ hL ⟨a, ha⟩)
  obtain ⟨-, hs, e⟩ := chIndep P AI hT ι h Bw hj _ η hc hη
  obtain ⟨ξ₀, -, hu, -⟩ := GlobalTheory.HeckeComp.main E χ w
  have hx : ξ = χ.loc w := (hu ξ hξ).trans (hu _ ⟨GlobalTheory.HeckeComp.smooth_loc χ w, fun _ => rfl⟩).symm
  haveI : Finite (Emb l w) := finite_contEmb w
  have key : (Units.map ι.toRingHom.toMonoidHom).comp η = ξ.comp a := by
    refine MonoidHom.ext fun σ => Units.ext ?_
    have h1 := hL.loc (a σ) _ (ha.glob art hart σ)
    have h2 : locPow ι n w (a σ) * ∏ᶠ τ : Emb l w, τ.1 (a σ : w.adicCompletion E) ^
        (-n ((ι.toRingHom.comp τ.1).comp (algebraMap E (w.adicCompletion E)))) = 1 := by
      unfold locPow
      rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finprod_eq_one_of_forall_eq_one fun τ => ?_
      rw [← zpow_add₀ ((map_ne_zero τ.1).2 (Units.ne_zero _))]
      simp
    change ι (η σ : Qbar l) = (ξ (a σ) : ℂ)
    rw [eη]
    change ι ((μ (σ : G E Ω) : Qbar l) * _) = _
    rw [h1, mul_assoc, h2, mul_one, RingEquiv.apply_symm_apply, hx]
  refine (e : _ = _).trans ?_
  congr 1
