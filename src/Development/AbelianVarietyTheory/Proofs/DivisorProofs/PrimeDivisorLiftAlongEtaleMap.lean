module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrExtensionOfEssentiallyEtaleLocalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdFracFunctionFieldMapOfEssentiallyEtaleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkMapFlatFormallyEtaleEssFiniteTypeOfEtaleResStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormOrderRationalPullbackOfEssentiallyEtaleStatement
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_lift : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hU y hy E hE
  obtain ⟨hfl, hfe, hft⟩ := GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open M W f U hU y hy
  obtain ⟨V', h, hdvr, hS, hcomap, het, hess⟩ := GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local (K := W.functionField)
    (K' := M.functionField) (R := W.presheaf.stalk (f y)) (S := M.presheaf.stalk y)
    (functionFieldMap f) (f.stalkMap y).hom hfl hfe hft
    (RingHom.ext fun a => functionFieldMap_algebraMap f y a) E.ring E.dvr (fun a => hE _ ⟨a, rfl⟩)
  have hc : ∀ a, Cartier.constFn (f ≫ p) a ∈ V' := fun a => by
    rw [← functionFieldMap_comp_constFn p f]
    exact h _ (E.const_mem a)
  have hess' : ((Cartier.constFn (f ≫ p)).codRestrict V' hc).EssFiniteType := by
    have e : (Cartier.constFn (f ≫ p)).codRestrict V' hc =
        ((functionFieldMap f).restrict E.ring V' h).comp E.const := by
      ext a
      simp [DivOver.const, ← functionFieldMap_comp_constFn p f]
    rw [e]
    exact E.essFiniteType.comp hess
  let E' : DivOver (f ≫ p) := ⟨V', hc, hdvr, hess'⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  have hdim := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hord := GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale M W p f E E' h hcomap het hess
  refine ⟨E', fun g hg => ?_, hord, fun η hη => GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale M W p f n hdim E E' h het hord η hη⟩
  obtain ⟨a, rfl⟩ := hg
  exact hS a

end GlobalTheory.EtaleKlt
