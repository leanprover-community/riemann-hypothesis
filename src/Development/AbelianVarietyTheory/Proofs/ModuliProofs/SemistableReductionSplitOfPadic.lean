module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianModelSplitSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SS

theorem semistablePol_of_padic : GlobalTheory.Published.SemistableReductionSt → GlobalTheory.SS.SemistablePol := by
  intro H V K _ _ _ _ _ _ _ _ hfin A
  obtain ⟨p, hp, K₀, e, e₀, hK₀, he⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.1 V K hfin
  obtain ⟨P, ψ, hψ⟩ : ∃ (P : PolAV (Sp K₀)) (ψ : P.A.left ⟶ A.A.left),
      IsGrpPullback P.A A.A (spMap e.toRingHom) ψ := by
    obtain ⟨P', g, hg, -, hm, -⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap e.toRingHom) A
    refine ⟨P', g, hg, fun T x y x₀ y₀ hx hy => ?_⟩
    rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hg.w y), ← hm]
    rfl
  obtain ⟨K', h, hloc, hK', G, gG, hG, hE, φ, hφ⟩ :=
    GlobalTheory.exists_semiAbelian_model_split_specialFibre H p K₀ P
  obtain ⟨hdvr, hfr, hc, f, hf, hlf, hfx⟩ := GlobalTheory.completeDVR_eq_integralClosure_padicInt.2 p K₀ K' h hK'
  letI aV : Algebra V (integralClosure ℤ_[p] K') := (f.comp e₀.toRingHom).toAlgebra
  letI aK : Algebra K K' := ((IntermediateField.inclusion h).toRingHom.comp e.toRingHom).toAlgebra
  refine ⟨integralClosure ℤ_[p] K', K', inferInstance, inferInstance, hdvr, inferInstance, aV, inferInstance, aK, hfr,
    ?_, ?_, ?_, hc, G, gG, ?_, hG, hE⟩
  · ext1 x
    change ((f (e₀ x) : integralClosure ℤ_[p] K') : K') = IntermediateField.inclusion h (e (algebraMap V K x))
    rw [hfx, he]
  · exact RingHom.Finite.comp hf (RingHom.Finite.of_surjective _ e₀.surjective)
  · haveI : IsLocalHom e₀.toRingHom := isLocalHom_of_leftInverse e₀.symm.toRingHom e₀.left_inv
    exact RingHom.isLocalHom_comp f e₀.toRingHom
  · obtain ⟨i, hi, -⟩ := grpPullback_iso
      ((hφ.comp hψ).congr (GlobalTheory.SplitReduction.spMap_comp _ _) rfl)
      (isGrpPullback_pullback A.A (spMap (algebraMap K K')))
    exact ⟨i, hi⟩

end GlobalTheory.SS
