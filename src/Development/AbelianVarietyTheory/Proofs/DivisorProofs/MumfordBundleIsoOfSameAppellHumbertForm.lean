module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsAddOfFactorProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishingBundleGenerated
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoOfSameFactor
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.TorusRM.LamAdd GlobalTheory.ProdUnifSq in
theorem GlobalTheory.TorusRM.lbIso_lam_of_same_form : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → IsProjOver A.hom →
    ∀ (M M' : LB A.left) (u : HolUnif A M g) (u' : HolUnif A M' g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), M.IsLB → M'.IsLB → u'.ex = u.ex →
    GlobalTheory.TorusRM.IsFactorAH u Hm χ → GlobalTheory.TorusRM.IsFactorAH u' Hm χ' → LBIso (abelian₂ A M) (abelian₂ A M') := by
  intro g A _ hA hP M M' u u' Hm χ χ' h1 h2 he f1 f2
  haveI : IsCommMonObj A := hA.comm
  have hl1 : (abelian₂ A M).IsLB := LB.isLB_linComb h1 _ _
  have hl2 : (abelian₂ A M').IsLB := LB.isLB_linComb h2 _ _
  have hPP : IsProjOver (A ⊗ A).hom := GlobalTheory.ProjSpace.isProjOver_pullback hP hP
  refine GlobalTheory.HolUnifSec.hasGen_of_periodic (A ⊗ A) (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) hPP _
    (LB.isLB_div hl2 hl1) (g + g)
    (GlobalTheory.SameFactor.divUnif (lamUnif u u rfl) (lamUnif u u' he) rfl)
    (fun _ => 1) (differentiable_const _) (fun _ => one_ne_zero) ?_
  intro l hl p z hz
  obtain ⟨hz2, hz1⟩ := (GlobalTheory.top_le_preimage_inf _ _ _).1 hz
  have hexl : (sqUnif A u).ex (z + l) = (sqUnif A u).ex z := by
    rw [(sqUnif A u).ex_add, ((sqUnif A u).ker l).2 hl, _root_.mul_one]
  have e1 := lam_shift u u rfl h1 f1 p.2 z l hl hz1
  have e2 := lam_shift u u' he h2 f2 p.1 z l hl hz2
  have n1 := (lamUnif u u rfl).fr_ne p.2 (z + l) (by rw [lamUnif_ex, hexl]; exact hz1)
  have n2 := (lamUnif u u' he).fr_ne p.1 (z + l) (by rw [lamUnif_ex, hexl]; exact hz2)
  show 1 * ((lamUnif u u' he).fr p.1 (z + l) * ((lamUnif u u rfl).fr p.2 (z + l))⁻¹) =
    1 * ((lamUnif u u' he).fr p.1 z * ((lamUnif u u rfl).fr p.2 z)⁻¹)
  rw [e1, e2]
  have q1 := Complex.exp_ne_zero (Q Hm z l)
  field_simp
