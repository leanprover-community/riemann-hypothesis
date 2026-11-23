module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.divC_of :
    DivC := by
  intro S A B _ _ _ _ hA c hc
  obtain ⟨hfin, hflat, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA c hc
  have hmon : IsMonHom (mulN A c) := by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow]
    exact GlobalTheory.AbLaw.MulN.isMonHom_mulA A c
  have hqc : QuasiCompact (mulN A c).left := inferInstance
  have key : ∀ ν : A ⟶ B, IsMonHom ν → mulN A c ≫ ν = ν ^ c := by
    intro ν _
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.pow_comp, Category.id_comp]
  have hker : ∀ (T : Over S) (g : T ⟶ A), g ≫ mulN A c = g ^ c := by
    intro T g
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
  refine ⟨fun h hh htors => ?_, fun ν ν' hν hν' heq => ?_⟩
  · obtain ⟨⟨ψ, hψ, hcomp⟩, _⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S A A B (mulN A c) h
      hmon hh hflat hsurj hqc (fun T x hx => htors T x (by rw [← hker]; exact hx))
    exact ⟨ψ, hψ, by rw [← key ψ hψ, hcomp]⟩
  · obtain ⟨_, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective S A A A (mulN A c) (mulN A c)
      hmon hmon hflat hsurj hqc (fun _ _ hx => hx)
    rw [← cancel_epi (mulN A c), key ν hν, key ν' hν', heq]
