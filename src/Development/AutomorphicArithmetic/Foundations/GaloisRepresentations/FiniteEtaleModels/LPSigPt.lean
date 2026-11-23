module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lSigPt_holds :
    LSigPt := by
  intro I W Ω _
  haveI : Unique (sp Ω) := inferInstanceAs (Unique (PrimeSpectrum Ω))
  constructor
  · rintro ⟨i, x⟩ ⟨j, x'⟩ h
    have h' : x ≫ Sigma.ι (fun _ : I => W) i = x' ≫ Sigma.ι (fun _ : I => W) j := h
    have e : (Sigma.ι (fun _ : I => W) i) (x default) = (Sigma.ι (fun _ : I => W) j) (x' default) := by
      have := congrArg (fun f : sp Ω ⟶ _ => f default) h'
      simpa using this
    have e2 := (sigmaι_eq_iff _ _ _ _ _).mp e
    obtain ⟨rfl⟩ : i = j := congrArg Sigma.fst e2
    have : x = x' := (cancel_mono (Sigma.ι (fun _ : I => W) i)).mp h'
    rw [this]
  · intro y
    obtain ⟨i, w, hw⟩ := (sigmaOpenCover fun _ : I => W).exists_eq (y default)
    have hr : Set.range y ⊆ Set.range (Sigma.ι (fun _ : I => W) i) := by
      rintro _ ⟨p, rfl⟩
      rw [Subsingleton.elim p default]
      exact ⟨w, hw⟩
    exact ⟨(i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y hr), IsOpenImmersion.lift_fac _ _ _⟩
