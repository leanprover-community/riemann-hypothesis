module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CentralOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrBwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrCochain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrFwd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrInv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DeRhamInjOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.LevelVal
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

open UpperTheory.V.Cj.A
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem dCo_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q) (w : (geo ho U Ξ).Om q)
    (hw : Corr U Ξ α w.1) (hd : (geo ho U Ξ).dOm q w = 0) : dCo (smLie Ξ) α = 0 := by
  have h := corrD E a ho U Ξ q _ _ hw
  rw [hd] at h
  exact (corrUniq E a ho U Ξ (q + 1)).1 _ 0 _ h (corr_zero U Ξ)

theorem UpperTheory.V.Cj.A.levCorr :
    LevCorr := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα hd => ?_, fun w hi hd hb => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    refine ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, ?_⟩
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [hd] at h
    exact (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)
  · obtain ⟨η, hη⟩ := corrBwd E a ho U Ξ q w
    have e : dCo (smLie Ξ) η = 0 := dCo_zero' ho U Ξ q η w hη hd
    have b := (corrBasic E a U Ξ _ _ _ hη).2 hb
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hη
    exact ⟨η, hη, ⟨c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hη).2 hi X) (c2 X)
      (centralOf E a _ (smLie Ξ) q η b (fun Y i _ => by rw [e]; rfl) X)⟩, e⟩
