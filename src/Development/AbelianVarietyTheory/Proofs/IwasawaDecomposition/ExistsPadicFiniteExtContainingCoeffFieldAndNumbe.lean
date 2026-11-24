module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section
namespace GlobalTheory.HeckeLocN

theorem exists_finExt_big (D : D7) (pl : PlSide D) (big : D.what₂.places.Pl → Finset ℂ) (w : D.what₂.places.Pl) :
    ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), (∀ x, (plEmb pl).emb w x ∈ F0.1) ∧
      ∀ z ∈ big w, (pl.ι w).symm z ∈ F0.1 := by
  classical
  let c := (plEmb pl).emb w
  let S : Finset (Loc.Om (D.what₂.places.resChar w)) := (big w).image (fun z => (pl.ι w).symm z)
  have h1 := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range c
  have h2 : FiniteDimensional ℚ_[D.what₂.places.resChar w]
      (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w)))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c) ⊔
      IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))),
      IntermediateField.finiteDimensional_sup _ _⟩, fun x => ?_, fun z hz => ?_⟩
  · exact (le_sup_left (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact (le_sup_right (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.HeckeLocN
