module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameCfgRefl
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Formalism.LocalToGlobal.Columns.HeckeInert
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAlgebraicSetHeckeFieldsSplitStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteColumnConfigurationsWitnessesStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld

theorem heckeFields_of (hF : ∀ (P : Pre) (f : Top.Fr P) (F F₀ : IntermediateField ℚ ℂ) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)),
  ∃ (n : ℕ) (Wt : Fin n → Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0),
    (∀ i, (Wt i).1.fields.Ok ∧ (Wt i).2.2.Ok) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → B.toPre = P → HEq I.C f → B.KsC = F →
      B.fixedCoefficientFieldInComplex = F₀ → HEq (Set.range I.xi) Ξ → ∃ i, GlobalTheory.Mem.HFld.SameCfg B px I (Wt i).1 (Wt i).2.1 (Wt i).2.2) (hT : ∀ (B0 : Base) (px0 : PreX B0.toPre) (I0 : Col2.ColIn B0 px0), B0.fields.Ok → I0.Ok →
  ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → GlobalTheory.Mem.HFld.SameCfg B px I B0 px0 I0 →
      (∀ z ∈ s, z ∈ B.LLC) → ∀ a : I.ι,
        Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
          ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅) :
    ∃ So : ∀ P : Pre, Top.Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ,
  (∀ P f F F₀ Ξ, ∀ z ∈ So P f F F₀ Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok →
    (∀ z ∈ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC) → ∀ a : I.ι,
      Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
        ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  classical
  choose n Wt hWok hWcov using hF
  choose s hsalg hs using hT
  refine ⟨fun P f F F₀ Ξ => Finset.univ.biUnion fun i : Fin (n P f F F₀ Ξ) =>
    s (Wt P f F F₀ Ξ i).1 (Wt P f F F₀ Ξ i).2.1 (Wt P f F F₀ Ξ i).2.2 (hWok P f F F₀ Ξ i).1 (hWok P f F F₀ Ξ i).2, ?_, ?_⟩
  · intro P f F F₀ Ξ z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hz
    exact hsalg _ _ _ _ _ z hi
  · intro B px I hB hI hS a
    obtain ⟨i, hi⟩ := hWcov B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi) B px I hB hI rfl HEq.rfl rfl rfl HEq.rfl
    exact hs _ _ _ _ _ B px I hB hI hi (fun z hz => hS z (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hz⟩)) a

theorem heckeFields :
    ∃ So : ∀ P : Pre, Top.Fr P → IntermediateField ℚ ℂ → IntermediateField ℚ ℂ → Set (Formalism.L2.Host.HChar P.host.E) → Finset ℂ,
  (∀ P f F F₀ Ξ, ∀ z ∈ So P f F F₀ Ξ, IsAlgebraic ℚ z) ∧
  ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok →
    (∀ z ∈ So B.toPre I.C B.KsC B.fixedCoefficientFieldInComplex (Set.range I.xi), z ∈ B.LLC) → ∀ a : I.ι,
      Formalism.L2.Col.HeckeFieldsInAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
        ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeFieldsInAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ :=
  heckeFields_of GlobalTheory.T.exists_finite_columnConfigurations_witnesses GlobalTheory.T.exists_finite_algebraic_set_heckeFields_split

end GlobalTheory.Mem.HFld

end
