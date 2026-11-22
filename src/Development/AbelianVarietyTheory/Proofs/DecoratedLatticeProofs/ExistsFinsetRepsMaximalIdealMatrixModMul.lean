module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

noncomputable section

namespace GlobalTheory.LowerHecke.MaxReps

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

variable (k D A) in
def maxLat : AddSubgroup (Matrix D A k) where
  carrier := {ν | ∀ i a, valuation k (ν i a) < 1}
  add_mem' ha hb i a := by simpa using Valuation.map_add_lt _ (ha i a) (hb i a)
  zero_mem' i a := by simp
  neg_mem' ha i a := by simpa using ha i a

def mulLat (g : Matrix D D k) : AddSubgroup (Matrix D A k) where
  carrier := {x | ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ x = g * μ}
  add_mem' := by
    rintro _ _ ⟨μ, hμ, rfl⟩ ⟨μ', hμ', rfl⟩
    exact ⟨μ + μ', fun i a => by simpa using Valuation.map_add_lt _ (hμ i a) (hμ' i a),
      (Matrix.mul_add _ _ _).symm⟩
  zero_mem' := ⟨0, fun i a => by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨-μ, fun i a => by simpa using hμ i a, (Matrix.mul_neg _ _).symm⟩

end GlobalTheory.LowerHecke.MaxReps

end
