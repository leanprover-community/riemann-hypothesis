module

public import Development.WeilBound.CoreStatements.ThetaDilations.IsOpenCoset
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureLinearChangeStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatumStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.IwasawaDecompositionAdelicSL2Statement

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v => mul_mem (hx v) (hy v)

theorem oh_nat (N : ℕ) : (N : A F) ∈ Oh F := by
  induction N with
  | zero => exact fun v => by rw [Nat.cast_zero]; exact zero_mem _
  | succ n ih => exact fun v => by rw [Nat.cast_succ]; exact add_mem (ih v) (one_mem _)

def LN (F ι : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  zero_mem' := fun _ => ⟨0, fun _ => zero_mem _, (mul_zero _).symm⟩
  add_mem' := fun ha hb i => by
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨y', hy', e'⟩ := hb i
    exact ⟨y + y', fun v => add_mem (hy v) (hy' v), by rw [Pi.add_apply, e, e', mul_add]⟩
  neg_mem' := fun ha i => by
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, fun v => neg_mem (hy v), by rw [Pi.neg_apply, e, mul_neg]⟩

theorem co_LN {N : ℕ} (hN : 0 < N) : CO (LN F ι N) := by
  obtain ⟨-, -, -, h1, -, -, -, -, -, h2⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have e : (LN F ι N : Set (ι → A F)) = Set.univ.pi fun _ => (fun y => (N : A F) * y) '' Oh F := by
    ext x
    exact ⟨fun h i _ => (h i).imp fun y hy => ⟨hy.1, hy.2.symm⟩, fun h i => (h i trivial).imp fun y hy => ⟨hy.1, hy.2.symm⟩⟩
  refine ⟨e ▸ isCompact_univ_pi fun _ => h1.image (continuous_const.mul continuous_id), ?_⟩
  have e' : (LN F ι N : Set (ι → A F)) = ⋂ i, (fun x => x i) ⁻¹' {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
    ext x; rw [Set.mem_iInter]; rfl
  exact e' ▸ isOpen_iInter_of_finite fun i => (h2 N hN).preimage (continuous_apply i)

end PositivityTheory.PlacePermOperatorBicommutantSpan
