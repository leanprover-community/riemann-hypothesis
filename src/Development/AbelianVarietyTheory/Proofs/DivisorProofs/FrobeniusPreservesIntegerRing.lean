import Development.AbelianVarietyTheory.Definitions.Divisors.MaxWeightGL1EqOne
import BuildAid.ForwardExisting

section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem frobR_mem_intR (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) :
    ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  intro x hx
  have hx' : ((x : PadicAlgCl p)) ∈ Obar p := hx
  show ((frobR p K r x : Kn p K r) : PadicAlgCl p) ∈ Obar p
  have h : ((frobR p K r x : Kn p K r) : PadicAlgCl p) = frobK p K (x : PadicAlgCl p) := rfl
  rw [h, mem_Obar_iff, norm_map_GK]
  exact mem_Obar_iff.1 hx'

end GlobalTheory.LKLoc
end

open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_preserves_integer_ring : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), ∀ x ∈ intR p K r, frobR p K r x ∈ intR p K r := by
  atlas_forward_decl GlobalTheory.LKLoc.frobR_mem_intR
