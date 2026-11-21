import Mathlib
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CompanionTheory.Smooth

def linearFormStabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {g : G | l ∘ₗ ρ g = l}
  mul_mem' := by
    intro a b ha hb
    have ha' : l ∘ₗ ρ a = l := ha
    have hb' : l ∘ₗ ρ b = l := hb
    show l ∘ₗ ρ (a * b) = l
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ha', hb']
  one_mem' := by
    show l ∘ₗ ρ 1 = l
    rw [map_one]
    rfl
  inv_mem' := by
    intro a ha
    have ha' : l ∘ₗ ρ a = l := ha
    show l ∘ₗ ρ a⁻¹ = l
    conv_lhs => rw [← ha']
    rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem isOpen_linearForm_stabiliser {G V : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (hK : IsOpen (K : Set G)) (l : Module.Dual ℂ V)
    (hl : ∀ x ∈ K, l ∘ₗ ρ x = l) : IsOpen {g : G | l ∘ₗ ρ g = l} :=
  Subgroup.isOpen_mono (H₁ := K) (H₂ := linearFormStabiliser ρ l) (fun x hx => hl x hx) hK

end GlobalTheory.CompanionTheory.Smooth
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_functional_open_stabilizer : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → IsOpen {g : G | l ∘ₗ ρ g = l} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Smooth.isOpen_linearForm_stabiliser
