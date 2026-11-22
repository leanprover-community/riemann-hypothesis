module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

@[expose] public section

open MeasureTheory Topology Set
open scoped ENNReal ComplexConjugate

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

open GlobalTheory.CompanionTheory.SW.Core

variable {V : Type} [AddCommGroup V] [TopologicalSpace V]

def CO (L : AddSubgroup V) : Prop := IsCompact (L : Set V) ∧ IsOpen (L : Set V)

def ind (a : V) (L : AddSubgroup V) : V → ℂ := Set.indicator {x | x - a ∈ L} fun _ => (1 : ℂ)

omit [TopologicalSpace V] in
theorem ind_of_mem {a x : V} {L : AddSubgroup V} (h : x - a ∈ L) : ind a L x = 1 :=
  Set.indicator_of_mem (s := {x | x - a ∈ L}) h _

omit [TopologicalSpace V] in
theorem ind_of_not {a x : V} {L : AddSubgroup V} (h : x - a ∉ L) : ind a L x = 0 :=
  Set.indicator_of_notMem (s := {x | x - a ∈ L}) h _

section top

variable [IsTopologicalAddGroup V]

theorem isOpen_coset (a : V) {L : AddSubgroup V} (h : IsOpen (L : Set V)) : IsOpen {x | x - a ∈ L} :=
  h.preimage (continuous_id.sub continuous_const)

theorem lc_of_inv {f : V → ℂ} {L : AddSubgroup V} (h : IsOpen (L : Set V)) (hf : ∀ x, ∀ l ∈ L, f (x + l) = f x) :
    IsLocallyConstant f :=
  (IsLocallyConstant.iff_exists_open f).2 fun x => ⟨{y | y - x ∈ L}, isOpen_coset x h, by simp, fun y hy => by
    have := hf x _ hy
    rwa [add_sub_cancel] at this⟩

theorem sb_ind [T2Space V] (a : V) {L : AddSubgroup V} (h : CO L) : SB (ind a L) := by
  refine ⟨lc_of_inv h.2 fun x l hl => ?_, HasCompactSupport.intro (K := (fun y => y + a) '' L)
    (h.1.image (continuous_id.add continuous_const)) fun x hx => ind_of_not fun h' => hx ⟨_, h', by simp⟩⟩
  by_cases hx : x - a ∈ L
  · rw [ind_of_mem hx, ind_of_mem (by rw [add_sub_right_comm]; exact L.add_mem hx hl)]
  · rw [ind_of_not hx, ind_of_not fun h' => hx (by
      rw [add_sub_right_comm] at h'; exact (L.add_mem_cancel_right hl).1 h')]

end top

omit [AddCommGroup V] in
theorem sb_homeo {f : V → ℂ} (hf : SB f) (e : V ≃ₜ V) : SB (f ∘ e) :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

end PositivityTheory.PlacePermOperatorBicommutantSpan
