module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.LocGL

section Rad

variable {R S : Type} [CommRing R] [CommRing S] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem map_mem_unipRad_of_ringHom (f : R →+* S) {e : (Σ a, m a) ≃ n} {g : GL n R} (hg : g ∈ unipRad R e) :
    GeneralLinearGroup.map f g ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [mem_parab.1 h1 i j hij, map_zero]
  · show f ((g : Matrix n n R) _ _) = _
    rw [h2 a i j]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

end Rad

theorem isCuspidal_comp_generalLinearGroupMap {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi : Continuous i.symm) {n : Type} [Fintype n]
    [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (h : IsCuspidal π) : IsCuspidal (π.comp (GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  set M := GeneralLinearGroup.map (n := n) i.symm.toRingHom with hM
  have hc : Continuous M :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  refine ⟨fun v => (h.1 v).preimage hc, fun s d e he => ?_⟩
  have hmem : ∀ u ∈ unipRad k' e, M u ∈ unipRad k e := fun u hu => map_mem_unipRad_of_ringHom _ hu
  have hsurj : ∀ w ∈ unipRad k e, ∃ u ∈ unipRad k' e, M u = w := fun w hw =>
    ⟨GeneralLinearGroup.map i.toRingHom w, map_mem_unipRad_of_ringHom _ hw,
      Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩
  have hinj : Function.Injective M := fun x y hxy => Units.ext (Matrix.ext fun a b =>
    i.symm.injective (congrArg (fun g : GL n k => (g : Matrix n n k) a b) hxy))
  have hne : unipRad k e ≠ ⊥ := fun hb => he ((Subgroup.eq_bot_iff_forall _).2 fun u hu =>
    hinj ((((Subgroup.eq_bot_iff_forall _).1 hb) _ (hmem u hu)).trans (map_one M).symm))
  have h1 : twKer (π.comp M) (unipRad k' e) 1 = twKer π (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨M u, hmem u u.2⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u', hu', hu⟩ := hsurj u u.2
      exact ⟨⟨u', hu'⟩, v, by simp [hu]⟩
  exact Submodule.Quotient.subsingleton_iff.2 (h1 ▸ Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne))

end GlobalTheory.LocGL
