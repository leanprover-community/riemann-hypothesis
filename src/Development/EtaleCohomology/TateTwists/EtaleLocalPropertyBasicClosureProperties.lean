module

public import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosure
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.LocBasicPf

theorem loc_top (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, (Scheme.etaleTopology).top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : Loc U P)
    (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, (Scheme.etaleTopology).intersection_covering hS hT,
    fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

theorem loc_pull (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S.pullback k, (Scheme.etaleTopology).pullback_stable k hS,
    fun V g hg => hSP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hSP⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := by
        intro Y Z f hf g W' k
        simpa [Category.assoc] using hf W' (k ≫ g) }
  refine ⟨R, ?_, fun W h hR => by simpa using hR W (𝟙 W)⟩
  refine (Scheme.etaleTopology).transitive hS R ?_
  intro Y f hf
  obtain ⟨T, hT, hTP⟩ := hSP Y f hf
  refine (Scheme.etaleTopology).superset_covering ?_ hT
  intro Z k hk W' k'
  have := hTP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_finset (U : Scheme.{0}) (ι : Type) (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_top U _ (fun V g i hi => by simp at hi)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  haveI := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U ι P h Finset.univ) (fun V g hg i => hg i (Finset.mem_univ i))

theorem loc_empty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

end LateralTheory.EtaleFoundations.LocBasicPf

open LateralTheory.EtaleFoundations.LocBasicPf in
theorem LateralTheory.EtaleFoundations.etale_local_property_basic_closure_properties : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure :=
  ⟨loc_top, loc_mono, loc_and, loc_pull, loc_trans, fun U ι _ P h => loc_finite U ι P h,
    fun U _ P => loc_empty U P⟩
