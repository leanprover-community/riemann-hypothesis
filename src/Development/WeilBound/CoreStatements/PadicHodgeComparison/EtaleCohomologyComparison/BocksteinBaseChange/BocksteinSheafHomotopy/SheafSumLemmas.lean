module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.WeightedPowerFormIntegrability

open GlobalTheory.EtC

variable {R : Type} [CommRing R]

theorem isSheaf_types (G : Shv R) : Presieve.IsSheaf Scheme.etaleTopology (G.obj ⋙ forget _) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 G.property)

theorem sec_empty (G : Shv R) (Z : Scheme.{0}) [IsEmpty Z] (a b : Sec G Z) : a = b :=
  ((isSheaf_types G).isSheafFor (⊥ : Presieve Z) (by rw [Sieve.generate_bot]; exact Scheme.bot_mem_grothendieckTopology Z)).isSeparatedFor.ext
    (fun _ _ h => h.elim)

theorem sec_sum (G : Shv R) {X : Scheme.{0}} {r : ℕ} {Y : Fin r → Scheme.{0}} (j : ∀ s, Y s ⟶ X) (hj : IsSum j) :
    Function.Bijective (fun (y : Sec G X) (s : Fin r) => Sec.res (j s) y) := by
  obtain ⟨hopen, hcov, hdisj⟩ := hj
  let U : X.Cover (Scheme.precoverage @Etale) := Scheme.Cover.mkOfCovers (Fin r) Y j
    (fun x => by obtain ⟨s, y, hy⟩ := hcov x; exact ⟨s, y, hy⟩) (fun s => by have := hopen s; infer_instance)
  have hmem : Sieve.ofArrows Y j ∈ Scheme.etaleTopology X := U.mem_grothendieckTopology
  have hsf := (isSheaf_types G).isSheafFor _ hmem
  rw [Presieve.isSheafFor_arrows_iff] at hsf
  have hcomp : ∀ x : ∀ s, Sec G (Y s), Presieve.Arrows.Compatible (G.obj ⋙ forget _) j x := by
    intro x s t Z gs gt h
    by_cases hst : s = t
    · subst hst
      haveI := hopen s
      rw [cancel_mono] at h
      rw [h]
    · haveI : IsEmpty Z := ⟨fun z => by
        have h1 : (j s) (gs z) = (j t) (gt z) := by
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h]
        exact Set.disjoint_left.1 (hdisj s t hst) ⟨gs z, rfl⟩ ⟨gt z, h1.symm⟩⟩
      exact sec_empty G Z _ _
  constructor
  · intro a b hab
    obtain ⟨t, -, ht⟩ := hsf _ (hcomp (fun s => Sec.res (j s) b))
    exact (ht a fun s => congrFun hab s).trans (ht b fun s => rfl).symm
  · intro x
    obtain ⟨t, ht, -⟩ := hsf x (hcomp x)
    exact ⟨t, funext ht⟩

end CrystallineSemistableComparison.WeightedPowerFormIntegrability
