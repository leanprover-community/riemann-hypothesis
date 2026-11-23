module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace JacquetImage

variable {n : ℕ} (G : Grp k n)

theorem leviEmb_mem_PO (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) : leviEmb k G.e m ∈ G.PO :=
  ⟨leviEmb_mem_KO (k := k) G.e hm, leviEmb_mem_parab k G.e m⟩

theorem lam_leviEmb (hL : LeviSubgroupRestriction) (m : Levi k (fun a : Fin G.s => Fin (G.d a)))
    (hm : m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a))) :
    G.lam (leviEmb k G.e m) = G.eta m := by
  have h := hL k n G ⟨leviEmb k G.e m, leviEmb_mem_parab k G.e m⟩ (leviEmb_mem_PO G m hm).1
  rw [leviProj_leviEmb] at h
  exact h

end JacquetImage

theorem step_jacImage {n : ℕ} (G : Grp k n) : JacquetImageProp G := by
  intro hL hJ V _ _ π x hx m hm
  show (Submodule.Quotient.mk (π (leviEmb k G.e m) x) : Jacquet π (unipRad k G.e)) = _
  rw [hx _ (hJ.2 (JacquetImage.leviEmb_mem_PO G m hm)), JacquetImage.lam_leviEmb G hL m hm,
    Submodule.Quotient.mk_smul]

end UpperTheory.TNZ.Grp
