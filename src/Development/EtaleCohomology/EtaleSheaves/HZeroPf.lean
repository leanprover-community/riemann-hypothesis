module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.HZeroPf

open LateralTheory.E.t_E2Cut

def RootAIC : Prop := ∀ (q : ℕ) (X : Scheme.{0}), AICSch X → IsUnit (q : Γ(X, ⊤)) → Nonempty (Prim q Γ(X, ⊤))

def ResBij : Prop := ∀ (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X), ConnectedSpace Y → ConnectedSpace X →
  Nonempty (Prim q Γ(X, ⊤)) → Function.Bijective (Sec.res (F := tw q i) f)

theorem connected_of_AICSch {X : Scheme.{0}} (h : AICSch X) : ConnectedSpace X := by
  have := h.1
  infer_instance

theorem HZero_of (hR : RootAIC) (hB : ResBij) : LateralTheory.E.t_E2Cut.HZero := by
  intro hyp q Y X f hX hY hq i
  obtain ⟨_, e, he, _⟩ := hyp.a9 (ZMod q) (tw q i)
  have := connected_of_AICSch hX
  have hres := hB q i f hY (connected_of_AICSch hX) (hR q X hX hq)
  have key : (pull (ZMod q) (sch.map f) (tw q i) 0) = (e Y).toAddMonoidHom.comp
      ((AddMonoidHom.mk' (Sec.res (F := tw q i) f) (fun a b => map_add _ a b)).comp (e X).symm.toAddMonoidHom) := by
    ext x
    obtain ⟨s, rfl⟩ := (e X).surjective x
    simp [he]
  rw [key]
  exact (e Y).bijective.comp (hres.comp (e X).symm.bijective)

end LateralTheory.E.HZeroPf
