module

public import Development.EtaleCohomology.CohomologicalPurity.LeafChartFactPf
public import Mathlib.Order.CompletePartialOrder
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
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

theorem wincl_mono (d : ℕ) : Mono (Wincl d) := by
  have h : ∀ n, Mono ((Wincl d).app n) := by
    intro n
    have : ∀ U, Mono (((Wincl d).app n).app U) := by
      intro U
      rw [mono_iff_injective]
      intro F G hFG
      change (F : ComposableArrows (WVec d U.unop) _) ⋙ WVec.incl d U.unop = G ⋙ WVec.incl d U.unop at hFG
      exact CategoryTheory.Functor.hext (fun i => Subtype.ext (congrArg (fun K => K.obj i) hFG))
        (fun i j a => Functor.hcongr_hom hFG a)
    exact NatTrans.mono_of_mono_app _
  exact NatTrans.mono_of_mono_app _

theorem wb_mono (d : ℕ) (R : Type) [CommRing R] : Mono (wb d R) := by
  have := wincl_mono d
  unfold wb; infer_instance

def LocCov {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E) : Prop :=
  ∀ (n : SimplexCategoryᵒᵖ) (X : Scheme.{0}) (x : (E.obj n).obj (op X)), ∃ (ι : Type) (O : ι → X.Opens),
    iSup O = ⊤ ∧ ∀ i, (∃ y, (f.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x) ∨
      (∃ y, (g.app n).app (op (O i : Scheme.{0})) y = (E.obj n).map (O i).ι.op x)

def LeafCovLoc : Prop := ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Mono f → Mono g →
  LocCov f g → Cover2 R f g

def LeafWLoc : Prop := ∀ (d : ℕ) (R : Type) [CommRing R], LocCov (wb d R) (pr d R).hom

theorem LeafWCov_of (hG : LeafGeo) (hC : LeafCovLoc) (hW : LeafWLoc) : LeafWCov := by
  intro _ q _ d R _ _
  exact hC (ZMod q) (wb d R) (pr d R).hom (wb_mono d R) (hG.1 d R) (hW d R)

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
