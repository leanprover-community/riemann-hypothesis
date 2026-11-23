module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOf
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanTopFamily
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ExistsGl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace MassDataIdxLatFree

open NumberField

variable {E K : Type} [Field E] [NumberField E] [Field K] (O : ValuationSubring K) (ι : E →+* K)
  {n : Type} [Fintype n] [DecidableEq n]

theorem int_mem (a : 𝓞 E) : ι (a : E) ∈ O := by
  have h1 : IsIntegral ℤ (ι (a : E)) := (RingOfIntegers.isIntegral_coe a).map ι.toIntAlgHom
  have h2 : IsIntegral O (ι (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  rw [← hy]
  exact y.2

def Mι (L : Submodule (𝓞 E) (n → E)) : Submodule O (n → K) :=
  Submodule.span O ((fun l : n → E => fun j => ι (l j)) '' (L : Set (n → E)))

theorem fg (L : Submodule (𝓞 E) (n → E)) (hL : L.FG) : (Mι O ι L).FG := by
  classical
  obtain ⟨S, hS⟩ := hL
  refine ⟨S.image (fun l : n → E => fun j => ι (l j)), ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.2
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hy
    exact Submodule.subset_span ⟨l, hS ▸ Submodule.subset_span hl, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨l, hl, rfl⟩
    rw [← hS] at hl
    induction hl using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (by simpa using ⟨x, hx, rfl⟩)
    | zero =>
        have : (fun j => ι ((0 : n → E) j)) = 0 := by funext j; simp
        beta_reduce; rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
        have : (fun j => ι ((x + y) j)) = (fun j => ι (x j)) + (fun j => ι (y j)) := by
          funext j; simp
        beta_reduce; rw [this]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
        have : (fun j => ι ((a • x) j)) = (⟨ι (a : E), int_mem O ι a⟩ : O) • (fun j => ι (x j)) := by
          funext j
          simp [Algebra.smul_def]
        beta_reduce; rw [this]; exact Submodule.smul_mem _ _ hx

theorem span_top (L : Submodule (𝓞 E) (n → E)) (hL : Submodule.span E (L : Set (n → E)) = ⊤) :
    Submodule.span K (Mι O ι L : Set (n → K)) = ⊤ :=
  by apply _root_.UpperTheory.Reformulated.B.SpanTopFamily.span_top <;> assumption

end MassDataIdxLatFree

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting

theorem latFree_holds {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p) :
    LatFreeP X p θ :=
  MassDataIdxLatFree.exists_gl (OpX X p) (Mlat1 X p θ)
    (MassDataIdxLatFree.fg (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_fg)
    (MassDataIdxLatFree.span_top (OpX X p) (iota1 X p θ) X.B.I.L X.B.I.L_span)

end MassDataIdxSteps
