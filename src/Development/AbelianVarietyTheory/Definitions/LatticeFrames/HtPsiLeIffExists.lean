module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions

variable (D : D7) (u : D.what₂.Word)

abbrev Pt : HLat D.what₂.LL := (D.fm u).ptLat

def IsPsi (Ψ : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V) : Prop :=
  ∀ x : (D.div.Nu u).V, (D.fm u).ptEmb (Ψ x) = PsiC (D.mem u).C (D.mem u).A (D.mem u).P (D.eMu u (D.jN u x))

def PsiRat : Prop := ∃ Ψ, IsPsi D u Ψ


open Classical in
def Psi : (D.div.Nu u).V →ₗ[D.what₂.LL] (Pt D u).V := if h : PsiRat D u then h.choose else 0

theorem isPsi_Psi (h : PsiRat D u) : IsPsi D u (Psi D u) := by
  unfold Psi; rw [dite_eq_left h]; exact h.choose_spec

def htPsi : ℝ := Formalism.HN.htMap (D.div.Nu u).b (D.div.Nu u).X (Pt D u).b (Pt D u).X (Psi D u)

def HtPsiLe (h : ℝ) : Prop := PsiRat D u ∧ (Psi D u ≠ 0 → htPsi D u ≤ h)

def PsiInt (N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Prop :=
  PsiRat D u ∧ ∀ x ∈ N, Psi D u x ∈ (Pt D u).L

variable (Am : AmbForm D (RowSide.sharp D))

def IsPer (e : (Pt D u).V ≃ₗ[D.what₂.LL] (MtDual D Am).V) : Prop :=
  ∀ (x : (Pt D u).V) (z : (Mt D Am).V),
    D.what₂.embLL ((show Module.Dual D.what₂.LL (Mt D Am).V from e x) z) =
      (D.mem u).P.period ((D.fm u).ptEmb x) ((D.eMt u).symm (Am.jAmb D.what₂.mu0 z))

theorem IsPer.isPhi_comp {e} (he : IsPer D u Am e) {Ψ} (h : IsPsi D u Ψ) : IsPhi D Am u (e.toLinearMap ∘ₗ Ψ) := fun x z => by
  refine (he (Ψ x) z).trans ?_
  rw [h x]
  exact (PhiC_apply _ _ _ _ _).trans (D.perCol_base_eq_PtilCol u _ _).symm

def AmbMetric : Prop :=
  ∃ e, IsPer D u Am e ∧ ∀ (v : InfinitePlace D.what₂.LL) (x : (Pt D u).V),
    Formalism.HermitianLatticesTheory.normAt (MtDual D Am).b (MtDual D Am).X v (e x) = Formalism.HermitianLatticesTheory.normAt (Pt D u).b (Pt D u).X v x

def AmbLattice : Prop :=
  ∃ e, IsPer D u Am e ∧ (∀ x, e x ∈ (MtDual D Am).L → x ∈ (Pt D u).L) ∧
    ∀ x ∈ (Pt D u).L, ((D.mem u).C.DGam : D.what₂.LL) • e x ∈ (MtDual D Am).L

end GlobalTheory.Core.Rk

end
