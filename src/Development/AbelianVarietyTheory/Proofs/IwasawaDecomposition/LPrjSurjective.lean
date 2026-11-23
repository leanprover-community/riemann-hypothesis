module

public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
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

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Mem.LiftProjOnto

theorem lPrj_surjective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (k : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A P ψ k t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W) (op : W →ₗ[ℂ] W), A.fam.Ok 1 → FormsTie D.what₂.embLL j (lH D A P ψ k t) (lE D A P ψ k t) op → Function.Surjective (lPrj D A P ψ Zs k t).mulVec := by
  intro D G _ _ Pl0 T A P ψ Zs k t W _ _ j op hOk _
  have hB : BlockHyp (A.fam.L k t) (A.fam.lvlA P ψ) A.v0 1 := ⟨hOk.conj, hOk.irr, hOk.lifts k t⟩
  exact BlockDat.lf_lPr_surj (Z := Zs.Zl k t) hB

end GlobalTheory.Mem.LiftProjOnto
