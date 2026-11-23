module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.LocalToGlobal.CharacterGerms.SubstSubst
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def exZero (Y : FBChart C V O dd) : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C :=
  fun q => if q.1 = 0 then un1 (Y.ex q.2) else 0

def ExpODESt (Y : FBChart C V O dd) : Prop :=
  ∀ i j : Fin dd, MvPowerSeries.pderiv (R := C) i (un1 (Y.ex j)) =
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.FK C j))

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_exZero (q : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (exZero Y q) = 0 := by
  unfold exZero
  split_ifs
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex q.2) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Y.ex_const _
  · exact map_zero _

theorem subst_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.subst a (0 : MvPowerSeries σ C) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (Formalism.L2.FormalSeriesBounds.VP.hs ha), map_zero]

theorem constantCoeff_two_points_zero {n : ℕ} (b : Fin n) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simp

end VP

end Formalism.L2.FormalSeriesBounds
