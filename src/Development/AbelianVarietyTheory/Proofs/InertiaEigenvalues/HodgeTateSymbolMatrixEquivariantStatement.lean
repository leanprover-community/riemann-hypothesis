module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordFMemFil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateSymbolMatrixEquivariant
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HTBasis

theorem _root_.GlobalTheory.T.hodgeTateSymbolMatrix_equivariant : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (J : Formalism.MainNotions.LocalSituation.ThetaL P AI) {K LL : FinExt l} {m : ℕ} (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1) (u : Fin m → Fin m → P.R.BdR) (k : Fin m → ℤ), (∀ i j, u i j ∈ (P.PD K).Fil (k i)) → ∀ g : ↥(GK K), (∀ i, ((r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (embF P LL)).mulVec (fun j => P.actQdR (g : GQ l) (u i j)) = u i) → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (colHT J u k).map (Per.σC (g : GQ l)) = colHT J u k * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.colHT_equivariant) | (exact GlobalTheory.HTBasis.colHT_equivariant) | (intros; apply GlobalTheory.HTBasis.colHT_equivariant <;> assumption)
