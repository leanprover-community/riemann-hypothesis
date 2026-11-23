module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEqLatticeUnipotentCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integralUnipotent_eq_latticeUnipotent_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  first | exact @GlobalTheory.CovDomGrp.nO_eq_nLam_coords | exact GlobalTheory.CovDomGrp.nO_eq_nLam_coords | (intros; apply GlobalTheory.CovDomGrp.nO_eq_nLam_coords <;> assumption)
