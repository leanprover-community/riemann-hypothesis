module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionIntegralAdelicReduction
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.parahoricTestFunction_integralAdelic_reduction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : EAf D →+* k), (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (δ : kˣ →* ℂˣ), IsTame δ → ∀ (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), (∀ (z : 𝓞 D.host.E) (x : kˣ) (u : (Formalism.L2.DIV.kP PP)ˣ), (x : k) = (ofSplit q).pr (z : D.host.E) → (u : Formalism.L2.DIV.kP PP) = Ideal.Quotient.mk PP.asIdeal z → δ x = (ξ u)⁻¹) → ∀ (κ l r t j j' a b : ℕ), r = κ + l → ∀ (ea : Ix (Fin κ ⊕ Fin l) (Fin t) j ≃ Fin a) (eb : Ix (Fin κ ⊕ Fin l) (Fin t) j' ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), parPhi δ ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) = if H : LowZero r (N.map (Formalism.L2.DIV.resS D.host.F PP)) ∧ IsUnit (topL r (N.map (Formalism.L2.DIV.resS D.host.F PP))).det then ((ξ H.2.unit : ℂˣ) : ℂ) else 0 := by
  first | exact @GlobalTheory.QTw.LocFn.parPhi_component | exact GlobalTheory.QTw.LocFn.parPhi_component | (intros; apply GlobalTheory.QTw.LocFn.parPhi_component <;> assumption)
