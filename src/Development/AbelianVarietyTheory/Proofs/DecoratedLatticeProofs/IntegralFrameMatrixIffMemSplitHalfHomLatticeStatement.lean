module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFrameMatrixIffMemSplitHalfHomLattice
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integralFrameMatrix_iff_mem_splitHalfHomLattice : ∀ (D : D7) (r : ℕ) (k : Fin r → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)) (pl : Fin r → Formalism.L2.DIV.Pl D.host.E) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), (∀ i, Formalism.L2.NTheta.IsIdemAt (q i).e (pl i)) → (∀ i, (q i).UnitAA) → Function.Injective pl → (∀ PP, PP ∈ Q ↔ ∃ i, pl i = PP) → IsIdemSum e Q → ∀ (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), (∀ i (π' : EAf D →+* k i), (∀ a, π' (toEAf D a) = (q i).pr a) → (∀ y : Fin S.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βS.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV S LS (· = (q i).v)) ∧ ∀ y : Fin T.rank → k i, (∀ a, y a ∈ 𝒪[k i]) ↔ (fun a => (q i).sec ((βT.val.map π' *ᵥ y) a)) ∈ GlobalTheory.FinPl.latV T LT (· = (q i).v)) → ∀ x : WO S T, IsHalf e x → (IsIntM (frMapO S T βS βT x) ↔ x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.HalfInt.isIntM_iff_mem_latO | exact GlobalTheory.HalfInt.isIntM_iff_mem_latO | (intros; apply GlobalTheory.HalfInt.isIntM_iff_mem_latO <;> assumption)
