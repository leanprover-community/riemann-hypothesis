module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentRealPlaceIffFrameUnipotentRadical
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

@[expose] public section

open Matrix NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isFlagUnipotent_realPlace_iff_frame_unipotentRadical : ∀ (I : Formalism.MainNotions.S.AutInst) (v : InfinitePlace I.F) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) ℂ), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (I.φ v)) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (I.φ v)) N ↔ Formalism.L2.SG.HidaSetting.InN (I.ε v) (fun a => Formalism.L2.SG.HidaSetting.rv I v (x a)) (Formalism.L2.SG.HidaSetting.rv I v z) ((I.P v)⁻¹ * N * I.P v) := by
  first | exact @GlobalTheory.RealUnipFrame.unip_iff_inN | exact GlobalTheory.RealUnipFrame.unip_iff_inN | (intros; apply GlobalTheory.RealUnipFrame.unip_iff_inN <;> assumption)
