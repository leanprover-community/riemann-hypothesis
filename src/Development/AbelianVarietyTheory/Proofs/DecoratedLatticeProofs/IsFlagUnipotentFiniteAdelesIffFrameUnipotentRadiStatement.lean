module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFlagUnipotentFiniteAdelesIffFrameUnipotentRadi
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

theorem _root_.GlobalTheory.T.isFlagUnipotent_finiteAdeles_iff_frame_unipotentRadical : ∀ (I : Formalism.MainNotions.S.AutInst) {ρ : ℕ} (x : Fin ρ → Fin I.n → I.E) (c : Fin ρ → I.E) (z : Fin I.n → I.E), (∀ a, c a ≠ 0) → (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (x a) z = 0) → ∀ (N : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), GlobalTheory.BesselChar.Unip ((Matrix.of fun k a => c a * x a k).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) ((Formalism.UG.cT (starRingEnd I.E) (Matrix.of fun k a => c a * x a k) * I.J).map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) N ↔ ((∀ a : Fin ρ, (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I (x a) ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) '' {b | b.1 < a.1})) ∧ (N - 1) *ᵥ Formalism.L2.SG.HidaSetting.incl I z ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b)) ∧ ∀ y : Formalism.L2.SG.HidaSetting.VA I, (∀ a, Formalism.L2.SG.HidaSetting.hA I (Formalism.L2.SG.HidaSetting.incl I (x a)) y = 0) → (N - 1) *ᵥ y ∈ Submodule.span (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Set.range fun b => Formalism.L2.SG.HidaSetting.incl I (x b))) := by
  first | exact @GlobalTheory.UnipFin.unip_flag_iff_Nfin | exact GlobalTheory.UnipFin.unip_flag_iff_Nfin | (intros; apply GlobalTheory.UnipFin.unip_flag_iff_Nfin <;> assumption)
