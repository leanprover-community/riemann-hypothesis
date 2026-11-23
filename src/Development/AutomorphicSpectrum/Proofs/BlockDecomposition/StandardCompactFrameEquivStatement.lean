module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFrameEquivSymm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactFrameEquiv
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

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.RgEis GlobalTheory.CompanionTheory.SiegelFrame

theorem _root_.GlobalTheory.T.standard_compact_frame_equiv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n), Dict → DictInf → IsCMExt F E σ → ∀ (χ : Chr F E) (ε : ℤˣ) (b : GL (Fin n ⊕ Fin n) E) (hb : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (B : Base F E) (K : Subgroup (G2 σ Y)), IsStdK (σ := σ) (Y := Y) B b K → ∀ x : G2 σ Y, x ∈ K ↔ frameEquiv χ ε b hb x ∈ (adCM σ χ).uK ε (Fin n) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | exact GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff | (intros; apply GlobalTheory.CompanionTheory.SiegelFrame.StdCompact.mem_isStdK_iff <;> assumption)
