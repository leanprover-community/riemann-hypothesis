module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RefCov

def crd (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r :=
  pTop k r j q.2 * uEmb k r (upperIn β q.1)

abbrev Crd (ι : Type) (k r j : ℕ) (β : Fin r → ℕ) :=
  (UTin β → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) ×
    (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))

def atP {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) (v : ι) : (UTin β → ℂ) × PTop k r j :=
  (fun i => p.1 i v, fun a => p.2.1 a v, fun s => p.2.2.1 s v, fun a => p.2.2.2 a v)

def CC {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) : ι → Mat k r := fun v => crd k r j β (atP p v)

theorem usage₂ {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} :
    Function.Bijective (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun q => (fun i v => (q v).1 i, fun a v => (q v).2.1 a,
    fun s v => (q v).2.2.1 s, fun a v => (q v).2.2.2 a), fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.DegVol.RefCov
