module

public import Formalism.SharpRestriction.GrowthBounds.DataG
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.LocalRingCardinality.Params
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq

@[expose] public section

namespace GlobalTheory.GO

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

namespace CmpMem

theorem isLattice_map {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (A : GL (Fin k) K)
    {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by
  obtain ⟨g, hg, rfl⟩ := hL
  refine ⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).mul hg
  · unfold colSpan
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

theorem isLatTup_smul (C : Level P) (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) :=
  fun v => isLattice_map (C.act v γ) (hL v)

variable {X : Fields} (T : PlTie X P) {n : ℕ} (hn : n = P.m + 1) {lam : X.Tau → DomWeight n} {c : ℤ}

variable {S : GSD X.K} (Y : PSys X n p lam S)

end CmpMem

end GlobalTheory.GO
