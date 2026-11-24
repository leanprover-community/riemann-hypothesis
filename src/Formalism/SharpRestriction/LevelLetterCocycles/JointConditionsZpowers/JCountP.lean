module

public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCount
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
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
import Formalism.SharpRestriction.LevelLetterCocycles.FamilyStatementsLocal

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.CylinderCountFamily

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.FamilyNumericLemmas

variable (D : D7) {Dall Dgood : ℕ}

def PCountTie (A : AllRowsAt D Dall Dgood) : Prop :=
  ∀ (k : Fin 2) (S : Set (Tup D k)),
    Formalism.MainNotions.S.CountE.PCount A.B.I A.B.μf (D.host.g (1 - k)) (A.eT (cyl D k S))

theorem countCylAt_of (A : AllRowsAt D Dall Dgood) {n₀ : ℕ} {Alev C₃ c₃ cb : ℝ}
    (h1 : Formalism.MainNotions.S.CountE.CountIdempotentsClass Formalism.MainNotions.S.CountE.PCount D n₀ Alev C₃ c₃ cb)
    (hT : TieCountAt A n₀ Alev C₃ cb) (hP : PCountTie D A) : CountCylAt D A c₃ := by
  intro k S
  obtain ⟨b, h, hST, hgap, hC, hlf, hlb, -⟩ := hT
  exact h1 A.B.I b A.B.lam A.B.g (D.host.g (1 - k)) (A.eT (cyl D k S)) _ A.B.σ A.B.w _ A.B.σs A.B.tens
    A.B.μf A.B.fund A.B.R (A.ReT (cyl D k S)) h (hST k S).1 (hP k S) (hST k S).2 hgap hC hlf hlb

end Formalism.MainNotions.N.CylinderCountFamily
