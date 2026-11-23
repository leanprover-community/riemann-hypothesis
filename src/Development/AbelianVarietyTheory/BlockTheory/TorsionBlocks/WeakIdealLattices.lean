module

import Formalism.SharpRestriction.LevelLetterCocycles.LocalTheoremOfUnramifiedLifting
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {l : ℕ} [Fact l.Prime]

def cZero (l : ℕ) (m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt l u)

theorem finiteDimensional_Ks (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  apply Formalism.MainNotions.WachCoordinates.Br.fd_Ks <;> assumption

def KsFin (K : FinExt l) (s : ℕ) : FinExt l := ⟨Ks K s, finiteDimensional_Ks K s⟩

section Ring

variable {P : LocPrime l} (AI : LocAinf l P)

end Ring

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  {R : Type} [CommRing R] [Algebra O R]

end Generic

section Hyp

variable {K LL : FinExt l}

variable {P : LocPrime l} (AI : LocAinf l P)


end Hyp

end GlobalTheory.IndefiniteRowSideFullHecke.LevelConstants
