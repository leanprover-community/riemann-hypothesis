module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MemUQptsStarCIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.UPel.HT
variable {p : ℕ} [Fact p.Prime] (D : Datum p)

def Datum.algO : Subalgebra ℚ (Module.End ℚ D.VQ) := Algebra.adjoin ℚ (Set.range D.actQ)

theorem Datum.actQ_mem_algO (b : D.O) : D.actQ b ∈ D.algO := Algebra.subset_adjoin ⟨b, rfl⟩

theorem Datum.centralizer_algO : Subalgebra.centralizer ℚ (D.algO : Set (Module.End ℚ D.VQ)) = D.endO := by
  apply le_antisymm
  · exact Subalgebra.centralizer_le ℚ _ _ (Algebra.subset_adjoin)
  · intro g hg
    rw [Subalgebra.mem_centralizer_iff]
    intro h hh
    have hle : D.algO ≤ Subalgebra.centralizer ℚ ({g} : Set (Module.End ℚ D.VQ)) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact (D.mem_endO.1 hg b).symm
    exact ((Subalgebra.mem_centralizer_iff ℚ).1 (hle hh) g rfl).symm

instance Datum.nontrivialVQ : Nontrivial D.VQ := by
  apply Module.nontrivial_of_finrank_pos (R := ℚ)
  haveI := D.freeLa; haveI := D.finLa
  rw [Module.finrank_baseChange, D.rankLa]
  exact Nat.mul_pos (Nat.mul_pos D.m_pos D.n_pos) Module.finrank_pos

end GlobalTheory.UPel.HT
