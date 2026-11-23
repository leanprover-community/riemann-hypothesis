module

public import Formalism.HermitianLattices.StatementLat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdelicFunctionRightTranslateDiamond
import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CrossDiagonalMatching.Common
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

noncomputable section

namespace SameDiaZero

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 Formalism.UG
open NumberField IsDedekindDomain Matrix CrossDiaZero

theorem smul_comm_OE {E : Type} [Field E] [NumberField E] {n : ℕ} (t : E) (m : 𝓞 E) (w : Fin n → E) :
    t • (m • w) = m • (t • w) := by
  exact smul_comm t m w

theorem localization_LshKer_eq_localization_sup {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (P : Ideal R) [P.IsPrime]
    (L : Submodule R W) (y : W) (s : R) (hs : s ∉ P) :
    Formalism.HermitianLatticesTheory.localization₂ P (L ⊔ Submodule.span R {s • y}) = Formalism.HermitianLatticesTheory.localization₂ P (L ⊔ Submodule.span R {y}) := by
  have hS : s ∈ P.primeCompl := hs
  ext x
  change (∃ t ∈ P.primeCompl, t • x ∈ L ⊔ Submodule.span R {s • y}) ↔
    ∃ t ∈ P.primeCompl, t • x ∈ L ⊔ Submodule.span R {y}
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨t, ht, (sup_le_sup_left ?_ L) hx⟩
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self y)
  · rintro ⟨t, ht, hx⟩
    refine ⟨s * t, P.primeCompl.mul_mem hS ht, ?_⟩
    obtain ⟨l, hl, z, hz, he⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [mul_smul, ← he, smul_add, smul_comm s c y]
    exact Submodule.add_mem_sup (L.smul_mem s hl)
      (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

end SameDiaZero

end
