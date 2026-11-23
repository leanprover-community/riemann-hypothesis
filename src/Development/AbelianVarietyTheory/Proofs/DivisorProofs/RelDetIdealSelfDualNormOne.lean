module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.SelfDualDetNorm

theorem star_eq_conj (D : D7) (x : D.host.E) :
    (letI := D.host.cmStar; star x) = D.host.conj x := by
  letI := D.host.cmStar
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isSdLat_of_isSDLat {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsSDLat E n L) : Formalism.L2.Col.IsSdLat (E := E) L := by
  obtain ⟨hfg, hsp, hd⟩ := hL
  refine ⟨Submodule.IsLattice.of_fg E hfg, ?_⟩
  ext y
  rw [hd y]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  rfl

theorem detId_normOne : ∀ (D : D7) (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)),
    StandardLatticesGL3.SD D L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  intro D N L hL
  letI := D.host.cmStar
  obtain ⟨J, hJ, hIJ⟩ := GlobalTheory.CharValCompare.normOne_detI (isSdLat_of_isSDLat L hL)
  refine ⟨J, fun x => by rw [hJ, star_eq_conj]; exact Iff.rfl, ?_⟩
  exact hIJ

end GlobalTheory.SelfDualDetNorm
